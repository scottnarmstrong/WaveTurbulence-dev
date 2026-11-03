/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.TwoPoint
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Finset.SymmDiff

/-!
# Hypercontractivity on the Boolean cube

On the cube `K → Bool` (uniform measure, `K` finite) we prove the sharp moment bound for functions
of Walsh degree at most `n` (Bonami's inequality with the hypercontractive constant):

* `walshDeg_moment_le`: if `f : (K → Bool) → ℂ` lies in the span `walshDeg K n` of the Walsh
  characters `χ_S` with `|S| ≤ n`, then for every real `q ≥ 2`,
  `𝔼|f|^q ≤ (q-1)^{nq/2} (𝔼|f|²)^{q/2}`.

The proof: the product noise kernel `cubeKer ρ` is `(2,q)`-hypercontractive for
`ρ = (q-1)^{-1/2}` (`cubeKer_isHypercontractive`, by tensorizing the two-point inequality), it
acts on `χ_S` by `ρ^{|S|}`, and `f = T_ρ g` with `𝔼|g|² ≤ ρ^{-2n} 𝔼|f|²` by orthonormality of the
Walsh characters. We also record that `walshDeg` is closed under products
(`walshDeg_mul_mem`), which is how degree bounds for polynomials in the cube variables follow.
-/

public section

open Finset

namespace WaveTurbulence.Gaussian

variable {K : Type*} [Fintype K]

/-- The kernel of the noise operator with correlation `ρ` on the cube `K → Bool`. -/
@[expose] noncomputable def cubeKer (ρ : ℝ) (x y : K → Bool) : ℝ := ∏ i, boolKer ρ (x i) (y i)

theorem cubeKer_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) (x y : K → Bool) : 0 ≤ cubeKer ρ x y :=
  prod_nonneg fun _ _ => boolKer_nonneg hρ _ _

variable [DecidableEq K]

theorem cubeKer_fin_isHypercontractive {q : ℝ} (hq : 2 ≤ q) :
    ∀ N : ℕ, IsHypercontractive q (cubeKer (K := Fin N) (hcRho q))
  | 0 => by
    intro f hf
    have hka : ∀ x, kapply (cubeKer (hcRho q)) f x = f x := by
      intro x
      simp only [kapply, cubeKer, univ_eq_empty, prod_empty, one_mul, Fintype.sum_unique]
      exact congrArg f (Subsingleton.elim _ _)
    have hfa : ∀ g : (Fin 0 → Bool) → ℝ, favg g = g default := by
      intro g
      simp only [favg, Fintype.sum_unique, Fintype.card_unique, Nat.cast_one, inv_one, one_mul]
      exact congrArg g (Subsingleton.elim _ _)
    simp only [hka, hfa]
    have h2 : (f default ^ 2) ^ (q / 2) = f default ^ q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hf _)]
      congr 1
      push_cast
      ring
    rw [h2]
  | N + 1 => by
    have ih := cubeKer_fin_isHypercontractive hq N
    have h2 := (boolKer_isHypercontractive hq).ktensor hq
      (cubeKer_nonneg (abs_hcRho_le_one hq)) ih
    refine h2.of_equiv (Fin.consEquiv (fun _ => Bool)) ?_
    intro x y
    simp [cubeKer, ktensor, Fin.prod_univ_succ, Fin.consEquiv]

/-- **Hypercontractivity of the noise operator on the cube**: for `q ≥ 2` and
`ρ = (q-1)^{-1/2}`, `‖T_ρ f‖_q ≤ ‖f‖_2` for every nonnegative `f` on `K → Bool`. -/
theorem cubeKer_isHypercontractive {q : ℝ} (hq : 2 ≤ q) :
    IsHypercontractive q (cubeKer (K := K) (hcRho q)) := by
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  refine (cubeKer_fin_isHypercontractive hq _).of_equiv
    (e.arrowCongr (Equiv.refl Bool)).symm ?_
  intro x y
  simp only [cubeKer, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_apply, id_eq, Equiv.symm_symm]
  exact Equiv.prod_comp e (fun j => boolKer (hcRho q) (x j) (y j))

/-! ### Walsh characters -/

/-- The Walsh character `χ_S(x) = ∏_{i ∈ S} s(x_i)`. -/
@[expose] noncomputable def walsh (S : Finset K) (x : K → Bool) : ℂ := ∏ i ∈ S, (bsign (x i) : ℂ)

theorem walsh_eq_prod_ite (S : Finset K) (x : K → Bool) :
    walsh S x = ∏ i, if i ∈ S then (bsign (x i) : ℂ) else 1 := by
  rw [walsh, prod_ite_mem univ S, univ_inter]

omit [Fintype K] [DecidableEq K] in
theorem walsh_empty : walsh (∅ : Finset K) = 1 := by
  funext x
  simp [walsh]

omit [Fintype K] [DecidableEq K] in
theorem walsh_singleton (i : K) : walsh {i} = fun x => (bsign (x i) : ℂ) := by
  funext x
  simp [walsh]

theorem walsh_mul (S T : Finset K) (x : K → Bool) :
    walsh S x * walsh T x = walsh (symmDiff S T) x := by
  simp only [walsh_eq_prod_ite, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have hs : (bsign (x i) : ℂ) * bsign (x i) = 1 := by exact_mod_cast bsign_mul_self (x i)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, Finset.mem_symmDiff, hs]

omit [Fintype K] [DecidableEq K] in
theorem conj_walsh (S : Finset K) (x : K → Bool) : (starRingEnd ℂ) (walsh S x) = walsh S x := by
  simp [walsh, map_prod, Complex.conj_ofReal]

theorem sum_walsh (S : Finset K) :
    ∑ x : K → Bool, walsh S x = if S = ∅ then (Fintype.card (K → Bool) : ℂ) else 0 := by
  simp only [walsh_eq_prod_ite]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if i ∈ S then (bsign b : ℂ) else 1)]
  split_ifs with hS
  · subst hS
    simp [Fintype.card_bool]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hS
    refine prod_eq_zero (mem_univ i) ?_
    simp [hi, bsign]

/-- Orthonormality of the Walsh characters. -/
theorem sum_walsh_mul_walsh (S T : Finset K) :
    ∑ x : K → Bool, walsh S x * walsh T x =
      if S = T then (Fintype.card (K → Bool) : ℂ) else 0 := by
  simp only [walsh_mul, sum_walsh, symmDiff_eq_empty]

/-- Parseval's identity for a Walsh expansion. -/
theorem favg_norm_sq_walsh_sum (c : Finset K → ℂ) :
    favg (fun x => ‖∑ S, c S * walsh S x‖ ^ 2) = ∑ S, ‖c S‖ ^ 2 := by
  set N : ℝ := (Fintype.card (K → Bool) : ℝ) with hNdef
  have hN : N ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : ∀ x : K → Bool, ((‖∑ S, c S * walsh S x‖ ^ 2 : ℝ) : ℂ) =
      ∑ S, ∑ T, c S * (starRingEnd ℂ) (c T) * (walsh S x * walsh T x) := by
    intro x
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    refine sum_congr rfl fun S _ => sum_congr rfl fun T _ => ?_
    rw [map_mul, conj_walsh]
    ring
  have hsum : ((∑ x : K → Bool, ‖∑ S, c S * walsh S x‖ ^ 2 : ℝ) : ℂ) =
      (N : ℂ) * ((∑ S, ‖c S‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [key]
    calc ∑ x : K → Bool, ∑ S, ∑ T, c S * (starRingEnd ℂ) (c T) * (walsh S x * walsh T x)
        = ∑ S, ∑ x : K → Bool, ∑ T, c S * (starRingEnd ℂ) (c T) * (walsh S x * walsh T x) :=
          sum_comm
      _ = ∑ S, ∑ T, ∑ x : K → Bool, c S * (starRingEnd ℂ) (c T) * (walsh S x * walsh T x) :=
          sum_congr rfl fun S _ => sum_comm
      _ = ∑ S, ∑ T, c S * (starRingEnd ℂ) (c T) *
            ∑ x : K → Bool, walsh S x * walsh T x := by simp only [mul_sum]
      _ = ∑ S, c S * (starRingEnd ℂ) (c S) * (N : ℂ) := by
          simp only [sum_walsh_mul_walsh, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, hNdef,
            Complex.ofReal_natCast]
      _ = (N : ℂ) * ((∑ S, ‖c S‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum, mul_sum]
          refine sum_congr rfl fun S _ => ?_
          rw [Complex.mul_conj', Complex.ofReal_pow]
          ring
  have hR : (∑ x : K → Bool, ‖∑ S, c S * walsh S x‖ ^ 2 : ℝ) = N * ∑ S, ‖c S‖ ^ 2 := by
    exact_mod_cast hsum
  rw [favg, hR, ← hNdef]
  field_simp

/-! ### The noise operator on complex functions -/

/-- The noise operator with correlation `ρ` on complex functions on the cube. -/
@[expose] noncomputable def cnoise (ρ : ℝ) (f : (K → Bool) → ℂ) (x : K → Bool) : ℂ :=
  ∑ y, (cubeKer ρ x y : ℂ) * f y

theorem cnoise_walsh (ρ : ℝ) (S : Finset K) (x : K → Bool) :
    cnoise ρ (walsh S) x = (ρ : ℂ) ^ S.card * walsh S x := by
  have h1 : ∀ i, ∑ b : Bool, ((boolKer ρ (x i) b : ℝ) : ℂ) * (if i ∈ S then (bsign b : ℂ) else 1)
      = if i ∈ S then (ρ : ℂ) * bsign (x i) else 1 := by
    intro i
    split_ifs with hi
    · cases x i <;> simp [boolKer, bsign] <;> ring
    · cases x i <;> simp [boolKer, bsign] <;> ring
  calc cnoise ρ (walsh S) x
      = ∑ y : K → Bool, ∏ i, ((boolKer ρ (x i) (y i) : ℝ) : ℂ) *
          (if i ∈ S then (bsign (y i) : ℂ) else 1) := by
        simp only [cnoise, cubeKer, walsh_eq_prod_ite, Complex.ofReal_prod, prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, ((boolKer ρ (x i) b : ℝ) : ℂ) *
          (if i ∈ S then (bsign b : ℂ) else 1) :=
        (Fintype.prod_sum (fun i (b : Bool) => ((boolKer ρ (x i) b : ℝ) : ℂ) *
          (if i ∈ S then (bsign b : ℂ) else 1))).symm
    _ = ∏ i, if i ∈ S then (ρ : ℂ) * bsign (x i) else 1 := by simp only [h1]
    _ = (∏ i, if i ∈ S then (ρ : ℂ) else 1) * ∏ i, (if i ∈ S then (bsign (x i) : ℂ) else 1) := by
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun i _ => ?_
        split_ifs <;> simp
    _ = (ρ : ℂ) ^ S.card * walsh S x := by
        rw [prod_ite_mem univ S, univ_inter, prod_const, walsh_eq_prod_ite]

theorem cnoise_sum (ρ : ℝ) (c : Finset K → ℂ) (x : K → Bool) :
    cnoise ρ (fun y => ∑ S, c S * walsh S y) x = ∑ S, c S * ((ρ : ℂ) ^ S.card * walsh S x) := by
  simp only [← cnoise_walsh]
  simp only [cnoise, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun S _ => sum_congr rfl fun y _ => by ring

theorem norm_cnoise_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (f : (K → Bool) → ℂ) (x : K → Bool) :
    ‖cnoise ρ f x‖ ≤ kapply (cubeKer ρ) (fun y => ‖f y‖) x := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine sum_congr rfl fun y _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cubeKer_nonneg hρ x y)]

/-! ### Functions of bounded Walsh degree -/

variable (K) in
/-- The functions on the cube of Walsh degree at most `n`: the span of the Walsh characters
`χ_S` with `|S| ≤ n`. -/
@[expose] def walshDeg (n : ℕ) : Submodule ℂ ((K → Bool) → ℂ) :=
  Submodule.span ℂ (walsh '' {S : Finset K | S.card ≤ n})

omit [Fintype K] [DecidableEq K] in
theorem walsh_mem_walshDeg {S : Finset K} {n : ℕ} (h : S.card ≤ n) : walsh S ∈ walshDeg K n :=
  Submodule.subset_span ⟨S, h, rfl⟩

omit [Fintype K] [DecidableEq K] in
theorem walshDeg_mono {m n : ℕ} (h : m ≤ n) : walshDeg K m ≤ walshDeg K n :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans hS h)

omit [Fintype K] [DecidableEq K] in
theorem one_mem_walshDeg (n : ℕ) : (1 : (K → Bool) → ℂ) ∈ walshDeg K n := by
  rw [← walsh_empty]
  exact walsh_mem_walshDeg (by simp)

omit [Fintype K] [DecidableEq K] in
theorem bsign_mem_walshDeg (i : K) : (fun x : K → Bool => (bsign (x i) : ℂ)) ∈ walshDeg K 1 := by
  rw [← walsh_singleton]
  exact walsh_mem_walshDeg (by simp)

/-- `walshDeg` is closed under products, with additive degrees. -/
theorem walshDeg_mul_mem {a b : ℕ} {f g : (K → Bool) → ℂ} (hf : f ∈ walshDeg K a)
    (hg : g ∈ walshDeg K b) : f * g ∈ walshDeg K (a + b) := by
  have h := Submodule.mul_mem_mul hf hg
  rw [walshDeg, walshDeg, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨S, hS, rfl⟩, _, ⟨T, hT, rfl⟩, rfl⟩
  refine ⟨symmDiff S T, ?_, ?_⟩
  · exact (card_le_card symmDiff_subset_union).trans ((card_union_le S T).trans
      (add_le_add hS hT))
  · funext x
    exact (walsh_mul S T x).symm

/-- Elements of `walshDeg K n` are Walsh expansions with coefficients vanishing above degree
`n`. -/
theorem exists_walsh_expansion {n : ℕ} {f : (K → Bool) → ℂ} (hf : f ∈ walshDeg K n) :
    ∃ c : Finset K → ℂ, (∀ S, n < S.card → c S = 0) ∧ f = fun x => ∑ S, c S * walsh S x := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, hS, rfl⟩ := hg
    refine ⟨fun T => if T = S then 1 else 0, fun T hT => ?_, ?_⟩
    · have : T ≠ S := by rintro rfl; exact absurd hS (by simp at hT ⊢; omega)
      simp [this]
    · funext x
      simp
  | zero => exact ⟨0, fun _ _ => rfl, by funext x; simp⟩
  | add g h _ _ ihg ihh =>
    obtain ⟨c, hc, rfl⟩ := ihg
    obtain ⟨d, hd, rfl⟩ := ihh
    refine ⟨c + d, fun S hS => by simp [hc S hS, hd S hS], ?_⟩
    funext x
    simp [add_mul, sum_add_distrib]
  | smul a g _ ih =>
    obtain ⟨c, hc, rfl⟩ := ih
    refine ⟨a • c, fun S hS => by simp [hc S hS], ?_⟩
    funext x
    simp [mul_sum, mul_assoc]

/-- **Hypercontractive moment bound on the Boolean cube**: for `f` of Walsh degree at most `n`
and real `q ≥ 2`, `𝔼|f|^q ≤ (q-1)^{nq/2} (𝔼|f|²)^{q/2}`. -/
theorem walshDeg_moment_le {n : ℕ} {f : (K → Bool) → ℂ} (hf : f ∈ walshDeg K n) {q : ℝ}
    (hq : 2 ≤ q) :
    favg (fun x => ‖f x‖ ^ q) ≤
      (q - 1) ^ ((n : ℝ) * q / 2) * favg (fun x => ‖f x‖ ^ 2) ^ (q / 2) := by
  obtain ⟨c, hc, rfl⟩ := exists_walsh_expansion hf
  have hq1 : 1 < q := by linarith
  set ρ := hcRho q with hρdef
  have hρ0 : 0 < ρ := hcRho_pos hq1
  have hρ1 : |ρ| ≤ 1 := abs_hcRho_le_one hq
  have hρsq : (ρ ^ 2)⁻¹ = q - 1 := by rw [hρdef, hcRho_sq hq1, inv_inv]
  set g : (K → Bool) → ℂ := fun y => ∑ S, (c S * ((ρ : ℂ)⁻¹) ^ S.card) * walsh S y with hgdef
  have hTg : ∀ x, cnoise ρ g x = ∑ S, c S * walsh S x := by
    intro x
    rw [hgdef, cnoise_sum]
    refine sum_congr rfl fun S _ => ?_
    have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ0.ne'
    rw [show c S * (ρ : ℂ)⁻¹ ^ S.card * ((ρ : ℂ) ^ S.card * walsh S x) =
      c S * ((ρ : ℂ)⁻¹ * ρ) ^ S.card * walsh S x by ring, inv_mul_cancel₀ hρc, one_pow, mul_one]
  -- pointwise domination by the positive noise operator
  have hpt : ∀ x, ‖∑ S, c S * walsh S x‖ ^ q ≤
      kapply (cubeKer ρ) (fun y => ‖g y‖) x ^ q := by
    intro x
    rw [← hTg]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_cnoise_le hρ1 g x) (by linarith)
  have hHC := cubeKer_isHypercontractive (K := K) hq (fun y => ‖g y‖) (fun _ => norm_nonneg _)
  -- the `L²` norm of `g`
  have hg2 : favg (fun x => ‖g x‖ ^ 2) ≤
      (q - 1) ^ n * favg (fun x => ‖∑ S, c S * walsh S x‖ ^ 2) := by
    rw [hgdef, favg_norm_sq_walsh_sum, favg_norm_sq_walsh_sum, mul_sum]
    refine sum_le_sum fun S _ => ?_
    by_cases hS : n < S.card
    · simp [hc S hS]
    · replace hS := not_lt.1 hS
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ0.le, mul_pow,
        ← pow_mul, mul_comm S.card 2, pow_mul, inv_pow, hρsq, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hS) (sq_nonneg _)
  have hF0 : 0 ≤ favg (fun x => ‖∑ S, c S * walsh S x‖ ^ 2) := favg_nonneg fun _ => sq_nonneg _
  calc favg (fun x => ‖∑ S, c S * walsh S x‖ ^ q)
      ≤ favg (fun x => kapply (cubeKer ρ) (fun y => ‖g y‖) x ^ q) := favg_mono hpt
    _ ≤ favg (fun x => ‖g x‖ ^ 2) ^ (q / 2) := hHC
    _ ≤ ((q - 1) ^ n * favg (fun x => ‖∑ S, c S * walsh S x‖ ^ 2)) ^ (q / 2) :=
        Real.rpow_le_rpow (favg_nonneg fun _ => sq_nonneg _) hg2 (by linarith)
    _ = (q - 1) ^ ((n : ℝ) * q / 2) * favg (fun x => ‖∑ S, c S * walsh S x‖ ^ 2) ^ (q / 2) := by
        rw [Real.mul_rpow (pow_nonneg (by linarith) _) hF0, ← Real.rpow_natCast,
          ← Real.rpow_mul (by linarith), mul_div_assoc]

end WaveTurbulence.Gaussian
