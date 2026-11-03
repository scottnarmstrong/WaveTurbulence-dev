/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.CubeToGaussian
public import WaveTurbulence.Foundations.Gaussian.MomentLimit

/-!
# Gaussian hypercontractivity (DH21 Lemma A.3)

Let `η = (η_i)_{i ∈ ι}` be independent normalized complex Gaussians (law `stdComplexGaussian`).
For signs `ζ : Fin n → Bool` (`true` is `+`, `false` is `-`), a finite set `s` of index tuples and
coefficients `a`, consider
`X = multiGauss ζ s a η = ∑_{k ∈ s} a k ∏_{j < n} η_{k j}^{ζ j}`, `z^+ = z`, `z^- = conj z`
(DH21 (A.3), `multigauss`, L2810). Then for every real `q ≥ 2`,
`𝔼|X|^q ≤ (q-1)^{nq/2} (𝔼|X|²)^{q/2}` (DH21 (A.4), `hyper`, L2811).

## Main results

* `WaveTurbulence.integral_norm_rpow_multiGauss_le` (DH21 Lemma A.3, L2808–L2813), together with
  the finiteness of all moments `WaveTurbulence.integrable_norm_rpow_multiGauss`.
* `WaveTurbulence.Gaussian.multiGauss_moment_le_pi`: the same on the canonical product space.

## Proof

DH21 cites Oh–Thomann [OT, Lemma 2.6], i.e. Nelson's hypercontractivity. We prove it through
the Boolean cube: the sharp Bonami–Beckner bound for functions of Walsh degree `≤ n`
(`walshDeg_moment_le`) applies to `X` evaluated at the sign-sum approximation `approxZ ι M` of the
Gaussian vector (each coordinate has Walsh degree one, so `X ∘ approxZ ι M` has degree `≤ n`);
the approximations converge in law (`tendsto_favg_approxZ`, central limit theorem) and have
uniformly bounded moments, so the bound passes to the limit (`moment_le_of_tendsto_favg`).
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace WaveTurbulence

/-- `signConj ζ z` is `z^ζ` in DH21's notation: `z^+ = z` (`ζ = true`), `z^- = conj z`
(`ζ = false`). -/
@[expose] noncomputable def signConj (ζ : Bool) (z : ℂ) : ℂ :=
  if ζ then z else (starRingEnd ℂ) z

theorem norm_signConj (ζ : Bool) (z : ℂ) : ‖signConj ζ z‖ = ‖z‖ := by
  cases ζ <;> simp [signConj]

theorem continuous_signConj (ζ : Bool) : Continuous (signConj ζ) := by
  cases ζ
  · exact Complex.continuous_conj
  · exact continuous_id

/-- The Gaussian polynomial of DH21 (A.3) (`multigauss`, L2810):
`multiGauss ζ s a z = ∑_{k ∈ s} a k ∏_{j < n} (z (k j))^{ζ j}`. -/
@[expose] noncomputable def multiGauss {ι : Type*} {n : ℕ} (ζ : Fin n → Bool)
    (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℂ) (z : ι → ℂ) : ℂ :=
  ∑ k ∈ s, a k * ∏ j, signConj (ζ j) (z (k j))

theorem continuous_multiGauss {ι : Type*} {n : ℕ} (ζ : Fin n → Bool) (s : Finset (Fin n → ι))
    (a : (Fin n → ι) → ℂ) : Continuous (multiGauss ζ s a) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul
    (continuous_finsetProd _ fun _ _ => (continuous_signConj _).comp (continuous_apply _))

namespace Gaussian

/-- Products of `T.card` functions of Walsh degree one have Walsh degree at most `T.card`. -/
theorem prod_mem_walshDeg {K : Type*} [Fintype K] [DecidableEq K] {J : Type*} (T : Finset J)
    (g : J → (K → Bool) → ℂ) (hg : ∀ j ∈ T, g j ∈ walshDeg K 1) :
    (∏ j ∈ T, g j) ∈ walshDeg K T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using one_mem_walshDeg (K := K) 0
  | insert j T hj ih =>
    rw [prod_insert hj, card_insert_of_notMem hj, add_comm]
    exact walshDeg_mul_mem (hg j (mem_insert_self _ _))
      (ih fun j' hj' => hg j' (mem_insert_of_mem hj'))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gaussian polynomial evaluated at the sign-sum approximation has Walsh degree `≤ n`. -/
theorem multiGauss_approxZ_mem_walshDeg {n : ℕ} (ζ : Fin n → Bool) (s : Finset (Fin n → ι))
    (a : (Fin n → ι) → ℂ) (M : ℕ) :
    (fun x => multiGauss ζ s a (approxZ ι M x)) ∈ walshDeg (ι × Bool × Fin M) n := by
  have h : (fun x => multiGauss ζ s a (approxZ ι M x)) =
      ∑ k ∈ s, a k • ∏ j, fun x : ι × Bool × Fin M → Bool => signConj (ζ j) (approxZ ι M x (k j)) := by
    funext x
    simp [multiGauss, Finset.sum_apply, Finset.prod_apply]
  rw [h]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  have := prod_mem_walshDeg (K := ι × Bool × Fin M) univ
    (fun j x => signConj (ζ j) (approxZ ι M x (k j))) fun j _ => by
      cases ζ j
      · exact conj_approxZ_mem_walshDeg M (k j)
      · exact approxZ_mem_walshDeg M (k j)
  simpa using this

omit [DecidableEq ι] in
/-- Polynomial growth of the Gaussian polynomial. -/
theorem norm_multiGauss_le {n : ℕ} (ζ : Fin n → Bool) (s : Finset (Fin n → ι))
    (a : (Fin n → ι) → ℂ) (z : ι → ℂ) :
    ‖multiGauss ζ s a z‖ ≤ (∑ k ∈ s, ‖a k‖) * (1 + ∑ i, ‖z i‖) ^ n := by
  rw [multiGauss, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ∏ j, ‖signConj (ζ j) (z (k j))‖ ≤ ∏ _j : Fin n, (1 + ∑ i, ‖z i‖) := by
        gcongr with j
        rw [norm_signConj]
        have := single_le_sum (f := fun i => ‖z i‖) (fun i _ => norm_nonneg _) (mem_univ (k j))
        linarith
    _ = (1 + ∑ i, ‖z i‖) ^ n := by simp

omit [DecidableEq ι] in
/-- A crude power-mean bound: `(1 + ∑ f)^m ≤ (|ι| + 1)^m (1 + ∑ f^m)`. -/
theorem one_add_sum_pow_le (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (m : ℕ) :
    (1 + ∑ i, f i) ^ m ≤ ((Fintype.card ι : ℝ) + 1) ^ m * (1 + ∑ i, f i ^ m) := by
  set N1 : ℝ := (Fintype.card ι : ℝ) + 1 with hN1
  have hN1pos : 0 < N1 := by positivity
  have hN1one : 1 ≤ N1 := by rw [hN1]; linarith [(Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)]
  let z : Option ι → ℝ := fun o => o.elim 1 f
  have hw : ∑ _o : Option ι, N1⁻¹ = 1 := by
    rw [sum_const, card_univ, Fintype.card_option, nsmul_eq_mul]
    push_cast
    rw [← hN1]
    exact mul_inv_cancel₀ hN1pos.ne'
  have h := Real.pow_arith_mean_le_arith_mean_pow (s := univ) (fun _ => N1⁻¹) z
    (fun _ _ => by positivity) hw (fun o _ => by cases o <;> simp [z, hf]) m
  simp only [← mul_sum, Fintype.sum_option, z, Option.elim, one_pow] at h
  have hY : 0 ≤ 1 + ∑ i, f i ^ m := by
    have := sum_nonneg fun i (_ : i ∈ univ) => pow_nonneg (hf i) m
    linarith
  rw [mul_pow] at h
  calc (1 + ∑ i, f i) ^ m = N1 ^ m * (N1⁻¹ ^ m * (1 + ∑ i, f i) ^ m) := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hN1pos.ne', one_pow, one_mul]
    _ ≤ N1 ^ m * (N1⁻¹ * (1 + ∑ i, f i ^ m)) := by gcongr
    _ ≤ N1 ^ m * (1 + ∑ i, f i ^ m) := by
        gcongr
        calc N1⁻¹ * (1 + ∑ i, f i ^ m) ≤ 1 * (1 + ∑ i, f i ^ m) :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hN1one) hY
          _ = _ := one_mul _

/-- Uniform moment bounds for the coordinates of the approximation. -/
theorem favg_norm_pow_approxZ_le (n M : ℕ) (i : ι) :
    favg (fun x => ‖approxZ ι M x i‖ ^ (2 * n)) ≤ (2 * n + 1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [favg_const]
  have hq : (2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h := walshDeg_moment_le (approxZ_mem_walshDeg (ι := ι) M i) hq
  have h2 := favg_norm_sq_approxZ_le (ι := ι) M i
  simp only [Real.rpow_natCast] at h
  have hexp1 : ((1 : ℕ) : ℝ) * ((2 * n : ℕ) : ℝ) / 2 = (n : ℕ) := by push_cast; ring
  have hexp2 : ((2 * n : ℕ) : ℝ) / 2 = (n : ℕ) := by push_cast; ring
  rw [hexp1, hexp2, Real.rpow_natCast, Real.rpow_natCast] at h
  refine h.trans ?_
  have hF0 : 0 ≤ favg (fun x => ‖approxZ ι M x i‖ ^ 2) := favg_nonneg fun _ => sq_nonneg _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hle : ((2 * n : ℕ) : ℝ) - 1 ≤ 2 * n + 1 := by push_cast; linarith
  calc (((2 * n : ℕ) : ℝ) - 1) ^ n * favg (fun x => ‖approxZ ι M x i‖ ^ 2) ^ n
      ≤ (2 * n + 1) ^ n * 1 ^ n :=
        mul_le_mul (pow_le_pow_left₀ h0 hle n) (pow_le_pow_left₀ hF0 h2 n) (by positivity)
          (by positivity)
    _ = (2 * n + 1) ^ n := by simp

/-- The constant of the uniform second-moment bound. -/
@[expose] noncomputable def secondMomentConst (ι : Type*) [Fintype ι] (n : ℕ) (A : ℝ) : ℝ :=
  A ^ 2 * (((Fintype.card ι : ℝ) + 1) ^ (2 * n) * (1 + Fintype.card ι * (2 * n + 1) ^ n))

/-- Uniform second-moment bound for the approximations of the Gaussian polynomial. -/
theorem favg_norm_sq_multiGauss_approxZ_le {n : ℕ} (ζ : Fin n → Bool) (s : Finset (Fin n → ι))
    (a : (Fin n → ι) → ℂ) (M : ℕ) :
    favg (fun x => ‖multiGauss ζ s a (approxZ ι M x)‖ ^ 2) ≤
      secondMomentConst ι n (∑ k ∈ s, ‖a k‖) := by
  set A := ∑ k ∈ s, ‖a k‖ with hA
  have hA0 : 0 ≤ A := sum_nonneg fun k _ => norm_nonneg _
  set N1 : ℝ := (Fintype.card ι : ℝ) + 1
  have hpt : ∀ x, ‖multiGauss ζ s a (approxZ ι M x)‖ ^ 2 ≤
      A ^ 2 * N1 ^ (2 * n) * (1 + ∑ i, ‖approxZ ι M x i‖ ^ (2 * n)) := by
    intro x
    have h1 := norm_multiGauss_le ζ s a (approxZ ι M x)
    have h2 := one_add_sum_pow_le (fun i => ‖approxZ ι M x i‖) (fun i => norm_nonneg _) (2 * n)
    calc ‖multiGauss ζ s a (approxZ ι M x)‖ ^ 2
        ≤ (A * (1 + ∑ i, ‖approxZ ι M x i‖) ^ n) ^ 2 := by gcongr
      _ = A ^ 2 * (1 + ∑ i, ‖approxZ ι M x i‖) ^ (2 * n) := by ring
      _ ≤ A ^ 2 * (N1 ^ (2 * n) * (1 + ∑ i, ‖approxZ ι M x i‖ ^ (2 * n))) := by gcongr
      _ = _ := by ring
  refine (favg_mono hpt).trans ?_
  rw [favg_mul_left, favg_add, favg_const, favg_sum, secondMomentConst, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_)
    (by positivity)) (by positivity)
  calc ∑ i, favg (fun x => ‖approxZ ι M x i‖ ^ (2 * n)) ≤ ∑ _i : ι, ((2 * n + 1 : ℝ) ^ n) :=
        sum_le_sum fun i _ => favg_norm_pow_approxZ_le n M i
    _ = Fintype.card ι * (2 * n + 1) ^ n := by simp

/-- **Gaussian hypercontractivity on the canonical product space**: for `q ≥ 2`, under the law
`Measure.pi fun _ : ι => stdComplexGaussian` of independent normalized complex Gaussians,
`𝔼|X|^q ≤ (q-1)^{nq/2} (𝔼|X|²)^{q/2}` for `X = multiGauss ζ s a`, and `|X|^q` is integrable. -/
theorem multiGauss_moment_le_pi {n : ℕ} (ζ : Fin n → Bool) (s : Finset (Fin n → ι))
    (a : (Fin n → ι) → ℂ) {q : ℝ} (hq : 2 ≤ q) :
    Integrable (fun z => ‖multiGauss ζ s a z‖ ^ q)
        (Measure.pi fun _ : ι => stdComplexGaussian) ∧
      ∫ z, ‖multiGauss ζ s a z‖ ^ q ∂(Measure.pi fun _ : ι => stdComplexGaussian) ≤
        (q - 1) ^ ((n : ℝ) * q / 2) *
          (∫ z, ‖multiGauss ζ s a z‖ ^ 2 ∂(Measure.pi fun _ : ι => stdComplexGaussian)) ^
            (q / 2) := by
  have hΨc := continuous_multiGauss ζ s a
  set B := secondMomentConst ι n (∑ k ∈ s, ‖a k‖)
  have hB2 := favg_norm_sq_multiGauss_approxZ_le (ι := ι) ζ s a
  have hB0 : 0 ≤ B := (favg_nonneg fun _ => sq_nonneg _).trans (hB2 0)
  refine moment_le_of_tendsto_favg (Ω := fun M => ι × Bool × Fin M → Bool)
    (X := fun M x => multiGauss ζ s a (approxZ ι M x)) hΨc.aestronglyMeasurable
    (fun h hh C hC => tendsto_favg_approxZ (h := fun z => h (multiGauss ζ s a z))
      (hh.comp hΨc) (fun z => hC _)) hB2 (B4 := (4 - 1) ^ ((n : ℝ) * 4 / 2) * B ^ 2) ?_
    (by linarith) (Real.rpow_nonneg (by linarith) _)
    (fun M => walshDeg_moment_le (multiGauss_approxZ_mem_walshDeg ζ s a M) hq)
  intro M
  have h4 := walshDeg_moment_le (multiGauss_approxZ_mem_walshDeg ζ s a M)
    (show (2 : ℝ) ≤ 4 by norm_num)
  have hpow : ∀ x : ι × Bool × Fin M → Bool,
      (‖multiGauss ζ s a (approxZ ι M x)‖ ^ 2) ^ 2 = ‖multiGauss ζ s a (approxZ ι M x)‖ ^ (4 : ℝ) := by
    intro x
    rw [← pow_mul, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hpow]
  refine h4.trans ?_
  have hF0 : 0 ≤ favg (fun x => ‖multiGauss ζ s a (approxZ ι M x)‖ ^ 2) :=
    favg_nonneg fun _ => sq_nonneg _
  rw [show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  gcongr
  exact hB2 M

end Gaussian

open Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} {η : ι → Ω → ℂ}

/-- Reduction of a Gaussian polynomial to the finitely many coordinates it involves. -/
theorem exists_multiGauss_finite_reduction {n : ℕ} (ζ : Fin n → Bool) (s : Finset (Fin n → ι))
    (a : (Fin n → ι) → ℂ) :
    ∃ (T : Finset ι) (s₀ : Finset (Fin n → T)) (a₀ : (Fin n → T) → ℂ),
      ∀ z : ι → ℂ, multiGauss ζ s a z = multiGauss ζ s₀ a₀ (fun i : T => z i) := by
  classical
  set T : Finset ι := s.biUnion fun k => univ.image k with hT
  have hmem : ∀ k ∈ s, ∀ j, k j ∈ T := fun k hk j =>
    mem_biUnion.2 ⟨k, hk, mem_image.2 ⟨j, mem_univ _, rfl⟩⟩
  let r : s → (Fin n → T) := fun k j => ⟨k.1 j, hmem k.1 k.2 j⟩
  have hr : Function.Injective r := by
    intro k k' h
    apply Subtype.ext
    funext j
    have := congrFun h j
    exact congrArg Subtype.val this
  refine ⟨T, s.attach.image r, fun k₀ => a (fun j => (k₀ j).1), fun z => ?_⟩
  rw [multiGauss, multiGauss, sum_image fun k _ k' _ h => hr h, ← sum_attach s]

/-- **DH21 Lemma A.3 (Gaussian hypercontractivity), L2808–L2813.** Let `η` be an independent
family of normalized complex Gaussians, `ζ : Fin n → Bool` signs, and
`X = ∑_{k ∈ s} a k ∏_{j < n} η_{k j}^{ζ j}` (DH21 (A.3)). Then for every real `q ≥ 2`,
`𝔼|X|^q ≤ (q-1)^{nq/2} (𝔼|X|²)^{q/2}` (DH21 (A.4)). -/
theorem integral_norm_rpow_multiGauss_le (hind : iIndepFun η P)
    (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P) {n : ℕ} (ζ : Fin n → Bool)
    (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℂ) {q : ℝ} (hq : 2 ≤ q) :
    ∫ ω, ‖multiGauss ζ s a (fun i => η i ω)‖ ^ q ∂P ≤
      (q - 1) ^ ((n : ℝ) * q / 2) *
        (∫ ω, ‖multiGauss ζ s a (fun i => η i ω)‖ ^ 2 ∂P) ^ (q / 2) := by
  classical
  obtain ⟨T, s₀, a₀, hred⟩ := exists_multiGauss_finite_reduction ζ s a
  simp only [hred]
  have hV : AEMeasurable (fun ω (i : T) => η i ω) P :=
    AEMeasurable.of_eval fun i => (hlaw i).aemeasurable
  have hmap : P.map (fun ω (i : T) => η i ω) = Measure.pi fun _ : T => stdComplexGaussian := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun i : T => (hlaw i).aemeasurable).1
      (hind.precomp Subtype.val_injective)]
    simp only [(hlaw _).map_eq]
  have htr : ∀ p : ℝ, 0 < p → ∫ ω, ‖multiGauss ζ s₀ a₀ (fun i : T => η i ω)‖ ^ p ∂P =
      ∫ z, ‖multiGauss ζ s₀ a₀ z‖ ^ p ∂(Measure.pi fun _ : T => stdComplexGaussian) := by
    intro p hp
    have hm : AEStronglyMeasurable (fun z : T → ℂ => ‖multiGauss ζ s₀ a₀ z‖ ^ p)
        (P.map (fun ω (i : T) => η i ω)) :=
      ((continuous_norm.rpow_const fun _ => Or.inr hp.le).comp
        (continuous_multiGauss ζ s₀ a₀)).aestronglyMeasurable
    rw [← hmap, integral_map hV hm]
  have h2 : ∫ ω, ‖multiGauss ζ s₀ a₀ (fun i : T => η i ω)‖ ^ 2 ∂P =
      ∫ z, ‖multiGauss ζ s₀ a₀ z‖ ^ 2 ∂(Measure.pi fun _ : T => stdComplexGaussian) := by
    have := htr 2 two_pos
    simpa only [Real.rpow_two] using this
  rw [htr q (by linarith), h2]
  exact (multiGauss_moment_le_pi ζ s₀ a₀ hq).2

/-- All moments of a Gaussian polynomial are finite. -/
theorem integrable_norm_rpow_multiGauss (hind : iIndepFun η P)
    (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P) {n : ℕ} (ζ : Fin n → Bool)
    (s : Finset (Fin n → ι)) (a : (Fin n → ι) → ℂ) {q : ℝ} (hq : 2 ≤ q) :
    Integrable (fun ω => ‖multiGauss ζ s a (fun i => η i ω)‖ ^ q) P := by
  classical
  obtain ⟨T, s₀, a₀, hred⟩ := exists_multiGauss_finite_reduction ζ s a
  simp only [hred]
  have hV : AEMeasurable (fun ω (i : T) => η i ω) P :=
    AEMeasurable.of_eval fun i => (hlaw i).aemeasurable
  have hmap : P.map (fun ω (i : T) => η i ω) = Measure.pi fun _ : T => stdComplexGaussian := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun i : T => (hlaw i).aemeasurable).1
      (hind.precomp Subtype.val_injective)]
    simp only [(hlaw _).map_eq]
  have hint := (multiGauss_moment_le_pi ζ s₀ a₀ hq).1
  rw [← hmap] at hint
  exact hint.comp_aemeasurable hV

end WaveTurbulence
