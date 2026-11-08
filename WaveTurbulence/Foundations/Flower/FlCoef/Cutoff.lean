/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.ClassDef
public import WaveTurbulence.Foundations.ClassJR.Coupling
public import WaveTurbulence.Foundations.Fourier.Chi0Gevrey

/-!
# FL-COEF: Gevrey-2 bounds for products of coordinate cutoffs

Supplement Lemma 8.1, step one. A product `∏ᵢ fᵢ(α_{c i})` of scalar functions of single
coordinates, each with `‖f⁽ᵏ⁾‖ ≤ N Aᵏ (2k)!`, has `ℓ¹`-derivatives bounded by
`gev ((4N)^n) A k` (`n` the number of factors), with the same radius `A`. For the cutoffs
`χ₀(α_j / S)`, `S ≥ 1`, the constants are independent of `S`.
-/

@[expose] public section

set_option autoImplicit false

namespace WaveTurbulence.Flower.FlCoef

open WaveTurbulence.ClassJR WaveTurbulence.Fourier Finset
open scoped ContDiff ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A function of one coordinate, as a function on `ℓ¹(ι)`. -/
theorem coord_eq (j : ι) (f : ℝ → ℂ) :
    (fun β : L1 ι => f (β j)) = fun β => f (bundleL (Pi.single j 1) β + 0) := by
  funext β
  simp [bundle, Pi.single_apply]

theorem enorm_iteratedFDeriv_coord_le {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (j : ι) (k : ℕ)
    (x : L1 ι) :
    ‖iteratedFDeriv ℝ k (fun β : L1 ι => f (β j)) x‖ₑ ≤
      ‖iteratedDeriv k f (x j)‖ₑ := by
  have hb : IsBundle (Pi.single j (1 : ℤ)) := fun i => by
    by_cases h : i = j <;> simp [Pi.single_apply, h]
  have := enorm_iteratedFDeriv_scalar_le hf (bundleL (Pi.single j 1)) (norm_bundleL_le hb) 0 x k
  rw [coord_eq] 
  convert this using 2
  simp [bundle, Pi.single_apply]

theorem contDiff_coord {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (j : ι) :
    ContDiff ℝ ∞ (fun β : L1 ι => f (β j)) := by
  have hb : IsBundle (Pi.single j (1 : ℤ)) := fun i => by
    by_cases h : i = j <;> simp [Pi.single_apply, h]
  rw [coord_eq]
  exact hf.comp ((bundleL (Pi.single j 1)).contDiff.add contDiff_const)

variable {κ : Type*}

/-- **Gevrey-2 product bound.** A finite product of single-coordinate factors, each bounded by
`gev N A k`, is bounded by `gev ((4N)^n) A k`. -/
theorem enorm_iteratedFDeriv_prod_le (c : κ → ι) (f : κ → ℝ → ℂ) {N A : ℝ} (hN : 0 ≤ N)
    (hA : 0 ≤ A) (hs : ∀ i, ContDiff ℝ ∞ (f i))
    (hf : ∀ i k x, ‖iteratedDeriv k (f i) x‖ₑ ≤ gev N A k) [DecidableEq κ]
    (s : Finset κ) (k : ℕ) (x : L1 ι) :
    ‖iteratedFDeriv ℝ k (fun β : L1 ι => ∏ i ∈ s, f i (β (c i))) x‖ₑ ≤
      gev ((4 * N) ^ s.card) A k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero =>
      rw [← ofReal_norm, norm_iteratedFDeriv_zero]
      simp [gev]
    | succ k =>
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero]
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
      simp
  | insert a s ha ih =>
    have hprod : ∀ s : Finset κ, ContDiff ℝ ∞ (fun β : L1 ι => ∏ i ∈ s, f i (β (c i))) :=
      fun s => by
        refine contDiff_prod fun i _ => ?_
        exact contDiff_coord (hs i) (c i)
    have heq : (fun β : L1 ι => ∏ i ∈ insert a s, f i (β (c i))) =
        fun β => f a (β (c a)) * ∏ i ∈ s, f i (β (c i)) := by
      funext β; rw [Finset.prod_insert ha]
    rw [heq]
    refine (enorm_iteratedFDeriv_mul_le (contDiff_coord (hs a) (c a)) (hprod s) x k).trans ?_
    rw [Finset.card_insert_of_notMem ha]
    have h := gev_conv_le (S₁ := fun j => ‖iteratedFDeriv ℝ j (fun β : L1 ι => f a (β (c a))) x‖ₑ)
      (S₂ := fun j => ‖iteratedFDeriv ℝ j (fun β : L1 ι => ∏ i ∈ s, f i (β (c i))) x‖ₑ)
      hN (pow_nonneg (by positivity) _) hA
      (fun j => (enorm_iteratedFDeriv_coord_le (hs a) (c a) j x).trans (hf a j _))
      (fun j => ih j) k
    refine h.trans_eq ?_
    rw [pow_succ]; ring_nf

/-- The scaled cutoff `x ↦ χ₀(x/S)` as a complex function. -/
noncomputable def chi0C (S : ℝ) (x : ℝ) : ℂ := ((chi0 (x / S) : ℝ) : ℂ)

/-- The Gevrey-2 radius of `χ₀`. -/
noncomputable def chiA : ℝ := 16 + 16 * Real.exp 2

theorem chiA_nonneg : 0 ≤ chiA := by unfold chiA; positivity

theorem contDiff_chi0C (S : ℝ) : ContDiff ℝ ∞ (chi0C S) := by
  unfold chi0C
  exact Complex.ofRealCLM.contDiff.comp (chi0_contDiff.comp (contDiff_id.div_const S))

/-- **The scaled cutoff has `S`-independent Gevrey-2 bounds** for `S ≥ 1`:
`‖∂ᵏ χ₀(·/S)‖ ≤ e⁴ A₀ᵏ (2k)!`. -/
theorem enorm_iteratedDeriv_chi0C_le {S : ℝ} (hS : 1 ≤ S) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (chi0C S) x‖ₑ ≤ gev (Real.exp 4) chiA k := by
  have hS0 : 0 < S := lt_of_lt_of_le one_pos hS
  have h := (chi0_gevreyTwoBound.comp_affine chi0_contDiff (1 / S) 0)
  have hm := h.mono (by positivity) (by positivity) le_rfl
    (show |1 / S| * (16 + 16 * Real.exp 2) ≤ chiA by
      unfold chiA
      rw [abs_of_pos (by positivity), one_div]
      exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hS))
  have := hm k x
  rw [← ofReal_norm, gev]
  have hd : chi0C S = fun y : ℝ => ((chi0 (y / S) : ℝ) : ℂ) := rfl
  rw [hd]
  have hc : (fun y : ℝ => ((chi0 (y / S) : ℝ) : ℂ)) =
      fun y => (((fun x => chi0 (1 / S * x + 0)) y : ℝ) : ℂ) := by
    funext y; simp [div_eq_inv_mul]
  rw [hc, norm_iteratedDeriv_ofReal (by
    exact chi0_contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const))]
  exact ENNReal.ofReal_le_ofReal (by simpa using this)

/-- The product of scaled cutoffs, `∏ᵢ χ₀(α_{c i}/S_i)`, as a complex function on `ι → ℝ`. -/
noncomputable def cutProd (c : κ → ι) (S : κ → ℝ) [Fintype κ] (α : ι → ℝ) : ℂ :=
  ∏ i, chi0C (S i) (α (c i))

/-- **FL-COEF, product bound.** For `S i ≥ 1`, the `ℓ¹`-derivatives of `cutProd` satisfy
`‖D^k‖ ≤ gev ((4 e⁴)^n) A₀ k`, with `n = |κ|`, independent of the scales. -/
theorem enorm_iteratedFDeriv_cutProd_le [Fintype κ] [DecidableEq κ] (c : κ → ι) (S : κ → ℝ)
    (hS : ∀ i, 1 ≤ S i) (k : ℕ) (α : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (fun β : L1 ι => cutProd c S (WithLp.ofLp β))
      (WithLp.toLp 1 α)‖ₑ ≤ gev ((4 * Real.exp 4) ^ Fintype.card κ) chiA k := by
  have := enorm_iteratedFDeriv_prod_le c (fun i => chi0C (S i)) (N := Real.exp 4)
    (A := chiA) (Real.exp_pos 4).le chiA_nonneg (fun i => contDiff_chi0C (S i))
    (fun i k x => enorm_iteratedDeriv_chi0C_le (hS i) k x) Finset.univ k (WithLp.toLp 1 α)
  simpa [cutProd] using this

omit [DecidableEq ι] in
theorem contDiff_cutProd [Fintype κ] (c : κ → ι) (S : κ → ℝ) :
    ContDiff ℝ ∞ (cutProd c S) := by
  unfold cutProd
  refine contDiff_prod fun i _ => ?_
  exact (contDiff_chi0C (S i)).comp (contDiff_pi.1 contDiff_id (c i))

omit [DecidableEq ι] in
theorem norm_cutProd_le_one [Fintype κ] (c : κ → ι) (S : κ → ℝ) (α : ι → ℝ) :
    ‖cutProd c S α‖ₑ ≤ 1 := by
  unfold cutProd
  rw [← ofReal_norm, norm_prod]
  have : ∏ i, ‖chi0C (S i) (α (c i))‖ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    unfold chi0C
    rw [Complex.norm_real, Real.norm_of_nonneg (chi0_nonneg _)]
    exact chi0_le_one _
  simpa using ENNReal.ofReal_le_ofReal this

end WaveTurbulence.Flower.FlCoef
