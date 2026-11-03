/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Partition
public import WaveTurbulence.Foundations.ApproxNT.PoissonPair

/-!
# One momentum pair localized to a unit cell (packet NT6)

After the unit-cube localization, every pair `(x_j, y_j)` of DH23 Prop 6.4 carries the
amplitude `θ(x-p) θ(y-q) e(ξ·x + η·y)`. This file defines, for one such pair,

* `cellInt p q ξ η s = ∫∫ θ(x-p) θ(y-q) e(ξ·x + η·y + s⟨x,y⟩) dx dy` (as an `NTSP.ntIntegral`
  at scale `2`, since `χ₀((x-p)/2) = 1` on the support of `θ(x-p)`);
* `cellSum L p q ξ η s = ∑_{(x,y) ∈ (L⁻¹ℤ^d)²} θ(x-p) θ(y-q) e(ξ·x + η·y + s⟨x,y⟩)`;

and proves Poisson summation `cellSum = L^{2d} ∑_{(g,h)} cellInt(Lg + ξ, Lh + η)`.
-/

public section

noncomputable section

open MeasureTheory Metric WithLp Finset
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-- The cutoff `θ` with complex values. -/
@[expose] def thetaC (x : Mom d) : ℂ := (thetaMom d x : ℂ)

/-- The amplitude `θ(x-p) θ(y-q)` of one cell. -/
@[expose] def cellAmp (p q x y : Mom d) : ℂ := thetaC (x - p) * thetaC (y - q)

theorem norm_thetaC_le_one (x : Mom d) : ‖thetaC x‖ ≤ 1 := by
  rw [thetaC, Complex.norm_real, Real.norm_of_nonneg (thetaMom_nonneg x)]
  exact thetaMom_le_one x

theorem norm_cellAmp_le_one (p q x y : Mom d) : ‖cellAmp p q x y‖ ≤ 1 := by
  rw [cellAmp, norm_mul]
  calc ‖thetaC (x - p)‖ * ‖thetaC (y - q)‖ ≤ 1 * 1 :=
        mul_le_mul (norm_thetaC_le_one _) (norm_thetaC_le_one _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem contDiff_thetaC : ContDiff ℝ ∞ (thetaC (d := d)) :=
  Complex.ofRealCLM.contDiff.comp contDiff_thetaMom

theorem continuous_thetaC : Continuous (thetaC (d := d)) := contDiff_thetaC.continuous

theorem norm_iteratedFDeriv_thetaC_sub_le (k : ℕ) (p x : Mom d) :
    ‖iteratedFDeriv ℝ k (fun x => thetaC (x - p)) x‖ ≤ thetaDerivConst d k := by
  rw [iteratedFDeriv_comp_sub]
  have h : (thetaC (d := d)) = Complex.ofRealCLM ∘ thetaMom d := rfl
  rw [h, Complex.ofRealCLM.iteratedFDeriv_comp_left (contDiff_thetaMom (d := d)).contDiffAt
    (by exact_mod_cast le_top)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  calc ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ k (thetaMom d) (x - p)‖
      ≤ 1 * thetaDerivConst d k := by
        refine mul_le_mul ?_ (norm_iteratedFDeriv_thetaMom_le k _) (norm_nonneg _) zero_le_one
        exact Complex.ofRealCLM_norm.le
    _ = thetaDerivConst d k := one_mul _

/-- One constant controlling `θ`'s derivatives through order `N`. -/
@[expose] def cellConst (d N : ℕ) : ℝ := ∑ k ∈ range (N + 1), thetaDerivConst d k

theorem cellConst_nonneg (d N : ℕ) : 0 ≤ cellConst d N :=
  sum_nonneg fun k _ => thetaDerivConst_nonneg d k

theorem thetaDerivConst_le_cellConst {k N : ℕ} (hk : k ≤ N) :
    thetaDerivConst d k ≤ cellConst d N :=
  single_le_sum (fun j _ => thetaDerivConst_nonneg d j) (mem_range.2 (by omega))

/-- The cell amplitude, times a scalar of modulus at most one, satisfies (NTphibounds). -/
theorem ntBounds_cellAmp (N : ℕ) {c : ℂ} (hc : ‖c‖ ≤ 1) (p q : Mom d) :
    NTSP.NTBounds N (cellConst d N) (fun x y => c * cellAmp p q x y) where
  contDiff_left y := by
    have h : ContDiff ℝ ∞ (fun x => thetaC (x - p)) :=
      (contDiff_thetaC (d := d)).comp (contDiff_id.sub contDiff_const)
    show ContDiff ℝ N (fun x => c * (thetaC (x - p) * thetaC (y - q)))
    exact (contDiff_const.mul (h.mul contDiff_const)).of_le (by exact_mod_cast le_top)
  contDiff_right x := by
    have h : ContDiff ℝ ∞ (fun y => thetaC (y - q)) :=
      (contDiff_thetaC (d := d)).comp (contDiff_id.sub contDiff_const)
    show ContDiff ℝ N (fun y => c * (thetaC (x - p) * thetaC (y - q)))
    exact (contDiff_const.mul (contDiff_const.mul h)).of_le (by exact_mod_cast le_top)
  bound_left k hk x y := by
    have hf : ContDiff ℝ ∞ (fun x => thetaC (x - p)) :=
      (contDiff_thetaC (d := d)).comp (contDiff_id.sub contDiff_const)
    have he : (fun x => c * cellAmp p q x y) = (c * thetaC (y - q)) • (fun x => thetaC (x - p)) := by
      funext x; simp only [cellAmp, Pi.smul_apply, smul_eq_mul]; ring
    rw [he, iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, norm_mul]
    calc ‖c‖ * ‖thetaC (y - q)‖ * ‖iteratedFDeriv ℝ k (fun x => thetaC (x - p)) x‖
        ≤ 1 * 1 * thetaDerivConst d k := by
          refine mul_le_mul (mul_le_mul hc (norm_thetaC_le_one _) (norm_nonneg _) zero_le_one)
            (norm_iteratedFDeriv_thetaC_sub_le k p x) (norm_nonneg _) (by norm_num)
      _ ≤ cellConst d N := by rw [one_mul, one_mul]; exact thetaDerivConst_le_cellConst hk
  bound_right k hk x y := by
    have hf : ContDiff ℝ ∞ (fun y => thetaC (y - q)) :=
      (contDiff_thetaC (d := d)).comp (contDiff_id.sub contDiff_const)
    have he : (fun y => c * cellAmp p q x y) = (c * thetaC (x - p)) • (fun y => thetaC (y - q)) := by
      funext y; simp only [cellAmp, Pi.smul_apply, smul_eq_mul]; ring
    rw [he, iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, norm_mul]
    calc ‖c‖ * ‖thetaC (x - p)‖ * ‖iteratedFDeriv ℝ k (fun y => thetaC (y - q)) y‖
        ≤ 1 * 1 * thetaDerivConst d k := by
          refine mul_le_mul (mul_le_mul hc (norm_thetaC_le_one _) (norm_nonneg _) zero_le_one)
            (norm_iteratedFDeriv_thetaC_sub_le k q y) (norm_nonneg _) (by norm_num)
      _ ≤ cellConst d N := by rw [one_mul, one_mul]; exact thetaDerivConst_le_cellConst hk

/-- On the support of `θ(x-p)`, the scale-two cutoff `χ₀((x-p)/2)` equals one. -/
theorem chiScaled_two_mul_thetaC (p x : Mom d) :
    NTSP.chiScaled 2 (x - p) * thetaC (x - p) = thetaC (x - p) := by
  by_cases h : thetaMom d (x - p) = 0
  · simp [thetaC, h]
  · have h1 : NTSP.chiScaled 2 (x - p) = 1 := by
      rw [NTSP.chiScaled_apply]
      simp only [Fourier.chi0Tensor]
      rw [Finset.prod_eq_one, Complex.ofReal_one]
      intro i _
      apply Fourier.chi0_eq_one
      have hi := abs_lt_one_of_thetaMom_ne_zero h i
      have he : (WithLp.ofLp ((2 : ℝ)⁻¹ • (x - p))) i = 2⁻¹ * (x - p) i := by simp
      rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
      linarith
    rw [h1, one_mul]

theorem chiScaled_mul_cellAmp (p q x y : Mom d) (c : ℂ) :
    NTSP.chiScaled 2 (x - p) * NTSP.chiScaled 2 (y - q) * (c * cellAmp p q x y) =
      c * cellAmp p q x y := by
  have h1 := chiScaled_two_mul_thetaC p x
  have h2 := chiScaled_two_mul_thetaC q y
  simp only [cellAmp]
  calc NTSP.chiScaled 2 (x - p) * NTSP.chiScaled 2 (y - q) * (c * (thetaC (x - p) * thetaC (y - q)))
      = c * ((NTSP.chiScaled 2 (x - p) * thetaC (x - p)) *
          (NTSP.chiScaled 2 (y - q) * thetaC (y - q))) := by ring
    _ = _ := by rw [h1, h2]

/-- The one-cell oscillatory integral. -/
@[expose] def cellInt (p q ξ η : Mom d) (s : ℝ) : ℂ := NTSP.ntIntegral 2 (cellAmp p q) p q ξ η s

theorem cellInt_eq (p q ξ η : Mom d) (s : ℝ) :
    cellInt p q ξ η s = ∫ y, ∫ x, Real.fourierChar (inner ℝ x ξ + inner ℝ y η + s * inner ℝ x y) •
      cellAmp p q x y := by
  rw [cellInt, NTSP.ntIntegral]
  congr 1; funext y; congr 1; funext x
  congr 1
  simpa using chiScaled_mul_cellAmp p q x y 1

theorem ntIntegral_const_mul_cellAmp (c : ℂ) (p q ξ η : Mom d) (s : ℝ) :
    NTSP.ntIntegral 2 (fun x y => c * cellAmp p q x y) p q ξ η s = c * cellInt p q ξ η s := by
  rw [cellInt_eq, NTSP.ntIntegral, ← integral_const_mul]
  congr 1; funext y
  rw [← integral_const_mul]
  congr 1; funext x
  rw [chiScaled_mul_cellAmp, mul_smul_comm]

/-- The one-cell lattice sum over `(L⁻¹ℤ^d)²`. -/
@[expose] def cellSum (L : ℝ) (p q ξ η : Mom d) (s : ℝ) : ℂ :=
  ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
    Real.fourierChar (inner ℝ (latticePoint L gh.1) ξ + inner ℝ (latticePoint L gh.2) η +
      s * inner ℝ (latticePoint L gh.1) (latticePoint L gh.2)) •
      cellAmp p q (latticePoint L gh.1) (latticePoint L gh.2)

/-- The nonzero Poisson modes of the cell sum, defined through Poisson summation. -/
@[expose] def cellModes (L : ℝ) (p q ξ η : Mom d) (s : ℝ) : ℂ :=
  ((L ^ (2 * d) : ℝ) : ℂ)⁻¹ * cellSum L p q ξ η s - cellInt p q ξ η s

theorem cellSum_eq_modes {L : ℝ} (hL : 0 < L) (p q ξ η : Mom d) (s : ℝ) :
    cellSum L p q ξ η s = ((L ^ (2 * d) : ℝ) : ℂ) * (cellInt p q ξ η s + cellModes L p q ξ η s) := by
  have h : ((L ^ (2 * d) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hL _).ne'
  rw [cellModes]; field_simp; ring

/-! ### Joint regularity of the one-cell integrand -/

theorem contDiff_cellIntegrand (p q ξ η : Mom d) (s : ℝ) :
    ContDiff ℝ ∞ (fun z : Mom d × Mom d =>
      Real.fourierChar (inner ℝ z.1 ξ + inner ℝ z.2 η + s * inner ℝ z.1 z.2) •
        cellAmp p q z.1 z.2) := by
  have hphase : ContDiff ℝ ∞ (fun z : Mom d × Mom d =>
      ((Real.fourierChar (inner ℝ z.1 ξ + inner ℝ z.2 η + s * inner ℝ z.1 z.2) : Circle) : ℂ)) := by
    simp_rw [Real.fourierChar_apply]
    refine Complex.contDiff_exp.comp ?_
    refine ContDiff.mul ?_ contDiff_const
    refine Complex.ofRealCLM.contDiff.comp ?_
    refine contDiff_const.mul ?_
    exact ((contDiff_fst.inner ℝ contDiff_const).add (contDiff_snd.inner ℝ contDiff_const)).add
      (contDiff_const.mul (contDiff_fst.inner ℝ contDiff_snd))
  have hamp : ContDiff ℝ ∞ (fun z : Mom d × Mom d => cellAmp p q z.1 z.2) :=
    ((contDiff_thetaC (d := d)).comp (contDiff_fst.sub contDiff_const)).mul
      ((contDiff_thetaC (d := d)).comp (contDiff_snd.sub contDiff_const))
  simp_rw [Circle.smul_def]
  exact hphase.mul hamp

theorem hasCompactSupport_cellIntegrand (p q ξ η : Mom d) (s : ℝ) :
    HasCompactSupport (fun z : Mom d × Mom d =>
      Real.fourierChar (inner ℝ z.1 ξ + inner ℝ z.2 η + s * inner ℝ z.1 z.2) •
        cellAmp p q z.1 z.2) := by
  have hK : IsCompact (closedBall p (Real.sqrt d) ×ˢ closedBall q (Real.sqrt d)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro z hz
  have hz1 : thetaMom d (z.1 - p) ≠ 0 := by
    intro h; apply hz; simp [cellAmp, thetaC, h]
  have hz2 : thetaMom d (z.2 - q) ≠ 0 := by
    intro h; apply hz; simp [cellAmp, thetaC, h]
  have h1 := thetaMom_support_subset (d := d) hz1
  have h2 := thetaMom_support_subset (d := d) hz2
  simp only [mem_closedBall, dist_zero_right] at h1 h2
  exact ⟨by rw [mem_closedBall, dist_eq_norm]; exact h1, by rw [mem_closedBall, dist_eq_norm]; exact h2⟩

/-- Poisson summation for the cell sum. -/
theorem cellSum_eq_poisson {L : ℝ} (hL : 0 < L) (p q ξ η : Mom d) (s : ℝ) :
    cellSum L p q ξ η s = ((L ^ (2 * d) : ℝ) : ℂ) * ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
      cellInt p q (L • NTSP.intVec gh.1 + ξ) (L • NTSP.intVec gh.2 + η) s := by
  have hP := poisson_pair (F := fun x y =>
      Real.fourierChar (inner ℝ x ξ + inner ℝ y η + s * inner ℝ x y) • cellAmp p q x y)
    (contDiff_cellIntegrand p q ξ η s) (hasCompactSupport_cellIntegrand p q ξ η s) hL
  rw [cellSum, hP, Complex.ofReal_pow]
  congr 1
  rw [← (Equiv.neg ((Fin d → ℤ) × (Fin d → ℤ))).tsum_eq]
  refine tsum_congr fun gh => ?_
  have hint : Integrable (fun z : Mom d × Mom d =>
      Real.fourierChar (inner ℝ z.1 (L • NTSP.intVec gh.1 + ξ) +
        inner ℝ z.2 (L • NTSP.intVec gh.2 + η) + s * inner ℝ z.1 z.2) • cellAmp p q z.1 z.2) :=
    ((contDiff_cellIntegrand p q _ _ s).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_cellIntegrand p q _ _ s)
  have h2 := integral_prod_symm _ hint
  simp only at h2
  rw [cellInt_eq, ← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hneg : ∀ g : Fin d → ℤ, NTSP.intVec (-g) = -NTSP.intVec g := by
    intro g; ext i; simp [NTSP.intVec_apply]
  simp only [Equiv.neg_apply, Prod.fst_neg, Prod.snd_neg, smul_smul, hneg]
  congr 1
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [inner_add_right, inner_neg_right, inner_smul_right]
  ring

end WaveTurbulence.ApproxNT
