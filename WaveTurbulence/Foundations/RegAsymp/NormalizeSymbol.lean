/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CoordinateDerivative
public import WaveTurbulence.Foundations.RegAsymp.MomentWeights

/-! # Fixed-frequency coefficient normalization for Prop6.4

The positive scalar g is the actual common frequency envelope. Dividing
the symbol by g gives the NT derivative and moment budgets with C0=1;
the factor g is retained outside the NT approximation and integrated later.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WithLp
open scoped ContDiff ENNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem wordDeriv_const_smul {f : EuclideanSpace ℝ ι → ℂ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) {k : ℕ} (v : Fin k → ι) (x : EuclideanSpace ℝ ι) :
    ApproxNT.wordDeriv (fun y => c • f y) v x = c • ApproxNT.wordDeriv f v x := by
  unfold ApproxNT.wordDeriv
  rw [iteratedFDeriv_const_smul_apply' ((hf.of_le (by exact_mod_cast le_top)).contDiffAt)]
  rfl

omit [DecidableEq ι] in
/-- Normalization and Euclidean pullback preserve the source smoothness. -/
theorem normalized_symbol_contDiff {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (g : ℝ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => g⁻¹ • f (ofLp x)) :=
  (hf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).contDiff).const_smul _

/-- All NT coordinate-word bounds with unit Gevrey4 budget follow from
the actual normalized l1-operator derivative envelope. -/
theorem normalized_symbol_wordDeriv {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    {g : ℝ} (hg : 0 < g)
    (hD : ∀ k, ∫⁻ α, ClassJR.dnorm k (fun β (_ : Unit) => f β) α () ≤
      ENNReal.ofReal (g * (4*k).factorial)) :
    ApproxNT.WordDerivL1 (fun x : EuclideanSpace ℝ ι => g⁻¹ • f (ofLp x))
      (fun k => ((4*k).factorial : ℝ)) := by
  have hfe : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => f (ofLp x)) :=
    hf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).contDiff
  intro k v
  calc
    _ = ∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal g⁻¹ *
        ‖ApproxNT.wordDeriv (fun y => f (ofLp y)) v x‖ₑ := by
      apply lintegral_congr
      intro x
      rw [wordDeriv_const_smul hfe,enorm_smul,← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hg.le)]
    _ ≤ ∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal g⁻¹ *
        ClassJR.dnorm k (fun β (_ : Unit) => f β) (ofLp x) () := by
      apply lintegral_mono
      intro x
      exact mul_le_mul_right (enorm_wordDeriv_le_dnorm hf v x) _
    _ = ENNReal.ofReal g⁻¹ * ∫⁻ α, ClassJR.dnorm k (fun β (_ : Unit) => f β) α () := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact congrArg (fun z => ENNReal.ofReal g⁻¹ * z)
        ((PiLp.volume_preserving_ofLp ι).lintegral_comp_emb
          (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding
          (fun α => ClassJR.dnorm k (fun β (_ : Unit) => f β) α ()))
    _ ≤ ENNReal.ofReal g⁻¹ * ENNReal.ofReal (g * (4*k).factorial) := mul_le_mul_right (hD k) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hg.le)]
      congr 1
      field_simp

omit [DecidableEq ι] in
/-- The maximum-coordinate moment is normalized by the same scalar g. -/
theorem normalized_symbol_moment {f : (ι → ℝ) → ℂ} {g b : ℝ} (hg : 0 < g)
    (hM : ∫⁻ α, ENNReal.ofReal (ApproxNT.wmax b α) * ‖f α‖ₑ ≤ ENNReal.ofReal g) :
    ∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal (ApproxNT.wmax b (ofLp x)) *
      ‖g⁻¹ • f (ofLp x)‖ₑ ≤ 1 := by
  have he (x : EuclideanSpace ℝ ι) : ENNReal.ofReal (ApproxNT.wmax b (ofLp x)) *
      ‖g⁻¹ • f (ofLp x)‖ₑ = ENNReal.ofReal g⁻¹ *
        (ENNReal.ofReal (ApproxNT.wmax b (ofLp x)) * ‖f (ofLp x)‖ₑ) := by
    rw [enorm_smul,← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hg.le)]
    ring
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    (PiLp.volume_preserving_ofLp ι).lintegral_comp_emb
      (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding
      (fun α => ENNReal.ofReal (ApproxNT.wmax b α) * ‖f α‖ₑ)]
  calc _ ≤ ENNReal.ofReal g⁻¹ * ENNReal.ofReal g := mul_le_mul_right hM _
    _ = 1 := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hg.le),inv_mul_cancel₀ hg.ne',ENNReal.ofReal_one]

end WaveTurbulence.RegAsymp
