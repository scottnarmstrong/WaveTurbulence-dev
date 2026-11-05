/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Resonant.EnergyBilinear
public import WaveTurbulence.Foundations.Resonant.PVDecay
public import WaveTurbulence.Foundations.ApproxNT.AppTools

/-! # Exact momentum-energy normalization in source link coordinates

The source has x=child0-parent and y=parent-child2. The resonant momentum
parametrization therefore uses ell=x,w=-y. Delta and principal-value
factors both contribute the same positive factor2 in these coordinates.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Resonant Filter Topology

variable {d : ℕ}

/-- Reflection preserves the actual hyperplane delta, without an
integrability premise or a support condition. -/
theorem deltaInner_neg_right (F : Mom d → Mom d → ℂ) :
    NTSP.deltaInner (fun x y => F x (-y)) = NTSP.deltaInner F := by
  rw [NTSP.deltaInner,NTSP.deltaInner]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  congr 1
  exact integral_neg_eq_self (fun w : ↥(ℝ ∙ x)ᗮ => F x w) volume

/-- Exact delta normalization for the original source orientation. -/
theorem deltaInner_neg_right_ofReal (F : Mom d → Mom d → ℝ) :
    NTSP.deltaInner (fun x y => (F x (-y):ℂ)) = (2:ℂ)*(deltaInt F:ℂ) := by
  rw [deltaInner_neg_right (fun x y => (F x y:ℂ)),NTSP.deltaInner,deltaInt,← integral_complex_ofReal,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [Complex.ofReal_mul,← integral_complex_ofReal]
  simp only [mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_ofNat]
  ring

/-- The bilinear cutoff kernel is odd under the actual y reflection. -/
theorem pvTrunc_neg_right (ν : ℝ) (F : Mom d → Mom d → ℂ) :
    pvTrunc ν (fun x y => F x (-y)) = -pvTrunc ν F := by
  rw [pvTrunc_eq_integral,pvTrunc_eq_integral,← integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [← integral_neg,← integral_neg_eq_self
    (fun y : Mom d => (((1-Fourier.chi0 (ν*inner ℝ x y))/inner ℝ x y:ℝ):ℂ)*F x (-y)) volume]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  simp only [inner_neg_right,mul_neg,Fourier.chi0_even,div_neg,Complex.ofReal_neg,neg_neg,neg_mul]

/-- Every finite source cutoff has precisely the positive factor2 and
half-scaled physical energy parameter; no limiting premise is needed. -/
theorem pvTrunc_neg_right_ofReal (ν : ℝ) (F : Mom d → Mom d → ℝ) :
    pvTrunc ν (fun x y => (F x (-y):ℂ)) =
      (2:ℂ)*(energyInvIntegral Fourier.chi0 (ν/2) F:ℂ) := by
  rw [pvTrunc_neg_right ν (fun x y => (F x y:ℂ))]
  have he := energyInvIntegral_eq_bilinearFourierTruncation isPVCutoff_chi0 (ν/2) F
  change (energyInvIntegral Fourier.chi0 (ν/2) F:ℂ) =
    -(2:ℂ)⁻¹*pvTrunc (2*(ν/2)) (fun x y => (F x y:ℂ)) at he
  rw [show 2*(ν/2)=ν by ring] at he
  rw [he]
  ring

/-- Actual cutoff convergence for the reflected source kernel follows
from its decay and actual gradient bounds. This permits scalar extraction
before evaluating the source principal value. -/
theorem tendsto_pvTrunc_neg_right_ofReal_of_decay
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x) :
    Tendsto (fun ν : ℝ => pvTrunc ν (fun x y => (F x (-y):ℂ))) atTop
      (𝓝 ((2:ℂ)*(((∫ ℓ, energyInvSliceLimit F ℓ):ℝ):ℂ))) := by
  have hs : Tendsto (fun ν : ℝ => ν/2) atTop atTop := by
    simpa only [div_eq_mul_inv, id_eq] using
      Tendsto.atTop_mul_const (by norm_num : (0:ℝ) < (2:ℝ)⁻¹) tendsto_id
  have ht := (tendsto_energyInvIntegral_of_decay hd hF hgrad hDc hD isPVCutoff_chi0).comp hs
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  have hlim : Tendsto (fun ν : ℝ => pvTrunc ν (fun x y => (F x (-y):ℂ))) atTop
      (𝓝 ((2:ℂ)*(((∫ ℓ, energyInvSliceLimit F ℓ):ℝ):ℂ))) :=
    (hcomplex.const_mul (2:ℂ)).congr (fun ν => (pvTrunc_neg_right_ofReal ν F).symm)
  exact hlim

/-- The actual source principal value agrees with the real symmetric
quotient formula. Convergence is derived from decay and gradient bounds,
not assumed as a premise; this is shared by Mstar and Nstar bridges. -/
theorem pvOp_neg_right_ofReal_of_decay
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M : ℝ} (hd : 0 < d)
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ)) (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x) :
    pvOp (fun x y => (F x (-y):ℂ)) =
      (2:ℂ)*(((∫ ℓ, energyInvSliceLimit F ℓ):ℝ):ℂ) := by
  exact (tendsto_pvTrunc_neg_right_ofReal_of_decay hd hF hgrad hDc hD).limUnder_eq

end WaveTurbulence.RegAsymp
