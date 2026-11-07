/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Cut2A.FiniteProducts
public import WaveTurbulence.Foundations.Fourier.Chi0
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
/-! Global Fourier measures for the literal radial bond cutoff. Affine pullback
keeps the mass fixed, so no frequency derivatives enter Stage 2 amplitudes. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff FourierTransform
namespace WaveTurbulence.FC23
open Cut2A
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]


def radialCut (x : V) : ℂ := (Fourier.chi0 ‖x‖ : ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem radialCut_smooth : ContDiff ℝ ∞ (radialCut : V → ℂ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : V) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    have hn : ‖y‖ ≤ 1 / 2 := (by simpa only [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < 1 / 2).le
    dsimp [radialCut]
    rw [Fourier.chi0_eq_one (by simpa only [abs_of_nonneg (norm_nonneg _)] using hn)]
    norm_num
  · have hn : ContDiffAt ℝ ∞ (fun y : V => ‖y‖) x := contDiffAt_norm ℝ hx
    change ContDiffAt ℝ ∞ (fun y : V => (Fourier.chi0 ‖y‖ : ℂ)) x
    exact
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Fourier.chi0_contDiff.contDiffAt.comp x hn)

omit [MeasurableSpace V] [BorelSpace V] in
theorem radialCut_compact : HasCompactSupport (radialCut : V → ℂ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : V) 1)
  intro x hx
  have hn : 1 ≤ ‖x‖ := (not_le.mp (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).le
  dsimp [radialCut]
  rw [Fourier.chi0_eq_zero (by simpa only [abs_of_nonneg (norm_nonneg _)] using hn)]
  rfl

/-- One fixed density for the unscaled radial cutoff. -/
def radialSchwartz : SchwartzMap V ℂ := radialCut_compact.toSchwartzMap radialCut_smooth

def radialMeasure : SpatialMeasure V V where
  μ := volume
  sigmaFinite := inferInstance
  frequency := id
  frequency_measurable := measurable_id
  amplitude := fun x => (𝓕 (radialSchwartz : SchwartzMap V ℂ) : SchwartzMap V ℂ) x
  amplitude_integrable := (𝓕 (radialSchwartz : SchwartzMap V ℂ)).integrable

theorem radialMeasure_value (x : V) : (radialMeasure : SpatialMeasure V V).value x = radialCut x := by
  have h := congrFun (radialSchwartz.continuous.fourierInv_fourier_eq
    (radialSchwartz : SchwartzMap V ℂ).integrable
    (𝓕 (radialSchwartz : SchwartzMap V ℂ)).integrable) x
  change (∫ a : V, (𝓕 (radialSchwartz : SchwartzMap V ℂ) : SchwartzMap V ℂ) a *
    (Real.fourierChar (inner ℝ a x) : ℂ)) = (radialSchwartz : SchwartzMap V ℂ) x
  simpa only [Real.fourierInv_eq, real_inner_comm, Circle.smul_def, smul_eq_mul,
    SchwartzMap.fourier_coe, mul_comm] using h


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

/-- Any affine bond momentum, including dependent or rank-deficient coordinates. -/
def bondMeasure (A : W →L[ℝ] V) (b : V) (R : ℝ) : SpatialMeasure W V :=
  (radialMeasure : SpatialMeasure V V).affine (R⁻¹ • A) (R⁻¹ • b)

omit [SecondCountableTopology W] in
theorem bondMeasure_mass (A : W →L[ℝ] V) (b : V) (R : ℝ) :
    (bondMeasure A b R).mass = (radialMeasure : SpatialMeasure V V).mass :=
  SpatialMeasure.affine_mass _ _ _

omit [SecondCountableTopology W] in
theorem bondMeasure_value (A : W →L[ℝ] V) (b : V) {R : ℝ} (hR : 0 < R) (x : W) :
    (bondMeasure A b R).value x = (Fourier.chi0 (‖A x + b‖ / R) : ℂ) := by
  rw [bondMeasure, SpatialMeasure.affine_value, radialMeasure_value]
  change (Fourier.chi0 ‖R⁻¹ • A x + R⁻¹ • b‖ : ℂ) = _
  rw [← smul_add, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  congr 2
  ring

/-- A whole finite bond family has mass C_d to the number of bonds, uniformly
in scales, affine offsets and conservation maps. -/
theorem bond_product_measure {ι : Type*} [Fintype ι]
    (A : ι → W →L[ℝ] V) (b : ι → V) (R : ι → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ F : SpatialMeasure W (ι → V),
      F.mass = (radialMeasure : SpatialMeasure V V).mass ^ Fintype.card ι ∧
      ∀ x, F.value x = ∏ i, (Fourier.chi0 (‖A i x + b i‖ / R i) : ℂ) := by
  refine ⟨SpatialMeasure.finiteProduct (fun i => bondMeasure (A i) (b i) (R i)), ?_, ?_⟩
  · rw [SpatialMeasure.finiteProduct_mass]
    simp only [bondMeasure_mass, Finset.prod_const, Finset.card_univ]
  · intro x
    rw [SpatialMeasure.finiteProduct_value]
    apply Finset.prod_congr rfl
    intro i _
    exact bondMeasure_value _ _ (hR i) x
end WaveTurbulence.FC23
