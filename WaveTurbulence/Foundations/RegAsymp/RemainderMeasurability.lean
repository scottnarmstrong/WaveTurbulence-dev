/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.AppRep
public import WaveTurbulence.Foundations.ClassJR.Symbol
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Temporal measurability of the literal NT remainder

The temporal parameter remains in the original source frequency space.
No integrability assumption is needed for measurability of the Bochner
integral in the leading term.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT WithLp

/-- Parameterwise measurability of the actual lattice expression, allowing
both its compact amplitude and its coefficient to vary. -/
theorem measurable_approxSum_parameter {P : Type*} [MeasurableSpace P] {d n : ℕ}
    (L μ : ℝ) (J : Finset (Fin n))
    {W : P → (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    {C : ({j : Fin n // j ∉ J} → ℝ) → P → ℂ}
    (hW : ∀ x y, Measurable (fun p => W p x y))
    (hC : ∀ α, Measurable (C α)) :
    Measurable (fun p => approxSum L μ (W p) (resProfile J (fun Ω => C (ofLp Ω) p))) := by
  unfold approxSum
  apply Measurable.tsum
  intro g
  unfold resProfile
  exact (hW _ _).mul (measurable_const.mul (hC _))

/-- The lattice expression is measurable in every measurable coefficient parameter. -/
theorem measurable_approxSum_symbol {d n : ℕ} {L μ : ℝ}
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (J : Finset (Fin n))
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) :
    Measurable (fun lam => approxSum L μ W (resProfile J (fun Ω => C (ofLp Ω) lam))) := by
  unfold approxSum
  apply Measurable.tsum
  intro g
  unfold resProfile
  exact measurable_const.mul (measurable_const.mul
    (hC.comp_measurable (measurable_const.prodMk measurable_id)).measurable)

/-- The leading singular integral is independent of the temporal parameter. -/
theorem stronglyMeasurable_approxApp_symbol {d n : ℕ} (L δ γ : ℝ)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (J : Finset (Fin n))
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) :
    StronglyMeasurable (fun lam => approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) W) := by
  have hm : StronglyMeasurable (fun p : EuclideanSpace ℝ {j : Fin n // j ∉ J} × (ℝ × ℝ) =>
      C (ofLp p.1) p.2) := hC.comp_measurable
        (((WithLp.measurable_ofLp 2 _).comp measurable_fst).prodMk measurable_snd)
  exact (stronglyMeasurable_const.mul hm.integral_prod_left).mul stronglyMeasurable_const

/-- In particular the actual raw normalized difference has a measurable λ slice. -/
theorem stronglyMeasurable_normalized_remainder {d n : ℕ} (L δ γ : ℝ)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (J : Finset (Fin n))
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) :
    StronglyMeasurable (fun lam => (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
      (approxSum L (L^(2*γ)*δ) W (resProfile J (fun Ω => C (ofLp Ω) lam)) -
        approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) W)) :=
  stronglyMeasurable_const.mul ((measurable_approxSum_symbol W J hC).stronglyMeasurable.sub
    (stronglyMeasurable_approxApp_symbol L δ γ W J hC))

end WaveTurbulence.RegAsymp
