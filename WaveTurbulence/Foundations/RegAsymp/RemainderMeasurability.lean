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

end WaveTurbulence.RegAsymp
