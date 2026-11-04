/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreUntouched

/-!
# Independent old-factor integration within one coarse source core

Currying the unchanged old coordinates gives an exact product integral.
This identity is used for unrestricted cores; ordering strips in the
first bad core are retained for their separate uniform pair estimate.
-/

public section
open MeasureTheory ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- Currying one actual coarse core preserves its literal Lebesgue measure. -/
theorem volume_preserving_sourceCoreOldTimes {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) :
    MeasurePreserving (sourceCoreOldTimes D b) volume volume := by
  let e : SourceCoreCoordinate D b ≃
      (Σ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, FactorCoordinate D.S a.1) := Equiv.refl _
  have hp := (volume_measurePreserving_piCurry
    (ι := {a : FactorIdx D.S // sourceCoreGroup D a = b}) (κ := fun a => FactorCoordinate D.S a.1)).comp
      (volume_measurePreserving_piCongrLeft (fun _ => ℝ) e)
  convert hp using 1
  funext z a j
  rfl

/-- Integrating independent old-factor functions within a coarse core factors exactly. -/
theorem lintegral_sourceCoreOldTimes_product {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (f : (a : {a : FactorIdx D.S // sourceCoreGroup D a = b}) → (FactorCoordinate D.S a.1 → ℝ) → ℝ≥0∞)
    (hf : ∀ a, Measurable (f a)) :
    (∫⁻ z : SourceCoreCoordinate D b → ℝ, ∏ a, f a (sourceCoreOldTimes D b z a)) =
      ∏ a, ∫⁻ y, f a y := by
  let e := MeasurableEquiv.piCurry
    (fun (a : {a : FactorIdx D.S // sourceCoreGroup D a = b}) (_ : FactorCoordinate D.S a.1) => ℝ)
  have he := (volume_preserving_sourceCoreOldTimes D b).lintegral_comp_emb e.measurableEmbedding
    (fun z => ∏ a, f a (z a))
  rw [he]
  exact lintegral_fintype_prod_eq_prod _ f hf

end WaveTurbulence.Sumint
