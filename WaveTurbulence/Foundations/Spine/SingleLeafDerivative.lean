/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafInputDerivative
public import WaveTurbulence.Foundations.Spine.RootModifiedProfiles
/-! One coordinate derivative changes precisely one original positive input profile. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

noncomputable def singleLeafDerivative {w d : ℕ} (G : Garden w) (H : LeafProfiles w d)
    (l : ActualInputLeaves G) (j : Fin d) : LeafProfiles w d :=
  Function.update H l.1.1 (realPartialMom j (H l.1.1))

theorem singleLeafDerivative_input {w d : ℕ} (G : Garden w) (H : LeafProfiles w d)
    (l a : ActualInputLeaves G) (j : Fin d) :
    singleLeafDerivative G H l j a.1.1 =
      if a = l then realPartialMom j (H l.1.1) else H a.1.1 := by
  classical
  by_cases ha : a = l
  · subst a
    simp only [singleLeafDerivative, Function.update_self, ite_true]
  · have hraw : a.1.1 ≠ l.1.1 := fun h => ha (inputRawAddress_injective G h)
    simp only [singleLeafDerivative, Function.update_of_ne hraw, ha, ite_false]

theorem partialMom_ofReal_translate {d : ℕ} (j : Fin d) (H : Mom d → ℝ)
    (b x : Mom d) (hH : DifferentiableAt ℝ H (x + b)) :
    partialMom j (fun y => (H (y + b) : ℂ)) x = (realPartialMom j H (x + b) : ℂ) := by
  let f : Mom d → ℂ := fun y => (H y : ℂ)
  change fderiv ℝ (fun y => f (y + b)) x (EuclideanSpace.single j 1) = _
  rw [fderiv_comp_add_right]
  exact partialMom_ofReal j H (x + b) hH

end WaveTurbulence.LGSpine
