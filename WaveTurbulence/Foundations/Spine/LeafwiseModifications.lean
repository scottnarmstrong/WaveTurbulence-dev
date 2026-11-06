/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! The individual weight and derivative modifications used in TARGET L2065–2067. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

/-- The real profile at address a is modified independently of every other leaf. The real
part of the complex iterated coordinate derivative agrees with the real derivative, and
retains exactly the source's frozen derivative convention. The leafwise gates apply once
the ordinary 40d seminorm bound for this explicit function is established. -/
noncomputable def modifiedLeafProfiles {w d : ℕ} (H : LeafProfiles w d)
    (weight : (Fin w × TTree.Path) → ℕ)
    (deriv : (Fin w × TTree.Path) → (Fin d → ℕ)) : LeafProfiles w d :=
  fun a k => jbr k ^ weight a * (iterPartial (deriv a) (fun x => (H a x : ℂ)) k).re

/-- At zero modification the individual input profile is unchanged. -/
theorem modifiedLeafProfiles_zero {w d : ℕ} (H : LeafProfiles w d) :
    modifiedLeafProfiles H (fun _ => 0) (fun _ _ => 0) = H := by
  funext a k
  simp only [modifiedLeafProfiles, iterPartial_zero_index, pow_zero, one_mul,
    Complex.ofReal_re]

end WaveTurbulence.LGSpine
