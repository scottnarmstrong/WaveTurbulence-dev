/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHingePair
/-! Small literal bridges from the actual chosen pair to its actual Cs fields. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open RedSplice
variable {w : ℕ} {G : Garden w} {σ : Prescription G}
variable {v : GBranch (stSt G σ).G.tree} {x y : GardenDart (stSt G σ).G}

theorem collectionChoices_first_of_pair (h : hingePair G σ v = some (x, y)) :
    (collectionChoices G σ).first v = some x := by
  change (hingePair G σ v).map Prod.fst = some x
  rw [h]
  rfl

theorem collectionChoices_second_of_pair (h : hingePair G σ v = some (x, y)) :
    (collectionChoices G σ).second v = some y := by
  change (hingePair G σ v).map Prod.snd = some y
  rw [h]
  rfl

end WaveTurbulence.VineA
