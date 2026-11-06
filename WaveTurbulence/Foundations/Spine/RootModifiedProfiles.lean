/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.DecoratedLeafFactorization
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
/-! Actual leaf modifications retain the original raw addresses required by the producer API. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

def mapCoordinateSlot {I J : Type*} {d : ℕ} (f : I → J) :
    Option (I × Fin d) → Option (J × Fin d)
  | none => none
  | some (l, j) => some (f l, j)

theorem coordinateSlot_map {I J : Type*} [DecidableEq I] [DecidableEq J] {d : ℕ}
    (f : I → J) (hf : Function.Injective f) (c : Option (I × Fin d)) (l : I) (k : Mom d) :
    coordinateSlot (mapCoordinateSlot f c) (f l) k = coordinateSlot c l k := by
  cases c with
  | none => rfl
  | some c =>
    rcases c with ⟨a, j⟩
    simp only [mapCoordinateSlot, coordinateSlot, hf.eq_iff]

def inputRawAddress {w : ℕ} (G : Garden w) (l : ActualInputLeaves G) : Fin w × TTree.Path :=
  l.1.1

theorem inputRawAddress_injective {w : ℕ} (G : Garden w) :
    Function.Injective (inputRawAddress G) := by
  intro l r he
  apply Subtype.ext
  apply Subtype.ext
  exact he

/-- Individually modified raw profiles for one decoration-independent root-weight choice. -/
noncomputable def rootModifiedProfiles {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (H : LeafProfiles w d) (c : RootWeightChoices G d m) : LeafProfiles w d :=
  monomialLeafProfile H
    (fun t => mapCoordinateSlot (inputRawAddress G) (rootCoordinateSlots G hp c t))

theorem rootModifiedProfiles_input {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (H : LeafProfiles w d) (c : RootWeightChoices G d m) (l : ActualInputLeaves G) (k : Mom d) :
    rootModifiedProfiles G hp H c l.1.1 k =
      monomialLeafProfile (fun l : ActualInputLeaves G => H l.1.1)
        (rootCoordinateSlots G hp c) l k := by
  classical
  unfold rootModifiedProfiles monomialLeafProfile
  congr 1
  apply prod_congr rfl
  intro t _
  exact coordinateSlot_map (inputRawAddress G) (inputRawAddress_injective G) _ l k

end WaveTurbulence.LGSpine
