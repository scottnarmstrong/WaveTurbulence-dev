/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.ExchangeAddresses

/-! # Actual-garden involutivity of a unit twist

TARGET Definition twist: twisting in the reverse placement restores the
exact garden, including its ordered trees, pairing, marks, and signature.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The proof-independent uniform address formula for the actual core leaf bijection. -/
theorem coreLeafEquiv_address (l : GLeaf G.tree) :
    (coreLeafEquiv G P l).1 = exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep l.1 := by
  exact exchangeLeafEquiv_address (commonForest G P.lower) (collapsedRoot G P.lower)
    (pairedHole G P) P.keep (lowerCrown G P.lower)
    (forestLeafCast (restore_commonForest G P.lower).symm l)

/-- The two concrete actual leaf bijections reverse one another at every address. -/
theorem coreLeafEquiv_twice_val (l : GLeaf G.tree) :
    (coreLeafEquiv (unitTwistGarden G P) (reversePlacement G P) (coreLeafEquiv G P l)).1 = l.1 := by
  rw [coreLeafEquiv_address (unitTwistGarden G P) (reversePlacement G P) (coreLeafEquiv G P l)]
  change exchangeAddress (coreBranchEquiv G P P.lower).1
    ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).1 P.keep (coreLeafEquiv G P l).1 = _
  rw [unitTwistGarden_pair,coreBranchEquiv_lower_val,coreLeafEquiv_paired_val,coreLeafEquiv_address]
  exact exchangeAddress_twice (commonForest G P.lower) (collapsedRoot G P.lower)
    (pairedHole G P) P.keep (lowerCrown G P.lower)
    (forestLeafCast (restore_commonForest G P.lower).symm l)

/-- Equality of all computational garden fields determines the garden. -/
theorem garden_eq_of_fields {H K : Garden w} (hs : H.sig = K.sig) (ht : H.tree = K.tree)
    (hp : HEq H.pair K.pair) (hm : HEq H.mark K.mark) : H = K := by
  cases H
  cases K
  cases hs
  cases ht
  cases hp
  cases hm
  rfl

/-- A leaf bijection with unchanged addresses and conjugate pairing determines garden equality. -/
theorem garden_eq_of_leaf_transport {H K : Garden w} (hs : H.sig = K.sig) (ht : H.tree = K.tree)
    (e : GLeaf K.tree ≃ GLeaf H.tree) (hv : ∀ l, (e l).1 = l.1)
    (hp : ∀ l, H.pair (e l) = e (K.pair l)) (hm : ∀ l, H.mark (e l) = K.mark l) : H = K := by
  cases H
  cases K
  cases hs
  cases ht
  have he (l) : e l = l := Subtype.ext (hv l)
  have hpair := funext (fun l => by simpa only [he] using hp l)
  have hmark := funext (fun l => by simpa only [he] using hm l)
  cases hpair
  cases hmark
  rfl

/-- The unit twist is an involution on the actual Garden carrier, including pairing and marks. -/
theorem unitTwistGarden_involutive :
    unitTwistGarden (unitTwistGarden G P) (reversePlacement G P) = G := by
  let e := (coreLeafEquiv G P).trans (coreLeafEquiv (unitTwistGarden G P) (reversePlacement G P))
  apply garden_eq_of_leaf_transport (H := unitTwistGarden (unitTwistGarden G P) (reversePlacement G P))
    (K := G) rfl (coreTwistForest_involutive G P) e
  · exact coreLeafEquiv_twice_val G P
  · intro l
    change (unitTwistGarden (unitTwistGarden G P) (reversePlacement G P)).pair
      (coreLeafEquiv (unitTwistGarden G P) (reversePlacement G P) (coreLeafEquiv G P l)) = _
    rw [unitTwistGarden_pair (unitTwistGarden G P) (reversePlacement G P) (coreLeafEquiv G P l),
      unitTwistGarden_pair G P l]
    rfl
  · intro l
    change (unitTwistGarden (unitTwistGarden G P) (reversePlacement G P)).mark
      (coreLeafEquiv (unitTwistGarden G P) (reversePlacement G P) (coreLeafEquiv G P l)) = _
    rw [unitTwistGarden_mark (unitTwistGarden G P) (reversePlacement G P) (coreLeafEquiv G P l),
      unitTwistGarden_mark G P l]

end WaveTurbulence.Twist
