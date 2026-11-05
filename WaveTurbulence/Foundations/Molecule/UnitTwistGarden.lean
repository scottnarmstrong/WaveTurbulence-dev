/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CoreLeafSignTransport
public import WaveTurbulence.Foundations.Molecule.CoreVine

/-! # The actual garden produced by a unit twist

TARGET Definition twist, L1431--L1435. The ordered forest is the literal
subtree exchange. The actual pairing and marks are conjugated through
its concrete leaf bijection; all Garden axioms are proved.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Exchange the lower subtree with u0, switch its free children, and transport the actual pairing. -/
@[expose] noncomputable def unitTwistGarden : Garden w :=
  transportGardenPairing G (coreTwistForest G P) G.sig (coreLeafEquiv G P)
    (coreLeafMultiplier G P) (coreLeafMultiplier_pair G P) (coreLeafEquiv_sign G P)

/-- The signature is unchanged by the concrete unit twist. -/
theorem unitTwistGarden_sig : (unitTwistGarden G P).sig = G.sig := rfl

/-- Its forest is exactly the specified ordered subtree exchange. -/
theorem unitTwistGarden_tree : (unitTwistGarden G P).tree = coreTwistForest G P := rfl

/-- The pairing follows the actual leaf transport. -/
theorem unitTwistGarden_pair (l : GLeaf G.tree) :
    (unitTwistGarden G P).pair (coreLeafEquiv G P l) = coreLeafEquiv G P (G.pair l) :=
  transportGardenPairing_pair G _ _ _ _ _ _ l

/-- The original mark of every transported leaf is retained. -/
theorem unitTwistGarden_mark (l : GLeaf G.tree) :
    (unitTwistGarden G P).mark (coreLeafEquiv G P l) = G.mark l := by
  change G.mark ((coreLeafEquiv G P).symm (coreLeafEquiv G P l)) = _
  rw [Equiv.symm_apply_apply]

/-- Ordinary gardens remain ordinary gardens. -/
theorem unitTwistGarden_plain (hplain : G.IsPlain) : (unitTwistGarden G P).IsPlain :=
  transportGardenPairing_plain G _ _ _ _ _ _ hplain

/-- Couples remain couples, with the exact source carrier and signature. -/
theorem unitTwistGarden_couple {G : Garden 2} (P : CorePlacement G) (h : IsCouple G) :
    IsCouple (unitTwistGarden G P) :=
  ⟨unitTwistGarden_plain G P h.1,h.2⟩

/-- Every core source vine produces a valid actual twisted garden. -/
theorem unitTwistGarden_exists {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hcore : IsCoreCLVine G X S a b) :
    ∃ P : CorePlacement G, P.lower = b ∧ (unitTwistGarden G P).tree = coreTwistForest G P := by
  obtain ⟨P,hP⟩ := corePlacement_exists G hcore
  exact ⟨P,hP,rfl⟩

end WaveTurbulence.Twist
