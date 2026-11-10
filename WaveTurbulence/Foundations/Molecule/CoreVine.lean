/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CorePlacements

/-! # Core CL vines and actual placement production

TARGET molecpl, final paragraph: bad CL vines excluding scenario (II-e).
The definition uses only current source vine/CL premises and actual
scenario (II-e), not an assumed surgery witness.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w)

/-- A bad CL vine which is not the non-core configuration (II-e). -/
@[expose] def IsCoreCLVine (X : VineType) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) : Prop :=
  G.molecule.IsVine X S a b ∧ Mole.CLParentPattern G S a b ∧
    (X = .I ∨ X = .II ∧ ¬ ∃ p ∈ S, ∃ q ∈ S, Molecpl.IsTypeIIE G a b p q)

end WaveTurbulence.Twist
