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

/-- Excluding the source (II-e) case produces the lower LP placement, without local premises. -/
theorem typeII_corePlacement_of_not_E {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b)
    (hcore : ¬ ∃ p ∈ S, ∃ q ∈ S, Molecpl.IsTypeIIE G a b p q) :
    ∃ P : CorePlacement G, P.lower = b := by
  obtain ⟨R,hn,hp,hcases⟩ := Molecpl.garden_typeII_local_cases G hV hCL
  rcases hcases with ⟨_hall,hlp⟩ | ⟨_hparent,hlp,_hpc⟩ | ⟨_hparent,hlp,_hpc⟩ | ⟨hparent,hall⟩
  · exact typeII_corePlacement G hV hCL R hlp
  · exact typeII_corePlacement G hV hCL R hlp
  · exact typeII_corePlacement G hV hCL R hlp
  · obtain ⟨hqn,hqp⟩ := hparent
    obtain ⟨i,hi,hio,_⟩ := Molecpl.lower_child_retained G hV.1 hCL R.right_mem hqn hqp
    have hdouble : Molecpl.DoubleLeafPairAt G R.left R.right :=
      Molecpl.double_leaf_pair_positions G (Molecpl.FourIncidences.doublePair R.left_row) hall
    have hdesc := Mole.block_one_root_descendants G hV.1
      hCL.1 hCL.2 R.left_mem
    exact (hcore ⟨R.left,R.left_mem,R.right,R.right_mem,⟨hn,hp⟩,⟨hqn,hqp⟩,
      hdouble,⟨i,hi,hio⟩,hdesc⟩).elim

/-- Every core CL vine produces the actual concrete unit-twist placement. -/
theorem corePlacement_exists {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : IsCoreCLVine G X S a b) : ∃ P : CorePlacement G, P.lower = b := by
  obtain ⟨hV,hCL,hcore⟩ := h
  rcases hcore with rfl | ⟨rfl,hcore⟩
  · exact typeI_corePlacement G hV hCL
  · exact typeII_corePlacement_of_not_E G hV hCL hcore

end WaveTurbulence.Twist
