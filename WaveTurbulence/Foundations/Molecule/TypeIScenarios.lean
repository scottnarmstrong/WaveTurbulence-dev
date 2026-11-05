/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.PortShim
public import WaveTurbulence.Foundations.Molecule.TypeILeafPair
public import WaveTurbulence.Foundations.Molecule.ChildSigns

/-!
# TARGET molecpl (1): the exhaustive exclusive type-I scenarios

The theorem is on the actual current B2 vine predicate and actual garden
parent/leaf pairing operations. Both cases retain the paired u23 leaf
and its sign-preserving lower child slot.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- TARGET (I-a): the lower branch is outer, and u23 pairs to the middle upper child. -/
@[expose] def IsTypeIA (a b : GBranch G.tree) : Prop :=
  ∃ i : Fin 3, i ≠ 1 ∧ a.child i = b.toNode ∧
    ∃ (k : Fin 3) (l : GLeaf G.tree), k ≠ 1 ∧ G.mark l = none ∧
      l.toNode = b.child k ∧ (G.pair l).toNode = a.child 1

/-- TARGET (I-b): the lower branch is middle, and u23 pairs to an outer upper child. -/
@[expose] def IsTypeIB (a b : GBranch G.tree) : Prop :=
  a.child 1 = b.toNode ∧ ∃ j : Fin 3, j ≠ 1 ∧
    ∃ (k : Fin 3) (l : GLeaf G.tree), k ≠ 1 ∧ G.mark l = none ∧
      l.toNode = b.child k ∧ (G.pair l).toNode = a.child j

/-- TARGET Proposition molecpl (1), L1398–L1404: every type-I CL vine has exactly one of (I-a),(I-b). -/
theorem typeI_scenarios {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .I S a b) (hCL : Mole.CLParentPattern G S a b) :
    (IsTypeIA G a b ∨ IsTypeIB G a b) ∧ ¬ (IsTypeIA G a b ∧ IsTypeIB G a b) := by
  have hex : ¬ (IsTypeIA G a b ∧ IsTypeIB G a b) := by
    rintro ⟨⟨i,hi,hbi,_⟩,hb1,_⟩
    exact hi (child_injective G a (hbi.trans hb1.symm))
  refine ⟨?_,hex⟩
  obtain ⟨i,hbi⟩ := typeI_child G hV hCL
  obtain ⟨l,k,j,hmark,hl,hp,hk⟩ := typeI_leaf_pair G hV hCL
  have hsign : G.sign (a.child j) = -G.sign (a.child i) := by
    rw [hbi,← hp]
    have he : G.sign (G.pair l).toNode = -G.sign l.toNode :=
      G.pair_sign l (Garden.pair_ne_of_unmarked hmark)
    rw [he,hl,Mole.outer_child_sign G b k hk]
  rcases (opposite_child_sign_iff G a i j).mp hsign with ⟨hi,rfl⟩ | ⟨rfl,hj⟩
  · exact Or.inl ⟨i,hi,hbi,k,l,hk,hmark,hl,hp⟩
  · exact Or.inr ⟨hbi,j,hj,k,l,hk,hmark,hl,hp⟩

end WaveTurbulence.Molecpl
