/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.ParentChains
public import WaveTurbulence.Foundations.Molecule.LowerOtherGeometry

/-! # Exhaustion of the local PC/LP patterns at a type-II lower joint

TARGET molecpl (2). The parent-oriented patterns are (II-a)/(II-b),
(II-c), (II-d), and (II-e). These auxiliary predicates retain actual dart
labels; the child-leaf and descendant interpretation is supplied separately.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree Vine
variable {w : ℕ} (G : Garden w)

/-- The two doubled incidences are LP incidences. -/
@[expose] def RungAllLP {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : EndRungData G.molecule S a b) : Prop :=
  ∀ i : Fin 2, ¬ IsPCDart G ((FourIncidences.doublePair R.left_row).dart i)

/-- The lower non-parent incidence is an LP incidence. -/
@[expose] def LowerLP {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : EndRungData G.molecule S a b) : Prop :=
  ¬ IsPCDart G (G.molecule.mate (R.right_row.dart 2))

/-- The four parent-oriented local patterns, before interpreting descendant relations. -/
@[expose] def LocalTypeIICases {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : EndRungData G.molecule S a b) : Prop :=
  (RungAllLP G R ∧ LowerLP G R) ∨
  ((∃ hn : R.left.1.2 ≠ [], GNode.parent R.left.toNode hn = R.right) ∧ LowerLP G R ∧
    ∃ i : Fin 2, IsPCDart G ((FourIncidences.doublePair R.left_row).dart i)) ∨
  ((∃ hn : R.right.1.2 ≠ [], GNode.parent R.right.toNode hn = R.left) ∧ LowerLP G R ∧
    ∃ i : Fin 2, IsPCDart G ((FourIncidences.doublePair R.left_row).dart i)) ∨
  ((∃ hn : R.right.1.2 ≠ [], GNode.parent R.right.toNode hn = b) ∧ RungAllLP G R)

/-- Exhaust the local actual-dart patterns without a local-geometry assumption. -/
theorem typeII_local_cases {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : EndRungData G.molecule S a b) (hn : b.1.2 ≠ [])
    (hp : GNode.parent b.toNode hn = R.left) : LocalTypeIICases G R := by
  let Q := (FourIncidences.doublePair R.left_row)
  let x := G.molecule.mate (R.right_row.dart 2)
  have hx : G.molecule.atom x = b := R.right_row.neighbor_eq 2
  have hy : G.molecule.atom (G.molecule.mate x) = R.right := by
    dsimp [x]; rw [G.molecule.mate_mate]; exact R.right_row.atom_eq 2
  by_cases hpc : IsPCDart G x
  · have hq : ∃ hq : R.right.1.2 ≠ [], GNode.parent R.right.toNode hq = b := by
      rcases pc_dart_parent G hpc hx hy with ⟨hn',hp'⟩ | hq
      · exact (R.distinct (hp.symm.trans hp')).elim
      · exact hq
    obtain ⟨hqn,hqp⟩ := hq
    refine Or.inr (Or.inr (Or.inr ⟨⟨hqn,hqp⟩,?_⟩))
    intro i
    exact parent_chain_no_pc G hn hp hqn hqp (Q.atom_eq i) (Q.neighbor_eq i)
  · have hlp : LowerLP G R := hpc
    rcases doubled_label_split G Q with hall | ⟨h0,h1⟩ | ⟨h0,h1⟩
    · refine Or.inl ⟨?_,hlp⟩
      intro i; fin_cases i
      · exact hall.1
      · exact hall.2
    · rcases pc_dart_parent G h0 (Q.atom_eq 0) (Q.neighbor_eq 0) with hparent | hparent
      · exact Or.inr (Or.inl ⟨hparent,hlp,0,h0⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hparent,hlp,0,h0⟩))
    · rcases pc_dart_parent G h1 (Q.atom_eq 1) (Q.neighbor_eq 1) with hparent | hparent
      · exact Or.inr (Or.inl ⟨hparent,hlp,1,h1⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hparent,hlp,1,h1⟩))

/-- Every current CL type-II vine has one of the actual local patterns, including m=1. -/
theorem garden_typeII_local_cases {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ (R : EndRungData G.molecule S a b) (hn : b.1.2 ≠ []),
      GNode.parent b.toNode hn = R.left ∧ LocalTypeIICases G R := by
  obtain ⟨R,hn,hp⟩ := typeII_oriented_end_rung G hV hCL
  exact ⟨R,hn,hp,typeII_local_cases G R hn hp⟩

end WaveTurbulence.Molecpl
