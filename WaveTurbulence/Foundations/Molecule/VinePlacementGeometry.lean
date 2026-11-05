/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistPrime

/-! # The designated placement and selected branches of its source vine

TARGET twist: all selected branching nodes except the lower joint lie
outside its removed subtree; any internal leaf-pair witness identifies
the same designated u23. These facts tie scenario and splice consumers
to the exact input vine.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The designated internal lower leaf makes the lower joint terminal among selected branches. -/
theorem placement_lower_terminal {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hP : IsPlacementAt G S b P) :
    ∀ z ∈ S, b.toNode.IsDesc z.toNode → z = b := by
  apply Molecpl.cl_terminal_branch G hB hCL hB.2.2.1
  intro i hi
  have he := (hP.2 i).mp hi
  subst i
  exact ⟨P.retained,by rw [← hP.1]; exact P.child⟩

/-- Every other selected branch keeps its exact address. -/
theorem selected_branch_fixed {S : Finset (GBranch G.tree)} {a b z : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hP : IsPlacementAt G S b P)
    (hz : z ∈ S) (hne : z ≠ b) : (coreBranchEquiv G P z).1 = z.1 := by
  apply coreBranchEquiv_fixed_val
  rw [hP.1]
  exact fun hd => hne (placement_lower_terminal G P hB hCL hP z hz hd)

/-- Every actual internal lower leaf-pair witness selects the same retained leaf. -/
theorem placement_retained_of_pair {S : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hP : IsPlacementAt G S b P)
    (hc : c ∈ S) {l : GLeaf G.tree} {i j : Fin 3} (hm : G.mark l = none)
    (hl : l.toNode = b.child i) (hr : (G.pair l).toNode = c.child j) : l = P.retained := by
  have hs := retained_slot_of_leaf_pair G hB hCL hc hm hl hr
  have hi := (hP.2 i).mp ((hs i).mpr rfl)
  apply Mole.leaf_toNode_injective
  calc
    l.toNode = b.child i := hl
    _ = P.lower.child P.keep := by rw [hP.1,hi]
    _ = P.retained.toNode := P.child.symm

/-- An outer source leaf-pair relation identifies the old u0 parent in the designated placement. -/
theorem placement_paired_parent {S : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hP : IsPlacementAt G S b P)
    (hc : c ∈ S) (hpair : Molecpl.OuterLeafPairAt G b c) :
    GNode.parent (G.pair P.retained).toNode P.paired_nonroot = c := by
  obtain ⟨l,i,j,hm,hl,hr,_hi⟩ := hpair
  have he := placement_retained_of_pair G P hB hCL hP hc hm hl hr
  subst l
  exact parent_eq_of_child P.paired_nonroot hr

/-- Fixed selected branch addresses retain their ancestor relation. -/
theorem fixed_branch_desc_iff {p q : GBranch G.tree}
    (hp : (coreBranchEquiv G P p).1 = p.1) (hq : (coreBranchEquiv G P q).1 = q.1) :
    (coreBranchEquiv G P p).toNode.IsDesc (coreBranchEquiv G P q).toNode ↔ p.toNode.IsDesc q.toNode := by
  change (coreBranchEquiv G P p).1.1 = (coreBranchEquiv G P q).1.1 ∧
    (coreBranchEquiv G P p).1.2 <+: (coreBranchEquiv G P q).1.2 ↔ p.1.1 = q.1.1 ∧ p.1.2 <+: q.1.2
  rw [hp,hq]

end WaveTurbulence.Twist
