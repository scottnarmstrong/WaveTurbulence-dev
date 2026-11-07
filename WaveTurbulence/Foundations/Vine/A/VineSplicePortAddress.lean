/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.CLIncidenceParents
/-! R83: the literal CL boundary preserves the port of an edge whose
original parent survives. No comparison isomorphism is supplied. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Mole TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
    (D : CLSpliceSlots G S a b)

/-- The upper boundary occupies exactly its original outer slot. -/
theorem boundary_selector_zero_iff (e : Fin 3) (s : Bool) (i : Fin 3) :
    clBoundarySelector e s i = 0 ↔ i = e := by
  unfold clBoundarySelector
  by_cases hi : i = e
  · simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte, iff_false]
    split_ifs <;> decide

/-- A boundary root with retained old parent must be the upper external child. -/
theorem cl_boundary_port (i : Fin 3)
    (hn : ((clSpliceBoundary hB hCL D).node i).1.2 ≠ [])
    (hp : GNode.parent ((clSpliceBoundary hB hCL D).node i) hn ∉ S ∨
      GNode.parent ((clSpliceBoundary hB hCL D).node i) hn = a) :
    ((clSpliceBoundary hB hCL D).node i).1.2.getLast hn = i := by
  have ha := hp.resolve_left (not_not.mpr (clSpliceBoundary_parent_mem hB hCL D i hn))
  have hab : a ≠ b := hB.2.2.2.1
  have key : ∀ j : Fin 3, ∀ hj : (clBaseBoundary a b D.excluded D.kept j).1.2 ≠ [],
      GNode.parent (clBaseBoundary a b D.excluded D.kept j) hj = a → j = 0 := by
    intro j hj hjp
    fin_cases j
    · rfl
    · exact (hab ((parent_child_branch_eq G b 1 hj).symm.trans hjp).symm).elim
    · exact (hab ((parent_child_branch_eq G b (otherOuterChild D.kept) hj).symm.trans hjp).symm).elim
  have hz := key (clBoundarySelector D.excluded (clSameSign a b) i) hn ha
  have hi := (boundary_selector_zero_iff D.excluded (clSameSign a b) i).mp hz
  subst i
  change (clBaseBoundary a b D.excluded D.kept
    (clBoundarySelector D.excluded (clSameSign a b) D.excluded)).1.2.getLast hn = D.excluded
  simp only [clBoundarySelector, ↓reduceIte, clBaseBoundary, Matrix.cons_val_zero]
  exact List.getLast_append_singleton a.1.2

/-- Inside a graft, a nonempty suffix keeps its last port; at the graft root
the surviving-parent condition forces the upper external port. -/
theorem cl_inside_port (i : Fin 3) (q : Path)
    (hq : q ∈ (spliceNodeSubtree G ((clSpliceBoundary hB hCL D).node i)).nodes)
    (ho : (spliceOldInsideNode (clSpliceBoundary hB hCL D) i q hq).1.2 ≠ [])
    (hn : (spliceNewInsideNode (clSpliceBoundary hB hCL D) i q hq).1.2 ≠ [])
    (hp : GNode.parent (spliceOldInsideNode (clSpliceBoundary hB hCL D) i q hq) ho ∉ S ∨
      GNode.parent (spliceOldInsideNode (clSpliceBoundary hB hCL D) i q hq) ho = a) :
    (spliceNewInsideNode (clSpliceBoundary hB hCL D) i q hq).1.2.getLast hn =
      (spliceOldInsideNode (clSpliceBoundary hB hCL D) i q hq).1.2.getLast ho := by
  by_cases hq0 : q = []
  · subst q
    have hp' : GNode.parent ((clSpliceBoundary hB hCL D).node i)
        (clSpliceBoundary_nonroot hB hCL D i) ∉ S ∨
        GNode.parent ((clSpliceBoundary hB hCL D).node i)
          (clSpliceBoundary_nonroot hB hCL D i) = a := by
      simpa only [spliceOldInsideNode, List.append_nil, GNode.parent] using hp
    simpa only [spliceNewInsideNode, spliceOldInsideNode, List.append_nil,
      List.getLast_append_singleton] using (cl_boundary_port hB hCL D i _ hp').symm
  · change (a.1.2 ++ i :: q).getLast hn =
      (((clSpliceBoundary hB hCL D).node i).1.2 ++ q).getLast ho
    rw [List.getLast_append_of_right_ne_nil _ _ (List.cons_ne_nil i q),
      List.getLast_append_of_right_ne_nil _ _ hq0, List.getLast_cons hq0]

end WaveTurbulence.VineA
