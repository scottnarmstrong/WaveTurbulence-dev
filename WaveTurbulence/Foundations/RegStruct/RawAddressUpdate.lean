/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.RawTreeSurgery
public import WaveTurbulence.Foundations.RegStruct.DecodedCouple
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ForestCollapse

/-! # Source operations as literal address updates (DH21 Definition 4.2) -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Replace the rooted shape at a global address. -/
def updateAddressForest {w : ℕ} (tree : Fin w → TTree) (a : Fin w × Path) (s : TTree) :
    Fin w → TTree := Function.update tree a.1 (Comb.replaceAt (tree a.1) a.2 s)

/-- The raw code forest and the actual garden forest have exactly the same indexing. -/
theorem raw_tree_eq_coupleForest (Q : RegCpl) : Q.raw.tree = coupleForest Q := by
  funext j
  fin_cases j <;> simp [RegCpl.raw,RawCpl.tree,coupleForest]

/-- The raw A-step is two literal address updates, including when both roots lie in one tree. -/
theorem raw_opA_updates (R : RawCpl) (x y : Fin 2 × Path) (c : MiniCplCode) :
    (R.opA x y c).tree =
      updateAddressForest (updateAddressForest R.tree x (.node .leaf .leaf .leaf))
        y (.node .leaf .leaf .leaf) := by
  funext j
  obtain ⟨i,p⟩ := x
  obtain ⟨k,r⟩ := y
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp [RawCpl.opA,RawCpl.mapTree,RawCpl.tree,updateAddressForest,
      Function.update,setAt_eq_replaceAt]

/-- The literal mini-tree shape with the old subtree at the lone slot. -/
def miniTreeContext (m : MiniTreeCode) (s : TTree) : TTree :=
  node3 fun i => if i = m.c then node3 (fun k => if k = m.lone then s else .leaf) else .leaf

/-- The raw B-step is a literal update by its mini-tree context. -/
theorem raw_opB_update (R : RawCpl) (a : Fin 2 × Path) (m : MiniTreeCode) :
    (R.opB a m).tree = updateAddressForest R.tree a
      (miniTreeContext m ((R.tree a.1).subtreeAt a.2)) := by
  funext j
  obtain ⟨i,p⟩ := a
  fin_cases i <;> fin_cases j <;>
    simp [RawCpl.opB,RawCpl.mapTree,RawCpl.tree,updateAddressForest,
      miniTreeContext,Function.update,setAt_eq_replaceAt]

/-- Filling a mini-tree adds exactly its two branching nodes. -/
theorem miniTreeContext_order (m : MiniTreeCode) (s : TTree) :
    (miniTreeContext m s).order = s.order + 2 := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> simp [miniTreeContext,node3,MiniTreeCode.lone,TTree.order]

/-- Source total extraction agrees with COMB's actual extracted subtree on every valid node. -/
theorem subtreeAt_eq_of_subtree (t : TTree) (p : Path) (s : TTree)
    (h : Comb.subtree t p = some s) : t.subtreeAt p = s := by
  cases p with
  | nil =>
    have hs : t = s := by simpa only [Comb.subtree,Option.some.injEq] using h
    simp only [TTree.subtreeAt,hs]
  | cons i p =>
    cases t with
    | leaf => simp only [Comb.subtree,reduceCtorEq] at h
    | node l m r =>
      fin_cases i <;> simp [Comb.subtree] at h <;>
        simp [TTree.subtreeAt,subtreeAt_eq_of_subtree _ _ _ h]
termination_by structural t

/-- The source B-operation adds exactly two branching nodes at every valid node. -/
theorem raw_opB_order (R : RawCpl) (a : Fin 2 × Path) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) :
    (∑ j, ((R.opB a m).tree j).order) = (∑ j, (R.tree j).order) + 2 := by
  let A : GNode R.tree := ⟨a,ha⟩
  have hs : (R.tree a.1).subtreeAt a.2 = Comb.nodeSubtree A :=
    subtreeAt_eq_of_subtree _ _ _ (Comb.nodeSubtree_spec A)
  have ho := Comb.replaceNodeForest_order R.tree A
    (miniTreeContext m ((R.tree a.1).subtreeAt a.2))
  have hso := congrArg TTree.order hs
  rw [miniTreeContext_order] at ho
  rw [raw_opB_update]
  change (∑ j, (updateAddressForest R.tree a (miniTreeContext m ((R.tree a.1).subtreeAt a.2)) j).order) +
      (Comb.nodeSubtree A).order =
      (∑ j, (R.tree j).order) + (((R.tree a.1).subtreeAt a.2).order + 2) at ho
  omega

end WaveTurbulence.Reg
