/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fold6
import Mathlib.Tactic

/-!
# VINE-B Part I (7): the fold invariant is preserved by a splice step and by the whole fold
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.RedSplice.SpMap

variable {w : ℕ} {G0 : Garden w} {P : CLBlock G0 → Prop} {st : SpState G0} (T : FoldInv P st)
  (u : CLBlock G0) {a' b' : GBranch st.G.tree}
  (hB' : st.G.molecule.IsBlock (st.M.pb u.atoms) a' b') (hCL' : CLParentPattern st.G (st.M.pb u.atoms) a' b')
  (D : CLSpliceSlots st.G (st.M.pb u.atoms) a' b')

/-- The actual old parent of a retained leaf contracts to its new parent (copied from VINE-A's
`stepB_leaf_parent`, which is not in the farm). -/
theorem stepB_leaf_parent' {H : Garden w} {S : Finset (GBranch H.tree)}
    {a b : GBranch H.tree} (hB : H.molecule.IsBlock S a b) (hCL : CLParentPattern H S a b)
    (D : CLSpliceSlots H S a b) (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree)
    (hn : l.1.2 ≠ []) (ho : (clSplicedLeafNameEquiv hB hCL D l).1.1.2 ≠ []) :
    stepB hB hCL D (GNode.parent l.toNode hn) =
      rep S a (GNode.parent (clSplicedLeafNameEquiv hB hCL D l).1.toNode ho) := by
  apply eq_rep_of_contract hB.2.1 (stepB_mem hB hCL D _)
  have h1 := clSplicedBranchName_contract hB hCL D (GNode.parent l.toNode hn)
  have h2 := cl_leaf_name_parent_contract hB hCL D l hn ho
  change contractVertex S (clSplicedBranchNameEquiv hB hCL D _).1 = _
  rw [h1]
  exact h2.symm

theorem core_parentL (hU : ∀ v ∈ u.atoms, st.cls v = none) (ha : st.M.ob a' = u.upper)
    (ℓ : GLeaf (clSplicedGardenOfSlots hB' hCL' D).tree) (hn : ℓ.1.2 ≠ [])
    (ho : (T.leaf (clSplicedLeafNameEquiv hB' hCL' D ℓ).1).1.2 ≠ []) :
    st.M.ob (stepB hB' hCL' D (GNode.parent ℓ.toNode hn)) =
      repC (clsAdd st.cls u.atoms u.upper) (GNode.parent (T.leaf (clSplicedLeafNameEquiv hB' hCL' D ℓ).1).toNode ho) := by
  have hn1 : (clSplicedLeafNameEquiv hB' hCL' D ℓ).1.1.2 ≠ [] := fun h =>
    hn ((clSplicedLeafName_root_iff hB' hCL' D ℓ).mp h)
  apply (congrArg st.M.ob (stepB_leaf_parent' hB' hCL' D ℓ hn hn1)).trans
  rw [repC_clsAdd]
  have hp := T.parentL (clSplicedLeafNameEquiv hB' hCL' D ℓ).1 hn1 ho
  by_cases hx : GNode.parent (T.leaf (clSplicedLeafNameEquiv hB' hCL' D ℓ).1).toNode ho ∈ u.atoms
  · have hc : GNode.parent (clSplicedLeafNameEquiv hB' hCL' D ℓ).1.toNode hn1 ∈ st.M.pb u.atoms :=
      (SpMap.mem_pb st.M).mpr (by rw [hp, SpMap.repC_mem_iff st.hcls hU]; exact hx)
    rw [rep_of_mem hc]
    simp only [hx, ↓reduceIte]
    exact ha
  · have hc : GNode.parent (clSplicedLeafNameEquiv hB' hCL' D ℓ).1.toNode hn1 ∉ st.M.pb u.atoms := fun h =>
      hx ((SpMap.repC_mem_iff st.hcls hU).mp (by rw [← hp]; exact (SpMap.mem_pb st.M).mp h))
    rw [rep_of_notMem hc]
    simp only [hx, ↓reduceIte]
    exact hp


/-- One more actual CL splice of the fold. -/
noncomputable def FoldInv.add (T : FoldInv P st) (u : CLBlock G0) (hU : ∀ v ∈ u.atoms, st.cls v = none)
    (hdis : ∀ u1, P u1 → Disjoint u1.atoms u.atoms) :
    FoldInv (fun u1 => P u1 ∨ u1 = u) (st.add u hU) := by
  let h := SpMap.pb_block st.M st.hcls hU u.isBlock u.cl
  let a' := Classical.choose h
  let h2 := Classical.choose_spec h
  let b' := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let hB' := h3.2.2.1
  let hCL' := h3.2.2.2
  let D := clSpliceSlotsOfBlock hB' hCL'
  have hs := clSignedBoundary_sign hB' hCL' D.excluded D.kept D.excluded_missing D.excluded_ne_middle
    D.kept_ne_middle
  exact
  { node := fun y => T.node (spNode (clSpliceBoundary hB' hCL' D) y)
    inj := fun y y' e => spNode_inj _ (T.inj e)
    range := fun x => core_range T u hB' hCL' D hU h3.1 x
    tree_eq := fun y => (T.tree_eq _).trans (spNode_idx _ y)
    root := fun y => (T.root _).trans (spNode_root_iff _ (clSpliceBoundary_nonroot hB' hCL' D) y)
    br_node := fun c => by
      change (st.M.ob (stepB hB' hCL' D c)).toNode = T.node (spNode _ c.toNode)
      rw [T.br_node]
      exact congrArg T.node (stepB_node hB' hCL' D c)
    leaf := fun ℓ => T.leaf (clSplicedLeafNameEquiv hB' hCL' D ℓ).1
    leaf_node := fun ℓ => (T.leaf_node _).trans (congrArg T.node (leafName_node hB' hCL' D ℓ))
    pair := fun ℓ => (congrArg T.leaf (clSplicedLeafName_pair hB' hCL' D ℓ)).trans (T.pair _)
    mark := fun ℓ => (clSplicedLeafName_mark hB' hCL' D ℓ).trans (T.mark _)
    parentL := fun ℓ hn ho => core_parentL T u hB' hCL' D hU h3.1 ℓ hn ho
    sign := fun y => (T.sign _).trans (spNode_sign _ hs y)
    child := fun c i hc => core_child T u hB' hCL' D h3.1 c i hc
    crown := fun c u1 hu1 hc i => core_crown T u hB' hCL' D hdis hU h3.1 h3.2.1 c u1 hu1 hc i
    cls_none := fun v => by
      change clsAdd st.cls u.atoms u.upper v = none ↔ _
      by_cases hv : v ∈ u.atoms
      · rw [clsAdd_of_mem hv]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h; exact absurd hv (h u (Or.inr rfl))
      · rw [clsAdd_of_notMem hv, T.cls_none]
        constructor
        · intro h u1 hu1
          rcases hu1 with hu1 | rfl
          · exact h u1 hu1
          · exact hv
        · intro h u1 hu1
          exact h u1 (Or.inl hu1) }


/-- The fold step (a block meeting no earlier block is spliced). -/
noncomputable def FoldInv.step (T : FoldInv P st) (u : CLBlock G0)
    (hdis : ∀ u1, P u1 → Disjoint u1.atoms u.atoms) :
    FoldInv (fun u1 => P u1 ∨ u1 = u) (spliceStep st u) := by
  have hU : ∀ v ∈ u.atoms, st.cls v = none := fun v hv =>
    (T.cls_none v).mpr (fun u1 hu1 => Finset.disjoint_right.mp (hdis u1 hu1) hv)
  have e : spliceStep st u = st.add u hU := by
    unfold spliceStep
    exact dif_pos hU
  rw [e]
  exact T.add u hU hdis

/-- The fold invariant along a pairwise disjoint list of blocks. -/
noncomputable def FoldInv.fold (l : List (CLBlock G0))
    (hl : l.Pairwise (fun u u' => Disjoint u.atoms u'.atoms)) :
    ∀ (P : CLBlock G0 → Prop) (st : SpState G0), FoldInv P st →
      (∀ u ∈ l, ∀ u1, P u1 → Disjoint u1.atoms u.atoms) →
      FoldInv (fun u1 => P u1 ∨ u1 ∈ l) (l.foldl spliceStep st) := by
  induction l with
  | nil =>
    intro P st T _
    exact T.congr (fun u1 => by simp)
  | cons u l ih =>
    intro P st T hd
    have hl' := List.pairwise_cons.mp hl
    have T1 := T.step u (hd u (List.mem_cons_self ..))
    have T2 := ih hl'.2 _ _ T1 (fun u2 hu2 u1 hu1 => by
      rcases hu1 with hu1 | rfl
      · exact hd u2 (List.mem_cons_of_mem _ hu2) u1 hu1
      · exact (hl'.1 u2 hu2))
    exact T2.congr (fun u1 => by
      simp only [List.mem_cons]
      tauto)

/-- The invariant of `spliceFold` for a pairwise disjoint list. -/
noncomputable def spliceFoldInv (G0 : Garden w) (l : List (CLBlock G0))
    (hl : l.Pairwise (fun u u' => Disjoint u.atoms u'.atoms)) : FoldInv (fun u => u ∈ l) (spliceFold G0 l) :=
  (FoldInv.fold l hl _ _ (FoldInv.init G0) (fun u _ u1 h => h.elim)).congr (fun u1 => by simp)

end WaveTurbulence.VineB
