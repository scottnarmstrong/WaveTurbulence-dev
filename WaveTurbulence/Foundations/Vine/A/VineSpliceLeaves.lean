/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceQuotient
public import WaveTurbulence.Foundations.Molecule.CLLeafNames
import WaveTurbulence.Foundations.Molecule.CLIncidenceParents
/-! Actual iterated splices retain injective original leaf names, pairing,
marks and signs. These data include trivial-root leaves absent from the molecule. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.RedSplice.SpMap
variable {w : ℕ} {G : Garden w}

/-- Trivial-root leaf addresses are unchanged by an actual CL splice. -/
theorem clSplicedLeafName_root_address {H : Garden w} {S : Finset (GBranch H.tree)}
    {a b : GBranch H.tree} (hB : H.molecule.IsBlock S a b) (hCL : CLParentPattern H S a b)
    (D : CLSpliceSlots H S a b) (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree)
    (hl : l.1.2 = []) : (clSplicedLeafNameEquiv hB hCL D l).1.1 = l.1 := by
  obtain ⟨p, rfl⟩ := splicePieceNew_surjective (clSpliceBoundary hB hCL D) l
  change (spliceLeafEquiv (clSpliceBoundary hB hCL D)
    (splicePieceNew (clSpliceBoundary hB hCL D) p)).1.1 = _
  rw [spliceLeafEquiv_piece]
  cases p with
  | inl l => rfl
  | inr p =>
    exact ((List.append_ne_nil_of_right_ne_nil a.1.2 (List.cons_ne_nil p.1 p.2.1)) hl).elim

/-- The actual old parent of a retained leaf contracts to its new parent. -/
theorem stepB_leaf_parent {H : Garden w} {S : Finset (GBranch H.tree)}
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

/-- Actual old leaf names carried by an intermediate splice state. -/
structure SpliceLeafTrace (st : SpState G) where
  leaf : GLeaf st.G.tree → GLeaf G.tree
  injective : Function.Injective leaf
  pair : ∀ l, leaf (st.G.pair l) = G.pair (leaf l)
  mark : ∀ l, st.G.mark l = G.mark (leaf l)
  root : ∀ l, (leaf l).1.2 = [] ↔ l.1.2 = []
  root_address : ∀ l, l.1.2 = [] → (leaf l).1 = l.1
  parent : ∀ (l : GLeaf st.G.tree) (hn : l.1.2 ≠ []) (ho : (leaf l).1.2 ≠ []),
    st.M.ob (GNode.parent l.toNode hn) = repC st.cls (GNode.parent (leaf l).toNode ho)
  sign : ∀ l, st.G.sign l.toNode = G.sign (leaf l).toNode

/-- The empty splice carries every original leaf literally. -/
def spliceLeafTrace_init (G : Garden w) : SpliceLeafTrace (SpState.init G) where
  leaf := id
  injective := Function.injective_id
  pair _ := rfl
  mark _ := rfl
  root _ := Iff.rfl
  root_address _ _ := rfl
  parent _ _ _ := rfl
  sign _ := rfl

/-- One actual CL splice composes the literal retained-leaf names. -/
noncomputable def SpliceLeafTrace.add {st : SpState G} (T : SpliceLeafTrace st)
    (u : CLBlock G) (hU : ∀ v ∈ u.atoms, st.cls v = none) : SpliceLeafTrace (st.add u hU) := by
  let h := SpMap.pb_block st.M st.hcls hU u.isBlock u.cl
  let h2 := h.choose_spec
  let h3 := h2.choose_spec
  let hB := h3.2.2.1
  let hCL := h3.2.2.2
  let D := clSpliceSlotsOfBlock hB hCL
  let E := clSplicedLeafNameEquiv hB hCL D
  refine {
    leaf := fun l => T.leaf (E l).1
    injective := fun l m he => E.injective (Subtype.ext (T.injective he))
    pair := ?_, mark := ?_, root := ?_, root_address := ?_, parent := ?_, sign := ?_ }
  · intro l
    exact (congrArg T.leaf (clSplicedLeafName_pair hB hCL D l)).trans (T.pair _)
  · intro l
    exact (clSplicedLeafName_mark hB hCL D l).trans (T.mark _)
  · intro l
    exact (T.root _).trans (clSplicedLeafName_root_iff hB hCL D l)
  · intro l hl
    have hold : (E l).1.1.2 = [] := (clSplicedLeafName_root_iff hB hCL D l).mpr hl
    exact (T.root_address _ hold).trans (clSplicedLeafName_root_address hB hCL D l hl)
  · intro l hn ho
    have hn1 : (E l).1.1.2 ≠ [] := fun h => hn ((clSplicedLeafName_root_iff hB hCL D l).mp h)
    change st.M.ob (stepB hB hCL D (GNode.parent l.toNode hn)) =
      repC (clsAdd st.cls u.atoms u.upper) (GNode.parent (T.leaf (E l).1).toNode ho)
    apply (congrArg st.M.ob (stepB_leaf_parent hB hCL D l hn hn1)).trans
    rw [repC_clsAdd]
    have hp := T.parent (E l).1 hn1 ho
    by_cases hx : GNode.parent (T.leaf (E l).1).toNode ho ∈ u.atoms
    · have hc : GNode.parent (E l).1.toNode hn1 ∈ st.M.pb u.atoms :=
        (SpMap.mem_pb st.M).mpr (by rw [hp, SpMap.repC_mem_iff st.hcls hU]; exact hx)
      rw [rep_of_mem hc]
      simp only [hx, ↓reduceIte]
      exact h3.1
    · have hc : GNode.parent (E l).1.toNode hn1 ∉ st.M.pb u.atoms := fun h =>
        hx ((SpMap.repC_mem_iff st.hcls hU).mp (by rw [← hp]; exact (SpMap.mem_pb st.M).mp h))
      rw [rep_of_notMem hc]
      simp only [hx, ↓reduceIte]
      exact hp
  · intro l
    exact (clSplicedLeafName_sign hB hCL D l).trans (T.sign _)

/-- The actual fold step retains the old leaf trace even in the skip branch. -/
noncomputable def SpliceLeafTrace.step {st : SpState G} (T : SpliceLeafTrace st) (u : CLBlock G) :
    SpliceLeafTrace (spliceStep st u) := by
  classical
  exact if h : ∀ v ∈ u.atoms, st.cls v = none then
    (show st.add u h = spliceStep st u from by unfold spliceStep; rw [dite_eq_left h]) ▸ T.add u h
  else
    (show st = spliceStep st u from by unfold spliceStep; rw [dite_eq_right h]) ▸ T

/-- Every finite actual splice sequence has a literal original-leaf trace. -/
noncomputable def SpliceLeafTrace.fold (l : List (CLBlock G)) (st : SpState G) (T : SpliceLeafTrace st) :
    SpliceLeafTrace (l.foldl spliceStep st) := by
  induction l generalizing st with
  | nil => exact T
  | cons u l ih => exact ih (spliceStep st u) (T.step u)

/-- The actual spliceFold garden retains its full original-leaf data. -/
noncomputable def spliceFoldLeafTrace (l : List (CLBlock G)) : SpliceLeafTrace (spliceFold G l) :=
  SpliceLeafTrace.fold l (SpState.init G) (spliceLeafTrace_init G)

end WaveTurbulence.VineA
