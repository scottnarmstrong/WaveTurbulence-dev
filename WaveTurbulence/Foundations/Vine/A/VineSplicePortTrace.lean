/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSplicePortSingle
public import WaveTurbulence.Foundations.Vine.A.VineSpliceLeaves
/-! Retained-parent ports through the actual splice fold. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.RedSplice.SpMap
variable {w : ℕ} {G : Garden w}

/-- An old parent retained after an additional disjoint splice was retained before it. -/
theorem repC_fixed_before_add {st : SpState G} (u : CLBlock G)
    (hU : ∀ v ∈ u.atoms, st.cls v = none) (v : GBranch G.tree)
    (hv : repC (clsAdd st.cls u.atoms u.upper) v = v) : repC st.cls v = v := by
  classical
  by_cases hm : v ∈ u.atoms
  · unfold repC
    rw [hU v hm]
    rfl
  · simpa only [repC_clsAdd, hm, ↓reduceIte] using hv

/-- A retained old parent pulls back outside the new block or to its upper joint. -/
theorem parent_kept_pullback {st : SpState G} (u : CLBlock G)
    (a : GBranch st.G.tree) (ha : st.M.ob a = u.upper)
    (p : GBranch st.G.tree) (v : GBranch G.tree) (hp : st.M.ob p = v)
    (hv : repC (clsAdd st.cls u.atoms u.upper) v = v) :
    p ∉ st.M.pb u.atoms ∨ p = a := by
  classical
  by_cases hm : v ∈ u.atoms
  · right
    apply st.M.ob_inj
    rw [hp, ha]
    have he : u.upper = v := by simpa only [repC_clsAdd, hm, ↓reduceIte] using hv
    exact he.symm
  · left
    intro h
    exact hm (hp ▸ (SpMap.mem_pb st.M).mp h)

/-- The literal old-name trace retains each port whose original parent survives. -/
structure SplicePortTrace {st : SpState G} (T : SpliceLeafTrace st) : Prop where
  branch : ∀ (c : GBranch st.G.tree) (hn : c.1.2 ≠ []) (ho : (st.M.ob c).1.2 ≠ []),
    repC st.cls (GNode.parent (st.M.ob c).toNode ho) = GNode.parent (st.M.ob c).toNode ho →
    c.1.2.getLast hn = (st.M.ob c).1.2.getLast ho
  leaf : ∀ (l : GLeaf st.G.tree) (hn : l.1.2 ≠ []) (ho : (T.leaf l).1.2 ≠ []),
    repC st.cls (GNode.parent (T.leaf l).toNode ho) = GNode.parent (T.leaf l).toNode ho →
    l.1.2.getLast hn = (T.leaf l).1.2.getLast ho

/-- The empty fold has literal ports. -/
theorem splicePortTrace_init (G : Garden w) : SplicePortTrace (spliceLeafTrace_init G) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- An actual CL step preserves the retained-parent port invariant. -/
theorem SplicePortTrace.add {st : SpState G} {T : SpliceLeafTrace st} (H : SplicePortTrace T)
    (u : CLBlock G) (hU : ∀ v ∈ u.atoms, st.cls v = none) : SplicePortTrace (T.add u hU) := by
  let h := SpMap.pb_block st.M st.hcls hU u.isBlock u.cl
  let h2 := h.choose_spec
  let h3 := h2.choose_spec
  let hB := h3.2.2.1
  let hCL := h3.2.2.2
  let D := clSpliceSlotsOfBlock hB hCL
  constructor
  · intro c hn ho hv
    let c' := stepB hB hCL D c
    have hn' : c'.1.2 ≠ [] := fun he => hn ((clSplicedBranchName_root_iff hB hCL D c).mp he)
    change repC (clsAdd st.cls u.atoms u.upper) (GNode.parent (st.M.ob c').toNode ho) = _ at hv
    have hf := repC_fixed_before_add u hU _ hv
    have hp := (st.M.ob_parent c' hn' ho).trans hf
    exact (cl_branch_port_of_parent_kept hB hCL D c hn hn'
      (parent_kept_pullback u _ h3.1 _ _ hp hv)).trans (H.branch c' hn' ho hf)
  · intro l hn ho hv
    let l' := (clSplicedLeafNameEquiv hB hCL D l).1
    have hn' : l'.1.2 ≠ [] := fun he => hn ((clSplicedLeafName_root_iff hB hCL D l).mp he)
    change repC (clsAdd st.cls u.atoms u.upper) (GNode.parent (T.leaf l').toNode ho) = _ at hv
    have hf := repC_fixed_before_add u hU _ hv
    have hp := (T.parent l' hn' ho).trans hf
    exact (cl_leaf_port_of_parent_kept hB hCL D l hn hn'
      (parent_kept_pullback u _ h3.1 _ _ hp hv)).trans (H.leaf l' hn' ho hf)

/-- Literal state transport carries the proved port invariant. -/
theorem SplicePortTrace.transport {st st' : SpState G} {T : SpliceLeafTrace st}
    (H : SplicePortTrace T) (h : st = st') : SplicePortTrace (h ▸ T) := by
  cases h
  exact H

/-- Both branches of the actual fold step preserve retained-parent ports. -/
theorem SplicePortTrace.step {st : SpState G} {T : SpliceLeafTrace st} (H : SplicePortTrace T)
    (u : CLBlock G) : SplicePortTrace (T.step u) := by
  classical
  unfold SpliceLeafTrace.step
  split_ifs with h
  · exact (H.add u h).transport _
  · exact H.transport _

/-- Induction on the actual splice fold preserves retained-parent ports. -/
theorem SplicePortTrace.fold (l : List (CLBlock G)) (st : SpState G) (T : SpliceLeafTrace st)
    (H : SplicePortTrace T) : SplicePortTrace (T.fold l st) := by
  induction l generalizing st with
  | nil => exact H
  | cons u l ih => exact ih (spliceStep st u) (T.step u) (H.step u)

/-- Ports of retained-parent edges for the actual finite splice sequence. -/
theorem spliceFoldPortTrace (l : List (CLBlock G)) : SplicePortTrace (spliceFoldLeafTrace l) :=
  SplicePortTrace.fold l (SpState.init G) (spliceLeafTrace_init G) (splicePortTrace_init G)

end WaveTurbulence.VineA
