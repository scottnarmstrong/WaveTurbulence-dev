/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceDartTags
/-! Leaves not represented by an LP dart survive every actual CL splice.
This accounts for marked leaves and leaves paired to trivial roots. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- The actual full-leaf trace preserves exactly the LP typing predicate. -/
theorem SpliceLeafTrace.lp_profile {st : SpState G} (T : SpliceLeafTrace st) (l : GLeaf st.G.tree) :
    (st.G.mark l = none ∧ l.1.2 ≠ [] ∧ (st.G.pair l).1.2 ≠ []) ↔
      (G.mark (T.leaf l) = none ∧ (T.leaf l).1.2 ≠ [] ∧ (G.pair (T.leaf l)).1.2 ≠ []) := by
  constructor
  · intro h; exact (T.lp ⟨l, h⟩).2
  · rintro ⟨hm, hn, hp⟩
    refine ⟨(T.mark l).trans hm, fun h => hn ((T.root l).mpr h), ?_⟩
    intro h
    apply hp
    rw [← T.pair]
    exact (T.root (st.G.pair l)).mpr h

/-- A non-LP original leaf already present in a state survives the next actual splice. -/
theorem SpliceLeafTrace.nonLP_add_range {st : SpState G} (T : SpliceLeafTrace st)
    (u : CLBlock G) (hU : ∀ v ∈ u.atoms, st.cls v = none) (q : GLeaf G.tree)
    (hq : ¬ (G.mark q = none ∧ q.1.2 ≠ [] ∧ (G.pair q).1.2 ≠ []))
    (hcur : ∃ l, T.leaf l = q) : ∃ l, (T.add u hU).leaf l = q := by
  obtain ⟨l, hl⟩ := hcur
  let h := SpMap.pb_block st.M st.hcls hU u.isBlock u.cl
  let h2 := h.choose_spec
  let h3 := h2.choose_spec
  let hB := h3.2.2.1
  let hCL := h3.2.2.2
  let D := clSpliceSlotsOfBlock hB hCL
  let E := clSplicedLeafNameEquiv hB hCL D
  have hn : ¬ IsInternalLeaf st.G (st.M.pb u.atoms) l := by
    rintro ⟨hm, hn, hp, _⟩
    apply hq
    rw [← hl]
    exact (T.lp_profile l).mp ⟨hm, hn, hp⟩
  have hr : IsSpliceRetainedLeaf (clSpliceBoundary hB hCL D) l :=
    (clSignedBoundary_retained_iff hB hCL D.excluded D.kept D.excluded_missing
      D.excluded_ne_middle D.kept_ne_middle D.upper D.lower l).mpr hn
  refine ⟨E.symm ⟨l, hr⟩, ?_⟩
  change T.leaf (E (E.symm ⟨l, hr⟩)).1 = q
  rw [E.apply_symm_apply]
  exact hl

/-- A range witness transports with its actual splice state. -/
theorem SpliceLeafTrace.range_transport {st st' : SpState G} (T : SpliceLeafTrace st)
    (h : st = st') (q : GLeaf G.tree) (hr : ∃ l, T.leaf l = q) :
    ∃ l, ((h ▸ T) : SpliceLeafTrace st').leaf l = q := by
  cases h
  exact hr

/-- A non-LP leaf survives both branches of the actual fold step. -/
theorem SpliceLeafTrace.nonLP_step_range {st : SpState G} (T : SpliceLeafTrace st)
    (u : CLBlock G) (q : GLeaf G.tree)
    (hq : ¬ (G.mark q = none ∧ q.1.2 ≠ [] ∧ (G.pair q).1.2 ≠ []))
    (hcur : ∃ l, T.leaf l = q) : ∃ l, (T.step u).leaf l = q := by
  classical
  unfold SpliceLeafTrace.step
  split_ifs with h
  · exact (T.add u h).range_transport _ q (T.nonLP_add_range u h q hq hcur)
  · exact T.range_transport _ q hcur

/-- Every actual finite sequence retains each original non-LP leaf. -/
theorem SpliceLeafTrace.nonLP_fold_range (l : List (CLBlock G)) (st : SpState G) (T : SpliceLeafTrace st)
    (q : GLeaf G.tree) (hq : ¬ (G.mark q = none ∧ q.1.2 ≠ [] ∧ (G.pair q).1.2 ≠ []))
    (hcur : ∃ l, T.leaf l = q) : ∃ q', (T.fold l st).leaf q' = q := by
  induction l generalizing st with
  | nil => exact hcur
  | cons u l ih => exact ih (spliceStep st u) (T.step u) (T.nonLP_step_range u q hq hcur)

/-- All original non-LP leaves occur among the actual spliceFold leaves. -/
theorem spliceFold_nonLP_range (l : List (CLBlock G)) (q : GLeaf G.tree)
    (hq : ¬ (G.mark q = none ∧ q.1.2 ≠ [] ∧ (G.pair q).1.2 ≠ [])) :
    ∃ q', (spliceFoldLeafTrace l).leaf q' = q :=
  SpliceLeafTrace.nonLP_fold_range l (SpState.init G) (spliceLeafTrace_init G) q hq ⟨q, rfl⟩

end WaveTurbulence.VineA
