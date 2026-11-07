/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.TimeEquiv
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
import Mathlib.Tactic

/-!
# VINE-B: splitting the time domain of the skeleton

`dom_iff`: the glued times lie in the skeleton domain `coreTimeDomainW` (TARGET (timegarden), F-TT root truncation
R33) iff the `G_sb` times lie in the open spliced domain `openSb` and, for every unit, its interior times lie in V5's
local domain `clLocalTimeDomain` at the exterior clocks `(t_{u1}, t_{u21}, t_{u22})`.  The constraint
`t_{u21} < t_{u2}` of a lower boundary child is a constraint of the local domain; the constraint `t_{u21} < t_{u1}`
of `G_sb` and the root truncation follow from the parent order.  `openSb` differs from the closed
`splicedTimeDomain` (TARGET L1969–L1971) on a null set (`indicator_openSb_ae`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset MeasureTheory WaveTurbulence.LGSpine
  WaveTurbulence.RegRedLeaf

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

/-- The open spliced time domain. -/
def openSb (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ) : Set (GBranch G.tree → ℝ) :=
  {τ | (∀ c, (layer c : ℝ) < τ c ∧ τ c < layer c + 1) ∧ (∀ v u, v.IsChildOf u → τ v < τ u) ∧
    ∀ v, τ v < tt v.1.1}

theorem openSb_subset (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ) :
    openSb G layer tt ⊆ splicedTimeDomain G layer tt := fun τ h =>
  ⟨fun c => ⟨(h.1 c).1.le, (h.1 c).2.le⟩, h.2.1, h.2.2⟩

theorem measurableSet_openSb (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ) :
    MeasurableSet (openSb G layer tt) := by
  have h1 : ∀ c, MeasurableSet {τ : GBranch G.tree → ℝ | (layer c : ℝ) < τ c ∧ τ c < layer c + 1} := fun c =>
    (measurableSet_lt measurable_const (measurable_pi_apply c)).inter
      (measurableSet_lt (measurable_pi_apply c) measurable_const)
  have h2 : ∀ v u, MeasurableSet {τ : GBranch G.tree → ℝ | v.IsChildOf u → τ v < τ u} := by
    intro v u
    by_cases h : v.IsChildOf u
    · simpa [h] using measurableSet_lt (measurable_pi_apply v) (measurable_pi_apply u)
    · simp [h]
  have h3 : ∀ v, MeasurableSet {τ : GBranch G.tree → ℝ | τ v < tt v.1.1} := fun v =>
    measurableSet_lt (measurable_pi_apply v) measurable_const
  have he : openSb G layer tt = (⋂ c, {τ : GBranch G.tree → ℝ | (layer c : ℝ) < τ c ∧ τ c < layer c + 1}) ∩
      ((⋂ v, ⋂ u, {τ : GBranch G.tree → ℝ | v.IsChildOf u → τ v < τ u}) ∩
        ⋂ v, {τ : GBranch G.tree → ℝ | τ v < tt v.1.1}) := by
    ext τ
    simp only [openSb, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  exact (MeasurableSet.iInter h1).inter ((MeasurableSet.iInter fun v => MeasurableSet.iInter (h2 v)).inter
    (MeasurableSet.iInter h3))

/-- The closed and open spliced domains differ by a null set. -/
theorem indicator_openSb_ae (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ) {E : Type*} [Zero E]
    (f : (GBranch G.tree → ℝ) → E) :
    (splicedTimeDomain G layer tt).indicator f =ᵐ[volume] (openSb G layer tt).indicator f := by
  have hN : (volume : Measure (GBranch G.tree → ℝ))
      (⋃ c, (Function.eval c ⁻¹' {(layer c : ℝ)} ∪ Function.eval c ⁻¹' {(layer c : ℝ) + 1})) = 0 := by
    refine measure_iUnion_null fun c => measure_union_null ?_ ?_
    · exact Measure.pi_eval_preimage_null _ (Real.volume_singleton)
    · exact Measure.pi_eval_preimage_null _ (Real.volume_singleton)
  refine (measure_eq_zero_iff_ae_notMem.1 hN).mono fun τ hτ => ?_
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_preimage, Function.eval, Set.mem_singleton_iff,
    not_exists, not_or] at hτ
  by_cases h : τ ∈ splicedTimeDomain G layer tt
  · have ho : τ ∈ openSb G layer tt := ⟨fun c => ⟨lt_of_le_of_ne (h.1 c).1 (Ne.symm (hτ c).1),
      lt_of_le_of_ne (h.1 c).2 (hτ c).2⟩, h.2.1, h.2.2⟩
    rw [Set.indicator_of_mem h, Set.indicator_of_mem ho]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun ho => h (openSb_subset G layer tt ho))]

theorem exists_child_isDesc {x : GNode S.tree} (a : GBranch S.tree) (h : a.toNode.IsDesc x) (hne : a.toNode ≠ x) :
    ∃ i, (a.child i).IsDesc x := by
  obtain ⟨h1, r, hr⟩ := h
  cases r with
  | nil =>
    exfalso; apply hne
    exact Subtype.ext (Prod.ext h1 (by simpa using hr))
  | cons i r =>
    refine ⟨i, h1, r, ?_⟩
    rw [← hr]
    show a.1.2 ++ [i] ++ r = a.1.2 ++ i :: r
    simp

theorem root_eq (x : GNode S.tree) (h : x.1.2 = []) : x = GNode.root S.tree x.1.1 :=
  Subtype.ext (Prod.ext rfl h)

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- **The domain split** (TARGET (timegarden), (redvine) L1954–L1957). -/
theorem dom_iff (hd : Disj blk) (layer : GBranch S.tree → ℕ) (tt : Fin w → ℝ) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) :
    Φ.glueTime hd τ' τs ∈ coreTimeDomainW layer tt ↔
      τ' ∈ openSb Gsb (fun c => layer (Φ.br c)) tt ∧
        ∀ j, τs j ∈ clLocalTimeDomain (regionOf (blk j)) layer (Φ.clocks τ' j) := by
  set τ := Φ.glueTime hd τ' τs with hτdef
  have H1 : ∀ c, τ (Φ.br c) = τ' c := Φ.glueTime_br hd τ' τs
  have H2 : ∀ j (x : ↥(inter blk j)), τ x.1 = τs j x := Φ.glueTime_inter hd τ' τs
  have H3 : ∀ j v, v ∈ (blk j).atoms → clLocalClock (regionOf (blk j)) (Φ.clocks τ' j) (τs j) v = τ v :=
    fun j v hv => Φ.clLocalClock_glue hd τ' τs j hv
  have H5 : ∀ j (x : GNode S.tree), x ∈ clRealizationNodes S (blk j).atoms → x ≠ (blk j).upper.toNode →
      parentClock (Φ.clocks τ' j 0) (clLocalClock (regionOf (blk j)) (Φ.clocks τ' j) (τs j)) x =
        parentClockWith tt τ x := by
    intro j x hx hne
    obtain ⟨hn, hp⟩ := real_parent (blk j) hx hne
    rw [parentClock_nonroot _ _ x hn, parentClockWith_nonroot _ _ x hn, H3 j _ hp]
  have H6 : ∀ j (i : Fin 3) (p : GBranch S.tree), p.toNode = (blk j).lower.child i →
      clExternalTimes (regionOf (blk j)) (Φ.extTime τ') 1 = clBranchClock (Φ.extTime τ') ((blk j).lower.child
        (regionOf (blk j)).positive) := fun _ _ _ _ => rfl
  -- the parent clock of a retained branch, by the position of its `G_sb` parent
  have hpar : ∀ c u (i : Fin 3), c.toNode = u.child i →
      (∀ j, Φ.br u ≠ (blk j).upper) ∧ parentClockWith tt τ (Φ.br c).toNode = τ' u ∨
      ∃ j, Φ.br u = (blk j).upper ∧ ((Φ.br c).toNode = (blk j).upper.child (regionOf (blk j)).excluded ∧
          parentClockWith tt τ (Φ.br c).toNode = τ' u ∨
        ((Φ.br c).toNode = (blk j).lower.child (regionOf (blk j)).positive ∨
          (Φ.br c).toNode = (blk j).lower.child (regionOf (blk j)).negative) ∧
          parentClockWith tt τ (Φ.br c).toNode = τ (blk j).lower) := by
    intro c u i hc
    rcases Φ.node_child_parent u i with ⟨hh, -⟩ | ⟨j, hj, hcr⟩
    · left
      refine ⟨hh, ?_⟩
      rw [Φ.br_node, hc, Φ.child u i hh, parentClockWith_child, H1]
    · right
      refine ⟨j, hj, ?_⟩
      rw [← hc, ← Φ.br_node] at hcr
      rcases hcr with h | h | h
      · left; refine ⟨h, ?_⟩; rw [h, parentClockWith_child, ← hj, H1]
      · right; refine ⟨Or.inl h, ?_⟩; rw [h, parentClockWith_child]
      · right; refine ⟨Or.inr h, ?_⟩; rw [h, parentClockWith_child]
  constructor
  · intro hcore
    have hlow : ∀ j, τ (blk j).lower < τ (blk j).upper := by
      intro j
      have hne : (blk j).upper.toNode ≠ (blk j).lower.toNode := fun h =>
        (blk j).isBlock.2.2.2.1 (Subtype.ext (congrArg (fun x : GNode S.tree => x.1) h))
      obtain ⟨i, hi⟩ := exists_child_isDesc (blk j).upper (lower_desc (blk j)) hne
      have := branchTime_lt_parentClockWith_of_desc tt τ (fun b => (hcore b).2.2.2) _ _ hi
      rwa [parentClockWith_child] at this
    refine ⟨⟨fun c => ?_, fun c u hcu => ?_, fun c => ?_⟩, fun j => ⟨fun v => ?_, fun hb => ?_, fun hb => ?_⟩⟩
    · rw [← H1]; exact ⟨(hcore _).1, (hcore _).2.1⟩
    · obtain ⟨h1, i, h2⟩ := hcu
      have hc : c.toNode = u.child i := Subtype.ext (Prod.ext h1 h2)
      have hlt := (hcore (Φ.br c)).2.2.2
      rw [H1] at hlt
      rcases hpar c u i hc with ⟨-, h⟩ | ⟨j, hj, ⟨-, h⟩ | ⟨-, h⟩⟩
      · rwa [h] at hlt
      · rwa [h] at hlt
      · rw [h] at hlt
        have := hlow j
        rw [← hj, H1] at this
        linarith
    · have := lt_rootTop_of_lt_parentClockWith tt τ (fun b => (hcore b).2.2.2) (Φ.br c)
      rw [H1] at this
      have ht : (Φ.br c).1.1 = c.1.1 := by
        have := Φ.tree_eq c.toNode
        rw [← Φ.br_node] at this
        exact this
      rwa [ht] at this
    · have hv := mem_inter.mp v.2
      have h := hcore v.1
      rw [H2 j v] at h
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      rw [H5 j _ ((branch_real_iff _ _).mpr hv.1) (fun he => hv.2 (Subtype.ext
        (congrArg (fun x : GNode S.tree => x.1) he)))]
      exact h.2.2.2
    · rw [H3 j _ (lower_mem _)]
      have hr : Ret blk (GBranch.toNode (⟨_, hb⟩ : GBranch S.tree)) := ret_crown hd j (Or.inr (Or.inl rfl))
      show clBranchClock (Φ.extTime τ') _ < _
      unfold clBranchClock
      rw [dif_pos hb, ← Φ.glueTime_ret hd τ' τs hr]
      have := (hcore ⟨_, hb⟩).2.2.2
      exact this.trans_eq (parentClockWith_child _ _ _ _)
    · rw [H3 j _ (lower_mem _)]
      have hr : Ret blk (GBranch.toNode (⟨_, hb⟩ : GBranch S.tree)) := ret_crown hd j (Or.inr (Or.inr rfl))
      show clBranchClock (Φ.extTime τ') _ < _
      unfold clBranchClock
      rw [dif_pos hb, ← Φ.glueTime_ret hd τ' τs hr]
      have := (hcore ⟨_, hb⟩).2.2.2
      exact this.trans_eq (parentClockWith_child _ _ _ _)
  · rintro ⟨hsb, hloc⟩ v
    rcases ret_or_interior (blk := blk) v.toNode with hr | ⟨j, h1, h2⟩
    · obtain ⟨c, rfl⟩ := Φ.exists_br hr
      rw [H1]
      have hL0 : (0 : ℝ) ≤ layer (Φ.br c) := Nat.cast_nonneg _
      refine ⟨(hsb.1 c).1, (hsb.1 c).2, by linarith [(hsb.1 c).1], ?_⟩
      by_cases hn : c.1.2 = []
      · have hn' : (Φ.br c).toNode.1.2 = [] := by rw [Φ.br_node]; exact (Φ.root_iff _).mpr hn
        rw [root_eq _ hn', parentClockWith_root]
        have ht : (Φ.br c).toNode.1.1 = c.1.1 := by rw [Φ.br_node]; exact Φ.tree_eq c.toNode
        rw [ht]
        exact hsb.2.2 c
      · obtain ⟨i, hi⟩ := child_parent c.toNode hn
        set u := c.toNode.parent hn
        have hcu : c.IsChildOf u := ⟨congrArg (fun x : GNode Gsb.tree => x.1.1) hi.symm,
          i, congrArg (fun x : GNode Gsb.tree => x.1.2) hi.symm⟩
        have hlt := hsb.2.1 c u hcu
        rcases hpar c u i hi.symm with ⟨-, h⟩ | ⟨j, hj, ⟨-, h⟩ | ⟨hb, h⟩⟩
        · rwa [h]
        · rwa [h]
        · rw [h, ← H3 j _ (lower_mem _)]
          rcases hb with hb | hb
          · have := (hloc j).2.1 (by rw [← hb]; exact (Φ.br c).2)
            have he : Φ.clocks τ' j 1 = τ' c := by
              show clBranchClock (Φ.extTime τ') _ = _
              unfold clBranchClock
              have hb' : (blk j).lower.child (regionOf (blk j)).positive = (Φ.br c).toNode := hb.symm
              rw [dif_pos (by rw [hb']; exact (Φ.br c).2)]
              have : (⟨((blk j).lower.child (regionOf (blk j)).positive).1, by rw [hb']; exact (Φ.br c).2⟩ :
                GBranch S.tree) = Φ.br c := Subtype.ext (congrArg (fun x : GNode S.tree => x.1) hb')
              rw [this, Φ.extTime_br]
            rwa [he] at this
          · have := (hloc j).2.2 (by rw [← hb]; exact (Φ.br c).2)
            have he : Φ.clocks τ' j 2 = τ' c := by
              show clBranchClock (Φ.extTime τ') _ = _
              unfold clBranchClock
              have hb' : (blk j).lower.child (regionOf (blk j)).negative = (Φ.br c).toNode := hb.symm
              rw [dif_pos (by rw [hb']; exact (Φ.br c).2)]
              have : (⟨((blk j).lower.child (regionOf (blk j)).negative).1, by rw [hb']; exact (Φ.br c).2⟩ :
                GBranch S.tree) = Φ.br c := Subtype.ext (congrArg (fun x : GNode S.tree => x.1) hb')
              rw [this, Φ.extTime_br]
            rwa [he] at this
    · have hv : v ∈ (blk j).atoms := (branch_real_iff _ _).mp h1
      have hm : v ∈ inter blk j := mem_inter.mpr ⟨hv, fun he => h2 (by rw [he])⟩
      have h := (hloc j).1 ⟨v, hm⟩
      rw [H5 j _ h1 h2] at h
      rw [H2 j ⟨v, hm⟩]
      exact h

end SpliceShape

end WaveTurbulence.VineB
