/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvGarden
import Mathlib.Tactic

/-!
# How the unit twist moves the ancestor relation

The unit twist moves the subtree `D` below the lower joint `l` to hang below the paired leaf.  The
ancestor relation between two branching nodes is unchanged, except for a pair `(u, u')` with `u`
outside `D` and `u'` in `D`: then `u` is an ancestor of `u'` before iff `u` is an ancestor-or-equal of
the old parent `pO` of `l`, and after iff it is an ancestor-or-equal of the new parent `pN`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.Twist TTree

theorem prefix_dropLast_iff {α : Type*} {l x r : List α} (hl : l ≠ []) (hnot : ¬ l <+: x) :
    x <+: l ++ r ↔ x <+: l.dropLast := by
  constructor
  · intro h
    have h1 : x <+: l := by
      rcases List.prefix_or_prefix_of_prefix h (List.prefix_append l r) with h | h
      · exact h
      · exact absurd h hnot
    rw [← List.dropLast_append_getLast hl] at h1
    rcases List.prefix_concat_iff.mp h1 with h2 | h2
    · exfalso
      apply hnot
      rw [h2, List.dropLast_append_getLast hl]
    · exact h2
  · intro h
    exact (h.trans (List.dropLast_prefix l)).trans (List.prefix_append l r)

theorem switchPath_prefix_iff (keep : Fin 3) {p p' : Path} :
    switchPath keep p <+: switchPath keep p' ↔ p <+: p' := by
  cases p with
  | nil => simp [switchPath]
  | cons i p1 =>
    cases p' with
    | nil => simp [switchPath]
    | cons j p2 =>
      simp only [switchPath, List.cons_prefix_cons]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(freeSwap keep).injective h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨congrArg _ h1, h2⟩

namespace TwistSite
variable {w : ℕ} {G : Garden w} (Z : TwistSite G)

/-- Membership in the subtree below the lower joint. -/
@[expose] def InD (b : GBranch G.tree) : Prop := Z.P.lower.toNode.IsDesc b.toNode

theorem addr_of_InD {b : GBranch G.tree} (hb : Z.InD b) :
    ∃ r, b.1 = (Z.P.lower.1.1, Z.P.lower.1.2 ++ r) ∧
      (coreBranchEquiv G Z.P b).1 = ((G.pair Z.P.retained).1.1,
        (G.pair Z.P.retained).1.2 ++ switchPath Z.P.keep r) := by
  obtain ⟨q, hq⟩ := hb.2
  have hvu : b.1 = (Z.P.lower.1.1, Z.P.lower.1.2 ++ q) := Prod.ext hb.1.symm hq.symm
  refine ⟨q, hvu, ?_⟩
  exact (coreBranchEquiv_address G Z.P b).trans (by rw [hvu]; simp [exchangeAddress])

theorem addr_of_not_InD {b : GBranch G.tree} (hb : ¬ Z.InD b) :
    (coreBranchEquiv G Z.P b).1 = b.1 := coreBranchEquiv_fixed_val G Z.P b hb

/-- The case of two nodes in the moved subtree. -/
theorem desc_iff_InD {u u' : GBranch G.tree} (hu : Z.InD u) (hu' : Z.InD u') :
    u.toNode.IsDesc u'.toNode ↔
      (coreBranchEquiv G Z.P u).toNode.IsDesc (coreBranchEquiv G Z.P u').toNode := by
  obtain ⟨r, hr, hfr⟩ := Z.addr_of_InD hu
  obtain ⟨r', hr', hfr'⟩ := Z.addr_of_InD hu'
  change u.1.1 = u'.1.1 ∧ u.1.2 <+: u'.1.2 ↔
    (coreBranchEquiv G Z.P u).1.1 = (coreBranchEquiv G Z.P u').1.1 ∧
      (coreBranchEquiv G Z.P u).1.2 <+: (coreBranchEquiv G Z.P u').1.2
  rw [hr, hr', hfr, hfr']
  simp only [true_and]
  rw [List.prefix_append_right_inj, List.prefix_append_right_inj, switchPath_prefix_iff]

/-- Moved node against a fixed node: never a descendant relation on either side. -/
theorem desc_iff_InD_not {u u' : GBranch G.tree} (hu : Z.InD u) (hu' : ¬ Z.InD u') :
    ¬ u.toNode.IsDesc u'.toNode ∧
      ¬ (coreBranchEquiv G Z.P u).toNode.IsDesc (coreBranchEquiv G Z.P u').toNode := by
  have hnd : ¬ u.toNode.IsDesc u'.toNode := by
    intro hd
    apply hu'
    exact ⟨hu.1.trans hd.1, hu.2.trans hd.2⟩
  exact ⟨hnd, coreBranchEquiv_not_desc Z.P u u' hu' hnd⟩

/-- A fixed node against a node of the moved subtree: ancestor of the old resp. new parent. -/
theorem desc_iff_fixed_InD {u u' : GBranch G.tree} (hu : ¬ Z.InD u) (hu' : Z.InD u') :
    (u.toNode.IsDesc u'.toNode ↔ u.toNode.IsDesc Z.pO.toNode) ∧
      ((coreBranchEquiv G Z.P u).toNode.IsDesc (coreBranchEquiv G Z.P u').toNode ↔
        u.toNode.IsDesc Z.pN.toNode) := by
  obtain ⟨r', hr', hfr'⟩ := Z.addr_of_InD hu'
  have hfu := Z.addr_of_not_InD hu
  have hnr := Z.P.nonroot
  have hqnr := Z.P.paired_nonroot
  constructor
  · change u.1.1 = u'.1.1 ∧ u.1.2 <+: u'.1.2 ↔ u.1.1 = Z.pO.1.1 ∧ u.1.2 <+: Z.pO.1.2
    rw [hr']
    change u.1.1 = Z.P.lower.1.1 ∧ u.1.2 <+: Z.P.lower.1.2 ++ r' ↔
      u.1.1 = Z.P.lower.1.1 ∧ u.1.2 <+: Z.P.lower.1.2.dropLast
    by_cases ht : u.1.1 = Z.P.lower.1.1
    · have hnot : ¬ Z.P.lower.1.2 <+: u.1.2 := fun h => hu ⟨ht.symm, h⟩
      simp only [ht, true_and]
      exact prefix_dropLast_iff hnr hnot
    · simp [ht]
  · change (coreBranchEquiv G Z.P u).1.1 = (coreBranchEquiv G Z.P u').1.1 ∧
      (coreBranchEquiv G Z.P u).1.2 <+: (coreBranchEquiv G Z.P u').1.2 ↔
      u.1.1 = Z.pN.1.1 ∧ u.1.2 <+: Z.pN.1.2
    rw [hfu, hfr']
    change u.1.1 = (G.pair Z.P.retained).1.1 ∧
      u.1.2 <+: (G.pair Z.P.retained).1.2 ++ switchPath Z.P.keep r' ↔
      u.1.1 = (G.pair Z.P.retained).1.1 ∧ u.1.2 <+: (G.pair Z.P.retained).1.2.dropLast
    by_cases ht : u.1.1 = (G.pair Z.P.retained).1.1
    · have hnot : ¬ (G.pair Z.P.retained).1.2 <+: u.1.2 := by
        intro h
        have hb : u.1.2 ∈ (G.tree (G.pair Z.P.retained).1.1).branching := ht ▸ u.2
        exact leaf_not_prefix_branch (G.pair Z.P.retained).2 hb h
      simp only [ht, true_and]
      exact prefix_dropLast_iff hqnr hnot
    · simp [ht]

/-- **Ancestor relation under the twist** (all four cases), given agreement for the exceptional pair. -/
theorem desc_map_iff {u u' : GBranch G.tree}
    (hag : ¬ Z.InD u → Z.InD u' → (u.toNode.IsDesc Z.pO.toNode ↔ u.toNode.IsDesc Z.pN.toNode)) :
    u.toNode.IsDesc u'.toNode ↔
      (coreBranchEquiv G Z.P u).toNode.IsDesc (coreBranchEquiv G Z.P u').toNode := by
  by_cases hu : Z.InD u <;> by_cases hu' : Z.InD u'
  · exact Z.desc_iff_InD hu hu'
  · obtain ⟨h1, h2⟩ := Z.desc_iff_InD_not hu hu'
    exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
  · obtain ⟨h1, h2⟩ := Z.desc_iff_fixed_InD hu hu'
    rw [h1, h2]
    exact hag hu hu'
  · exact (fixed_branch_desc_iff G Z.P (Z.addr_of_not_InD hu) (Z.addr_of_not_InD hu')).symm

/-- Every branching node strictly between `a0` and an atom of `S0` lies in `S0`. -/
theorem path_in_S0 : ∀ (n : ℕ) (y : GBranch G.tree), y.1.2.length = n → y ∈ Z.S0 →
    ∀ x : GBranch G.tree, Z.a0.toNode.IsDesc x.toNode → x.toNode.IsDesc y.toNode → x ∈ Z.S0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hn hy x hax hxy
    by_cases hxe : x = y
    · subst hxe; exact hy
    have hxy1 : x.1.1 = y.1.1 := hxy.1
    have hxy2 : x.1.2 <+: y.1.2 := hxy.2
    have hlt : x.1.2.length < y.1.2.length := by
      rcases Nat.lt_or_ge x.1.2.length y.1.2.length with h | h
      · exact h
      · exfalso
        apply hxe
        have : x.1.2 = y.1.2 := hxy2.eq_of_length (le_antisymm hxy2.length_le h)
        exact Subtype.ext (Prod.ext hxy1 this)
    have hyroot : y.1.2 ≠ [] := by
      intro h; rw [h] at hlt; simp at hlt
    have hax2 : Z.a0.1.2.length ≤ x.1.2.length := hax.2.length_le
    have hya : y ≠ Z.a0 := by
      intro h; rw [h] at hlt; omega
    have hpar : GNode.parent y.toNode hyroot ∈ Z.S0 := by
      by_cases hyl : y = Z.P.lower
      · subst hyl; exact Z.pO_mem
      · have hdeg : G.molecule.degIn Z.S0 y = 4 := by
          rcases block_degIn_cases Z.hB hy with ⟨hj, _⟩ | ⟨_, h4⟩
          · rcases hj with h | h
            · exact absurd h hya
            · exact absurd h hyl
          · exact h4
        obtain ⟨h, hm⟩ := Mole.full_internal_has_parent G hdeg
        exact hm
    have hpl : (GNode.parent y.toNode hyroot).1.2.length < n := by
      change y.1.2.dropLast.length < n
      rw [List.length_dropLast]; omega
    have hxp : x.toNode.IsDesc (GNode.parent y.toNode hyroot).toNode := by
      change x.1.1 = y.1.1 ∧ x.1.2 <+: y.1.2.dropLast
      refine ⟨hxy1, ?_⟩
      rw [← List.dropLast_append_getLast hyroot] at hxy2
      rcases List.prefix_concat_iff.mp hxy2 with h | h
      · exfalso; apply hxe
        have : x.1.2 = y.1.2 := by rw [h, List.dropLast_append_getLast hyroot]
        exact Subtype.ext (Prod.ext hxy1 this)
      · exact h
    exact ih _ hpl (GNode.parent y.toNode hyroot) rfl hpar x hax hxp

/-- One-sided agreement of ancestry at the old and new parent, for nodes outside `S0` or equal `a0`. -/
theorem anc_imp {u y y' : GBranch G.tree} (hy : y ∈ Z.S0) (hy' : y' ∈ Z.S0)
    (hu : u ∉ Z.S0 ∨ u = Z.a0) (h : u.toNode.IsDesc y.toNode) : u.toNode.IsDesc y'.toNode := by
  have hay : Z.a0.toNode.IsDesc y.toNode :=
    Mole.block_one_root_descendants G Z.hB Z.hCL.1 Z.hCL.2 hy
  have hay' : Z.a0.toNode.IsDesc y'.toNode :=
    Mole.block_one_root_descendants G Z.hB Z.hCL.1 Z.hCL.2 hy'
  change u.1.1 = y.1.1 ∧ u.1.2 <+: y.1.2 at h
  change Z.a0.1.1 = y.1.1 ∧ Z.a0.1.2 <+: y.1.2 at hay
  change Z.a0.1.1 = y'.1.1 ∧ Z.a0.1.2 <+: y'.1.2 at hay'
  rcases List.prefix_or_prefix_of_prefix h.2 hay.2 with hua | hau
  · change u.1.1 = y'.1.1 ∧ u.1.2 <+: y'.1.2
    exact ⟨h.1.trans (hay.1.symm.trans hay'.1), hua.trans hay'.2⟩
  · have hux : Z.a0.toNode.IsDesc u.toNode := ⟨hay.1.trans h.1.symm, hau⟩
    have huS := Z.path_in_S0 _ y rfl hy u hux ⟨h.1, h.2⟩
    rcases hu with hu | hu
    · exact absurd huS hu
    · subst hu; exact hay'

theorem anc_agree {u : GBranch G.tree} (hu : u ∉ Z.S0 ∨ u = Z.a0) :
    u.toNode.IsDesc Z.pO.toNode ↔ u.toNode.IsDesc Z.pN.toNode :=
  ⟨Z.anc_imp Z.pO_mem Z.pN_mem hu, Z.anc_imp Z.pN_mem Z.pO_mem hu⟩

theorem desc_map_iff' {u u' : GBranch G.tree} (hu : u ∉ Z.S0 ∨ u = Z.a0 ∨ Z.InD u) :
    u.toNode.IsDesc u'.toNode ↔
      (coreBranchEquiv G Z.P u).toNode.IsDesc (coreBranchEquiv G Z.P u').toNode := by
  refine Z.desc_map_iff fun hnD _ => Z.anc_agree ?_
  rcases hu with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hnD

end TwistSite
end WaveTurbulence.Stage1
