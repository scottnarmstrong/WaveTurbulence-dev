/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.TimeDomain
public import WaveTurbulence.Foundations.Stage1.Represents.RepNV1
import Mathlib.Tactic

/-!
# VINE-B: regional and outer slots, and the routing of the outer frequencies

The replacement slots of the skeleton (TARGET (redkg): a regular couple at every leaf pair, a regular tree at every
branch) split into the regional slots of the units (the couples at the internal leaf pairs of `G_sk[U_j]` and the trees
at `U_j \ {u1^j}`, V5's `clRegionalPairs` / `clInteriorBranches`) and the outer slots.  The clock sources of an outer
slot are root times, retained branches, or a lower joint `u2^j` (finding F-LOWCLOCK, RULINGS R58: the slots at the
lower boundary children `u21^j, u22^j` read `t_{u2^j}`).  For per-mode outer factors `e^{πi(m_0 t + m_1 s)}`
(INTERFACE v2, PLAN-VINE.md) the total frequency at `u2^j` is the unit modulation `λ_j`, and no other interior clock
of a unit carries a frequency (`prod_outer_modes`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

variable (blk) in
/-- The regional slots of unit `j`. -/
noncomputable def regSlots (hS : S.IsPlain) (j : J) : Finset (ReplacementSlot S) :=
  (clRegionalPairs hS (blk j).atoms).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (inter blk j).map ⟨Sum.inr, Sum.inr_injective⟩

variable (blk) in
/-- The outer slots. -/
noncomputable def outerSlots (hS : S.IsPlain) : Finset (ReplacementSlot S) := by
  classical
  exact univ.filter fun s => ∀ j, s ∉ regSlots blk hS j

theorem mem_regSlots_inl (hS : S.IsPlain) (j : J) (p : SourcePair S) :
    Sum.inl p ∈ regSlots blk hS j ↔ Mole.IsInternalLeaf S (blk j).atoms (p.firstLeaf hS) := by
  unfold regSlots clRegionalPairs
  simp

theorem mem_regSlots_inr (hS : S.IsPlain) (j : J) (v : GBranch S.tree) :
    Sum.inr v ∈ regSlots blk hS j ↔ v ∈ inter blk j := by
  unfold regSlots
  simp

theorem regSlots_disjoint (hS : S.IsPlain) (hd : Disj blk) {j k : J} (hjk : j ≠ k) :
    Disjoint (regSlots blk hS j) (regSlots blk hS k) := by
  rw [Finset.disjoint_left]
  rintro (p | v) h1 h2
  · rw [mem_regSlots_inl] at h1 h2
    have r1 := (leaf_mem_clRealizationNodes _).mpr h1
    have r2 := (leaf_mem_clRealizationNodes _).mpr h2
    exact real_disjoint (hd j k hjk) r1 r2 (fun h => Mole.branch_toNode_ne_leaf _ _ h.symm)
  · rw [mem_regSlots_inr, mem_inter] at h1 h2
    exact Finset.disjoint_left.mp (hd j k hjk) h1.1 h2.1

theorem prod_slots (hS : S.IsPlain) (hd : Disj blk) {M : Type*} [CommMonoid M] (f : ReplacementSlot S → M) :
    ∏ s, f s = (∏ s ∈ outerSlots blk hS, f s) * ∏ j, ∏ s ∈ regSlots blk hS j, f s := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun s => ∀ j, s ∉ regSlots blk hS j)]
  unfold outerSlots
  congr 1
  rw [← Finset.prod_biUnion (fun j _ k _ hjk => regSlots_disjoint hS hd hjk)]
  congr 1
  ext s
  simp

theorem prod_regSlots (hS : S.IsPlain) (j : J) {M : Type*} [CommMonoid M] (f : ReplacementSlot S → M) :
    ∏ s ∈ regSlots blk hS j, f s =
      (∏ p ∈ clRegionalPairs hS (blk j).atoms, f (Sum.inl p)) * ∏ v ∈ inter blk j, f (Sum.inr v) := by
  unfold regSlots
  rw [Finset.prod_union]
  · simp
  · rw [Finset.disjoint_left]
    simp

/-! ## Outer slots -/

theorem second_internal_iff (hS : S.IsPlain) (U : Finset (GBranch S.tree)) (p : SourcePair S) :
    Mole.IsInternalLeaf S U (p.secondLeaf hS) ↔ Mole.IsInternalLeaf S U (p.firstLeaf hS) := by
  have h : S.pair (p.firstLeaf hS) = p.secondLeaf hS := sourcePair_partner S _ _ (Or.inl p.2)
  rw [← h]
  exact Mole.internal_leaf_pair_iff S U _

/-- The leaves of an outer pair slot are not in any realization. -/
theorem outer_pair_not_real (hS : S.IsPlain) {p : SourcePair S} (hs : Sum.inl p ∈ outerSlots blk hS) (j : J) :
    (p.firstLeaf hS).toNode ∉ clRealizationNodes S (blk j).atoms ∧
      (p.secondLeaf hS).toNode ∉ clRealizationNodes S (blk j).atoms := by
  classical
  have hs' := (Finset.mem_filter.mp hs).2 j
  rw [mem_regSlots_inl] at hs'
  refine ⟨fun h => hs' ((leaf_mem_clRealizationNodes _).mp h), fun h => hs' ?_⟩
  exact (second_internal_iff hS _ p).mp ((leaf_mem_clRealizationNodes _).mp h)

/-- The branch of an outer tree slot is not interior to any unit. -/
theorem outer_branch_not_inter (hS : S.IsPlain) {c : GBranch S.tree} (hs : Sum.inr c ∈ outerSlots blk hS)
    (j : J) : c ∉ inter blk j := by
  classical
  have hs' := (Finset.mem_filter.mp hs).2 j
  rwa [mem_regSlots_inr] at hs'

theorem ret_slotNode (hS : S.IsPlain) {s : ReplacementSlot S} (hs : s ∈ outerSlots blk hS) :
    Ret blk (slotNode hS s) := by
  intro j
  rcases s with p | c
  · exact Or.inl (outer_pair_not_real hS hs j).1
  · have h := outer_branch_not_inter hS hs j
    by_cases hc : c ∈ (blk j).atoms
    · right
      have : c = (blk j).upper := by
        by_contra hne; exact h (mem_inter.mpr ⟨hc, hne⟩)
      show c.toNode = _
      rw [this]
    · exact Or.inl (fun h' => hc ((branch_real_iff _ _).mp h'))

theorem clkOfNode_nonroot (x : GNode S.tree) (hn : x.1.2 ≠ []) : clkOfNode S x = Sum.inr (x.parent hn) := by
  unfold clkOfNode
  rw [nodeToSlot, dite_eq_right hn]

/-! ## Routing the outer frequencies -/

end WaveTurbulence.VineB
