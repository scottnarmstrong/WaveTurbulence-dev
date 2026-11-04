/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCouple

/-! # External-leaf witnesses and partner-root uniqueness (DH21 Proposition 4.10)

The signed sum rule rules out internally paired whole subtrees. Consequently,
closed sub-couples have genuine cross-root pairs, even when both roots lie in
the same tree. Partner-root uniqueness below is explicitly for incomparable
candidate roots, as required for the off-spine child subtrees.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open Finset
variable {w : ℕ} {G : Garden w}

/-- Property L of DH21 Prop 4.10: a descendant leaf pairs into a different original tree. -/
def HasExternal (G : Garden w) (a : GNode G.tree) : Prop :=
  ∃ ℓ ∈ a.leavesBelow, (G.pair ℓ).1.1 ≠ a.1.1

instance (G : Garden w) (a : GNode G.tree) : Decidable (HasExternal G a) := by
  unfold HasExternal
  infer_instance

/-- Every embedded sub-couple has a leaf pairing across its two rooted subtrees. -/
theorem subCouple_cross_witness {a b : GNode G.tree} (h : Comb.IsSubCouple G a b) :
    ∃ ℓ ∈ a.leavesBelow, G.pair ℓ ∈ b.leavesBelow := by
  by_contra hn
  apply Comb.not_completelyPaired_subtree a
  intro ℓ hℓ
  obtain ⟨hne,hmem⟩ := h ℓ (Finset.mem_union_left _ hℓ)
  refine ⟨hne, ?_⟩
  rcases Finset.mem_union.mp hmem with ha | hb
  · exact ha
  · exact (hn ⟨ℓ,hℓ,hb⟩).elim

/-- Closed roots in different original trees provide property L. -/
theorem hasExternal_of_subCouple {a b : GNode G.tree} (h : Comb.IsSubCouple G a b)
    (hidx : b.1.1 ≠ a.1.1) : HasExternal G a := by
  obtain ⟨ℓ,hℓ,hb⟩ := subCouple_cross_witness h
  refine ⟨ℓ,hℓ,?_⟩
  have hj := (Finset.mem_filter.mp hb).2.1
  exact fun he => hidx (hj.trans he)

/-- Side couples lying in one original tree have no external leaves. -/
theorem not_hasExternal_of_subCouple {a b : GNode G.tree} (h : Comb.IsSubCouple G a b)
    (hidx : b.1.1 = a.1.1) : ¬ HasExternal G a := by
  rintro ⟨ℓ,hℓ,hne⟩
  have hp := (h ℓ (Finset.mem_union_left _ hℓ)).2
  rcases Finset.mem_union.mp hp with ha | hb
  · exact hne (Finset.mem_filter.mp ha).2.1.symm
  · exact hne (((Finset.mem_filter.mp hb).2.1).symm.trans hidx)

/-- The same root cannot couple to two incomparable off-spine roots.
This is the non-overlap step needed to recover every red/green side couple. -/
theorem no_incomparable_partner_roots {a b c : GNode G.tree}
    (hab : Comb.IsSubCouple G a b) (hac : Comb.IsSubCouple G a c)
    (hbc : b.Incomparable c) : False := by
  obtain ⟨ℓ,hℓ,hb⟩ := subCouple_cross_witness hab
  have hp := (hac ℓ (Finset.mem_union_left _ hℓ)).2
  have hdab := Comb.disjoint_leavesBelow_of_incomparable (Comb.subCouple_incomparable hab)
  have hdbc := Comb.disjoint_leavesBelow_of_incomparable hbc
  rcases Finset.mem_union.mp hp with ha | hc
  · exact (Finset.disjoint_left.mp hdab) ha hb
  · exact (Finset.disjoint_left.mp hdbc) hb hc

/-- Partner roots are unique in any family of pairwise incomparable candidates. -/
theorem partner_root_unique {ι : Type*} (roots : ι → GNode G.tree)
    (hr : Pairwise fun i j => (roots i).Incomparable (roots j))
    {a : GNode G.tree} {i j : ι} (hi : Comb.IsSubCouple G a (roots i))
    (hj : Comb.IsSubCouple G a (roots j)) : i = j := by
  by_contra hne
  exact no_incomparable_partner_roots hi hj (hr hne)

end WaveTurbulence.Reg
