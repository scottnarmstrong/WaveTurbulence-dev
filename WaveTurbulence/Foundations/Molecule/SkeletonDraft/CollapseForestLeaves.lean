/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceMiniShapes

/-! # Literal leaf payload of collapsing two incomparable source subtrees -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- One collapsed root becomes a new leaf; every other leaf is an unchanged old leaf outside it. -/
theorem collapseNodeForest_leaf_iff {w : ℕ} (tree : Fin w → TTree) (a : GNode tree) (x : Address w) :
    x.2 ∈ (Comb.collapseNodeForest tree a x.1).leaves ↔
      (x.2 ∈ (tree x.1).leaves ∧ ¬ Below a.1 x) ∨ x = a.1 := by
  obtain ⟨j,p⟩ := x
  by_cases hj : j = a.1.1
  · have hf : Comb.collapseNodeForest tree a j = Comb.collapseAt (tree a.1.1) a.1.2 := by
      rw [Comb.collapseNodeForest,Comb.replaceNodeForest,hj,Function.update_self]
      rfl
    rw [hf]
    have he := Comb.mem_leaves_collapseAt_iff (Comb.nodeSubtree_spec a) (q := p)
    constructor
    · intro hp
      rcases he.mp hp with ⟨hl,hn⟩ | ha
      · exact Or.inl ⟨by rw [hj]; exact hl,fun hb => hn hb.2⟩
      · exact Or.inr (Prod.ext hj ha)
    · rintro (⟨hl,hn⟩ | ha)
      · apply he.mpr
        exact Or.inl ⟨by rw [← hj]; exact hl,fun hp => hn ⟨hj,hp⟩⟩
      · apply he.mpr
        exact Or.inr (congrArg Prod.snd ha)
  · have hf : Comb.collapseNodeForest tree a j = tree j := by
      rw [Comb.collapseNodeForest,Comb.replaceNodeForest,Function.update_of_ne hj]
    rw [hf]
    constructor
    · intro hp
      exact Or.inl ⟨hp,fun hb => hj hb.1⟩
    · rintro (⟨hp,_⟩ | ha)
      · exact hp
      · exact (hj (congrArg Prod.fst ha)).elim

/-- Collapse the two literal incomparable roots without changing any other subtree. -/
def collapsePairForest {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (hab : a.Incomparable b) :
    Fin w → TTree :=
  Comb.collapseNodeForest (Comb.collapseNodeForest tree a) (Comb.collapseOtherNode tree a b hab)

/-- Exact leaf decomposition of the collapsed forest, including both new root leaves. -/
theorem collapsePairForest_leaf_iff {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) (x : Address w) :
    x.2 ∈ (collapsePairForest tree a b hab x.1).leaves ↔
      (x.2 ∈ (tree x.1).leaves ∧ ¬ Below a.1 x ∧ ¬ Below b.1 x) ∨ x = a.1 ∨ x = b.1 := by
  have hba : ¬ Below b.1 a.1 := fun h => hab.2 ⟨h.1.symm,h.2⟩
  have he := collapseNodeForest_leaf_iff (Comb.collapseNodeForest tree a)
    (Comb.collapseOtherNode tree a b hab) x
  change x.2 ∈ (collapsePairForest tree a b hab x.1).leaves ↔
    (x.2 ∈ (Comb.collapseNodeForest tree a x.1).leaves ∧ ¬ Below b.1 x) ∨ x = b.1 at he
  rw [collapseNodeForest_leaf_iff tree a x] at he
  constructor
  · intro hx
    rcases he.mp hx with ⟨h,hb⟩ | hb
    · rcases h with ⟨hl,ha⟩ | ha
      · exact Or.inl ⟨hl,ha,hb⟩
      · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr hb)
  · rintro (⟨hl,ha,hb⟩ | ha | hb)
    · exact he.mpr (Or.inl ⟨Or.inl ⟨hl,ha⟩,hb⟩)
    · exact he.mpr (Or.inl ⟨Or.inr ha,by rw [ha]; exact hba⟩)
    · exact he.mpr (Or.inr hb)

/-- Distinct incomparable roots retain distinct raw addresses. -/
theorem incomparable_addr_ne {w : ℕ} {tree : Fin w → TTree} {a b : GNode tree} (hab : a.Incomparable b) :
    a.1 ≠ b.1 := by
  intro he
  have hn : a = b := Subtype.ext he
  subst b
  exact hab.1 ⟨rfl,List.prefix_refl _⟩

end WaveTurbulence.Reg.Skeleton
