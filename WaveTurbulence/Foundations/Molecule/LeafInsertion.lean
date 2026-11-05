/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistCrown
public import WaveTurbulence.Foundations.Molecule.ReplacementLeaves
public import WaveTurbulence.Foundations.Molecule.Subtrees

/-! # Inserting a tree at an actual forest leaf

TARGET twist: collapse the lower subtree to obtain a common forest with
two distinguished leaves, then insert the switched subtree at the other
leaf. These operations act on actual ordered trees and their addresses.
-/

public section
namespace WaveTurbulence.Twist
open TTree Finset

/-- Extraction at a leaf gives exactly the trivial tree. -/
theorem subtree_leaf_iff : ∀ (t : TTree) (p : Path),
    Comb.subtree t p = some .leaf ↔ p ∈ t.leaves
  | t, [] => by cases t <;> simp [Comb.subtree,TTree.leaves,TTree.pre]
  | .leaf, i::p => by simp [Comb.subtree,TTree.leaves]
  | .node l m r, i::p => by
    fin_cases i <;> simp [Comb.subtree,TTree.leaves,TTree.cons_mem_pre,subtree_leaf_iff]

/-- A leaf address cannot be a strict prefix of another leaf. -/
theorem leaf_prefix_eq {t : TTree} {p q : Path} (hp : p ∈ t.leaves) (hq : q ∈ t.leaves)
    (hpre : p <+: q) : p = q := by
  obtain ⟨r,hr⟩ := hpre
  have hs := (subtree_leaf_iff t p).mpr hp
  have hmem : r ∈ TTree.leaf.leaves :=
    (Comb.subtree_leaves_iff hs r).mpr (hr ▸ hq)
  have he : r = [] := mem_singleton.mp hmem
  simpa only [he,List.append_nil] using hr

/-- A leaf address cannot be a prefix of a branching address. -/
theorem leaf_not_prefix_branch {t : TTree} {p q : Path} (hp : p ∈ t.leaves)
    (hq : q ∈ t.branching) : ¬ p <+: q := by
  rintro ⟨r,hr⟩
  have hs := (subtree_leaf_iff t p).mpr hp
  have hmem := (Comb.subtree_branching_iff hs r).mpr (hr ▸ hq)
  exact notMem_empty r hmem

/-- Insert a subtree at a specified actual leaf of a forest. -/
@[expose] def insertLeaf {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) (t : TTree) : Fin w → TTree :=
  Function.update F h.1.1 (Comb.replaceAt (F h.1.1) h.1.2 t)

/-- The changed tree has the literal replacement body. -/
theorem insertLeaf_at {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) (t : TTree) :
    insertLeaf F h t h.1.1 = Comb.replaceAt (F h.1.1) h.1.2 t :=
  Function.update_self _ _ _

/-- All other trees remain literally equal. -/
theorem insertLeaf_other {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) (t : TTree)
    (j : Fin w) (hj : j ≠ h.1.1) : insertLeaf F h t j = F j :=
  Function.update_of_ne hj _ _

/-- Exact leaf addresses in the inserted tree. -/
theorem insertLeaf_leaves {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) (t : TTree) :
    (insertLeaf F h t h.1.1).leaves =
      ((F h.1.1).leaves.filter fun q => q ≠ h.1.2) ∪ t.leaves.image (fun q => h.1.2 ++ q) := by
  rw [insertLeaf_at,Comb.leaves_replaceAt_eq ((subtree_leaf_iff _ _).mpr h.2)]
  congr 1
  ext q
  simp only [mem_filter]
  constructor
  · rintro ⟨hq,hpre⟩
    exact ⟨hq,fun he => hpre (he ▸ List.prefix_refl _)⟩
  · rintro ⟨hq,hne⟩
    exact ⟨hq,fun hpre => hne (leaf_prefix_eq h.2 hq hpre).symm⟩

/-- The inserted subtree can be extracted at the same address. -/
theorem subtree_insertLeaf {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) (t : TTree) :
    Comb.subtree (insertLeaf F h t h.1.1) h.1.2 = some t := by
  rw [insertLeaf_at]
  exact Comb.subtree_replaceAt ((subtree_leaf_iff _ _).mpr h.2) t

/-- Inserting a leaf restores the common forest exactly. -/
theorem insertLeaf_leaf {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) : insertLeaf F h .leaf = F := by
  funext j
  by_cases hj : j = h.1.1
  · subst j
    rw [insertLeaf_at]
    exact Comb.replaceAt_self ((subtree_leaf_iff _ _).mpr h.2)
  · exact insertLeaf_other F h .leaf j hj

end WaveTurbulence.Twist
