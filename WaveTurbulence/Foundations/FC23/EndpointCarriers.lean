/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.DescendantCutoff
public import WaveTurbulence.Foundations.Molecule.LFTwist.LeafLayers
/-! Equality of native layer-p top leaves with the endpoint profile carrier. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset
variable {w : ℕ}

theorem free_leaf_nonroot {LG : LayeredGarden w} (hf : LG.garden.IsFlowerGarden)
    (l : GLeaf LG.garden.tree) (hl : ¬LG.garden.IsFlower l) : l.1.2 ≠ [] := by
  intro hr
  obtain ⟨l', he⟩ := card_eq_one.mp (hf.1 l.1.1)
  have hmem : l' ∈ univ.filter (fun a : GLeaf LG.garden.tree =>
      a.1.1 = l.1.1 ∧ LG.garden.mark a ≠ none) := by rw [he]; exact mem_singleton_self _
  have hm := (mem_filter.mp hmem).2
  have hdesc : l.toNode.IsDesc l'.toNode := ⟨hm.1.symm, by change l.1.2 <+: l'.1.2; rw [hr]; exact List.nil_prefix⟩
  have hl' := Comb.GLeaf.eq_of_isDesc hdesc
  exact hl (hl' ▸ hf.2.1 l' hm.2)

theorem free_top_leaf {LG : LayeredGarden w} {p : ℕ} (hc : IsCanonH (p + 1) LG)
    (l : GLeaf LG.garden.tree) (hf : ¬LG.garden.IsFlower l) (hl : LG.layer l.toNode = p) :
    LG.IsTopLeaf p l.toNode := by
  refine ⟨Or.inr l.2, free_leaf_nonroot hc.1 l hf, ?_⟩
  have hle := LFTwist.layer_le_parentLayer LG (Canon.layer_le_of_isCanonH hc) l.toNode
  have hge : LG.parentLayer p l.toNode ≤ p := by
    unfold LayeredGarden.parentLayer
    split_ifs
    · rfl
    · exact Canon.layer_le_of_isCanonH hc _
  omega

def directFreeLeaves (LG : LayeredGarden w) (p : ℕ) (j : Fin w) : Finset (GLeaf LG.garden.tree) :=
  (freeTreeLeaves LG j).filter fun l => LG.layer l.toNode = p

theorem directTopNodes_eq_image {LG : LayeredGarden w} {p : ℕ} (hc : IsCanonH (p + 1) LG)
    (j : Fin w) : directTopNodes LG p j = (directFreeLeaves LG p j).image GLeaf.toNode := by
  ext a
  constructor
  · intro ha
    obtain ⟨hj, ht, hf, hl⟩ := (mem_filter.mp ha).2
    have hleaf : a.1.2 ∈ (LG.garden.tree a.1.1).leaves := ht.1.resolve_left (by omega)
    let l : GLeaf LG.garden.tree := ⟨a.1, hleaf⟩
    refine mem_image.mpr ⟨l, ?_, rfl⟩
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, hj⟩, hl⟩
    intro h
    exact hf ⟨l, h, rfl⟩
  · intro ha
    obtain ⟨l, hl, rfl⟩ := mem_image.mp ha
    have hp := (mem_filter.mp hl).2
    have hj := (mem_filter.mp (mem_filter.mp hl).1).2
    have hf := (mem_filter.mp (mem_filter.mp (mem_filter.mp hl).1).1).2
    refine mem_filter.mpr ⟨mem_univ _, hj, free_top_leaf hc l hf hp, ?_, hp⟩
    rintro ⟨l', hf', he⟩
    have hll : l' = l := Subtype.ext (congrArg (fun a : GNode LG.garden.tree => a.1) he)
    exact hf (hll ▸ hf')

/-- Every endpoint at layer p is exactly one direct top leaf; other endpoint
layers contribute one. This includes negative endpoints. -/
theorem directTopNodes_product {LG : LayeredGarden w} {p : ℕ} (hc : IsCanonH (p + 1) LG)
    (j : Fin w) {M : Type*} [CommMonoid M] (g : GNode LG.garden.tree → M) :
    (∏ a ∈ directTopNodes LG p j, g a) =
      ∏ l ∈ freeTreeLeaves LG j, if LG.layer l.toNode = p then g l.toNode else 1 := by
  rw [directTopNodes_eq_image hc j, prod_image]
  · exact prod_filter (fun l : GLeaf LG.garden.tree => LG.layer l.toNode = p) (fun l => g l.toNode)
  · intro l _ l' _ he
    exact Subtype.ext (congrArg (fun a : GNode LG.garden.tree => a.1) he)
end WaveTurbulence.FC23
