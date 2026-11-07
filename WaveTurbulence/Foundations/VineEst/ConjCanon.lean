/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.GardenConj
public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4KConj

/-!
# Transport of the canonical criterion along a conjugation (CONJ-COH)

Along `IsConjugateBy LG LH e` the node, leaf and branching-node sets correspond (`PL234.Conj.nodeEquiv`, ...), the
layers and the pairing are transported, so `IsPlain`, `Irreducible` and `CanonCriterion p` (TARGET Prop `canonequiv`)
are invariant.  Signs enter `IsCanonGC` only through the width-`2` clause `sig j = (-1)^j`, which is dealt with in
`ConjCoherent`.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.ConjCoh

open WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.PL234

variable {w : ℕ} {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w} (h : IsConjugateBy LG LH e)

include h

theorem conj_isPlain (hp : LG.garden.IsPlain) : LH.garden.IsPlain := by
  intro ℓ'
  obtain ⟨ℓ, rfl⟩ := (Conj.leafEquiv h).surjective ℓ'
  rw [Conj.mark_leaf]; exact hp ℓ

theorem conj_isDesc_iff (a a' : GNode LG.garden.tree) :
    (Conj.nodeEquiv h a).IsDesc (Conj.nodeEquiv h a') ↔ a.IsDesc a' := by
  show (e a.1.1 = e a'.1.1 ∧ a.1.2 <+: a'.1.2) ↔ (a.1.1 = a'.1.1 ∧ a.1.2 <+: a'.1.2)
  rw [e.apply_eq_iff_eq]

theorem conj_incomparable_iff (a a' : GNode LG.garden.tree) :
    (Conj.nodeEquiv h a).Incomparable (Conj.nodeEquiv h a') ↔ a.Incomparable a' := by
  unfold GNode.Incomparable
  rw [conj_isDesc_iff h, conj_isDesc_iff h]

theorem conj_completelyPaired_iff (S : Finset (GLeaf LG.garden.tree)) :
    LH.garden.CompletelyPaired (S.map (Conj.leafEquiv h).toEmbedding) ↔ LG.garden.CompletelyPaired S := by
  unfold Garden.CompletelyPaired
  constructor
  · intro H ℓ hℓ
    have := H (Conj.leafEquiv h ℓ) (Finset.mem_map_of_mem _ hℓ)
    rw [Conj.pair_leaf] at this
    refine ⟨fun heq => this.1 (by rw [heq]), ?_⟩
    obtain ⟨x, hx, hxe⟩ := Finset.mem_map.1 this.2
    have : x = LG.garden.pair ℓ := (Conj.leafEquiv h).injective hxe
    exact this ▸ hx
  · intro H ℓ' hℓ'
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_map.1 hℓ'
    have := H ℓ hℓ
    show LH.garden.pair (Conj.leafEquiv h ℓ) ≠ Conj.leafEquiv h ℓ ∧
      LH.garden.pair (Conj.leafEquiv h ℓ) ∈ S.map (Conj.leafEquiv h).toEmbedding
    rw [Conj.pair_leaf]
    refine ⟨fun heq => this.1 ((Conj.leafEquiv h).injective heq), ?_⟩
    exact Finset.mem_map_of_mem _ this.2

theorem conj_leavesBelow_union (a a' : GNode LG.garden.tree) :
    (Conj.nodeEquiv h a).leavesBelow ∪ (Conj.nodeEquiv h a').leavesBelow =
      (a.leavesBelow ∪ a'.leavesBelow).map (Conj.leafEquiv h).toEmbedding := by
  ext ℓ'
  obtain ⟨ℓ, rfl⟩ := (Conj.leafEquiv h).surjective ℓ'
  simp only [Finset.mem_union, GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map, Equiv.coe_toEmbedding]
  rw [Conj.leaf_toNode, conj_isDesc_iff h, conj_isDesc_iff h]
  constructor
  · intro H; exact ⟨ℓ, H, rfl⟩
  · rintro ⟨x, hx, hxe⟩
    have : x = ℓ := (Conj.leafEquiv h).injective hxe
    exact this ▸ hx

theorem conj_parentLayer (p : ℕ) (a : GNode LG.garden.tree) :
    LH.parentLayer p (Conj.nodeEquiv h a) = LG.parentLayer p a := by
  unfold LayeredGarden.parentLayer
  by_cases hnil : a.1.2 = []
  · have : (Conj.nodeEquiv h a).1.2 = [] := hnil
    simp [hnil, this]
  · have : ¬ (Conj.nodeEquiv h a).1.2 = [] := hnil
    simp only [hnil, this, ite_false]
    exact Conj.layer_node h ⟨(a.1.1, a.1.2.dropLast), _⟩

theorem conj_canonCriterion {p : ℕ} (hc : LG.CanonCriterion p) : LH.CanonCriterion p := by
  refine ⟨fun a' => ?_, fun a' b' hinc hcp => ?_⟩
  · obtain ⟨a, rfl⟩ := (Conj.nodeEquiv h).surjective a'
    rw [Conj.layer_node]; exact hc.1 a
  · obtain ⟨a, rfl⟩ := (Conj.nodeEquiv h).surjective a'
    obtain ⟨b, rfl⟩ := (Conj.nodeEquiv h).surjective b'
    rw [conj_incomparable_iff h] at hinc
    rw [conj_leavesBelow_union h, conj_completelyPaired_iff h] at hcp
    rw [conj_parentLayer h, conj_parentLayer h, Conj.layer_node, Conj.layer_node]
    exact hc.2 a b hinc hcp

theorem conj_leavesOf (A : Finset (Fin w)) :
    LH.garden.leavesOf (A.image e) = (LG.garden.leavesOf A).map (Conj.leafEquiv h).toEmbedding := by
  ext ℓ'
  obtain ⟨ℓ, rfl⟩ := (Conj.leafEquiv h).surjective ℓ'
  simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hie⟩
    refine ⟨ℓ, ?_, rfl⟩
    have : i = ℓ.1.1 := e.injective hie
    exact this ▸ hi
  · rintro ⟨x, hx, hxe⟩
    have : x = ℓ := (Conj.leafEquiv h).injective hxe
    exact ⟨ℓ.1.1, this ▸ hx, rfl⟩

theorem conj_irreducible (hi : LG.garden.Irreducible) : LH.garden.Irreducible := by
  intro A' hne hall hcp
  apply hi (A'.image e.symm)
  · exact hne.image _
  · intro hA
    apply hall
    have : A' = (A'.image e.symm).image e := by
      ext x; simp
    rw [this, hA, Finset.image_univ_of_surjective e.surjective]
  · have := conj_leavesOf h (A'.image e.symm)
    rw [Finset.image_image] at this
    simp only [Equiv.self_comp_symm, Finset.image_id] at this
    rw [this, conj_completelyPaired_iff h] at hcp
    exact hcp

end WaveTurbulence.ConjCoh
