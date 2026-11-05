/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Ordinary garden carriers have exact finite oriented-pair data -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- The canonical finite set of the garden's positive-to-negative leaf pairs. -/
def sourcePairs {w : ℕ} (G : Garden w) : Finset (Pair w) :=
  (Finset.univ.filter fun ℓ : GLeaf G.tree => nodeSign G.sig ℓ.1 = 1).image
    (fun ℓ => (ℓ.1,(G.pair ℓ).1))

/-- An edge oriented from the positive endpoint, read from either endpoint. -/
def sourcePairAt {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) : Pair w :=
  if nodeSign G.sig ℓ.1 = 1 then (ℓ.1,(G.pair ℓ).1) else ((G.pair ℓ).1,ℓ.1)

/-- Every canonical edge is determined by either one of its endpoints. -/
theorem sourcePairs_eq_at {w : ℕ} (G : Garden w) (hG : G.IsPlain)
    (p : Pair w) (hp : p ∈ sourcePairs G) (ℓ : GLeaf G.tree)
    (he : p.1 = ℓ.1 ∨ p.2 = ℓ.1) : p = sourcePairAt G ℓ := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  have hs := (Finset.mem_filter.mp hx).2
  rcases he with he | he
  · have h : x = ℓ := Subtype.ext he
    subst ℓ
    simp only [sourcePairAt,hs,ite_true]
  · have h : G.pair x = ℓ := Subtype.ext he
    subst ℓ
    have hn := G.pair_sign x (Comb.pair_ne_of_plain hG x)
    rw [hs] at hn
    have hne : nodeSign G.sig (G.pair x).1 ≠ 1 := by rw [hn]; decide
    rw [sourcePairAt,ite_eq_right hne,G.pair_pair]

/-- The edge read at a leaf is one of the canonical pairs. -/
theorem sourcePairAt_mem {w : ℕ} (G : Garden w) (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    sourcePairAt G ℓ ∈ sourcePairs G := by
  by_cases hs : nodeSign G.sig ℓ.1 = 1
  · apply Finset.mem_image.mpr
    exact ⟨ℓ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,by rw [sourcePairAt,ite_eq_left hs]⟩
  · have hm : nodeSign G.sig ℓ.1 = -1 := (Int.units_eq_one_or _).resolve_left hs
    have hp := G.pair_sign ℓ (Comb.pair_ne_of_plain hG ℓ)
    rw [hm,neg_neg] at hp
    apply Finset.mem_image.mpr
    exact ⟨G.pair ℓ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,by
      rw [sourcePairAt,ite_eq_right hs,G.pair_pair]⟩

/-- Either orientation retains the input leaf as an actual endpoint. -/
theorem sourcePairAt_endpoint {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) :
    (sourcePairAt G ℓ).1 = ℓ.1 ∨ (sourcePairAt G ℓ).2 = ℓ.1 := by
  by_cases h : nodeSign G.sig ℓ.1 = 1
  · exact Or.inl (by rw [sourcePairAt,ite_eq_left h])
  · exact Or.inr (by rw [sourcePairAt,ite_eq_right h])

/-- The literal finite forest data of an ordinary garden. -/
def rawOfGarden {w : ℕ} (G : Garden w) : Raw w := ⟨G.sig,G.tree,sourcePairs G⟩

/-- Plainness supplies precisely the source matching/leaf/sign typing data. -/
theorem rawOfGarden_valid {w : ℕ} (G : Garden w) (hG : G.IsPlain) : (rawOfGarden G).Valid := by
  constructor
  · intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    have hs := (Finset.mem_filter.mp hx).2
    exact ⟨x.2,(G.pair x).2,hs,by
      have hn := G.pair_sign x (Comb.pair_ne_of_plain hG x)
      exact hn.trans (congrArg Neg.neg hs)⟩
  · intro ℓ
    refine ⟨sourcePairAt G ℓ,⟨sourcePairAt_mem G hG ℓ,sourcePairAt_endpoint G ℓ⟩,?_⟩
    intro p hp
    exact sourcePairs_eq_at G hG p hp.1 ℓ hp.2

/-- Canonical pair data contain every source partner edge in the appropriate orientation. -/
theorem sourcePairs_partner {w : ℕ} (G : Garden w) (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    (ℓ.1,(G.pair ℓ).1) ∈ sourcePairs G ∨ ((G.pair ℓ).1,ℓ.1) ∈ sourcePairs G := by
  have hm := sourcePairAt_mem G hG ℓ
  unfold sourcePairAt at hm
  split_ifs at hm with hs
  · exact Or.inl hm
  · exact Or.inr hm

end WaveTurbulence.Reg.Skeleton
