/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.PlainGraft

/-!
# X2E-2, step 2: pairing the flowers of a flower garden

A flower garden has exactly one marked leaf per tree, a flower. Let `σ` be a fixed-point-free involution of the
trees with `ζ_{σ j} = −ζ_j`, and let the flower of tree `j` carry the sign `ζ ζ_j`. Pairing the flower of tree `j`
with the flower of tree `σ j` gives a **plain** garden `pairFl LG` with the same trees, signature and layers.

**Statements.**
- `flowerOf LG j`: the marked leaf of tree `j`; `eq_flowerOf` (uniqueness), `flowerOf_isFlower`.
- `pairFl`: the paired layered garden; `pairFl_plain`, `pairFl_pair_flower`, `pairFl_pair_of_unmarked`.
- `canonCriterion_pairFl_iff`: if the stems are in layer `p` and all layers are `≤ p`, then `CanonCriterion p`
  holds for `pairFl LG` iff it holds for `LG`. A completely paired set of `LG` contains no flower. A completely
  paired set of `pairFl LG` containing a flower lies below a stem node, whose layer is `p`.
- `isCanonH_iff_pairFl`: `IsCanonH (p+1) LG` iff `LG` is a flower garden with stems in layer `p` and
  `pairFl LG` satisfies `CanonCriterion p`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct

variable {w : ℕ}

namespace LayeredGarden'

variable (LG : LayeredGarden w)

theorem exists_flower_choice (j : Fin w) : ∃ ℓ : GLeaf LG.garden.tree,
    (∃ ℓ' : GLeaf LG.garden.tree, ℓ'.1.1 = j ∧ LG.garden.mark ℓ' ≠ none) → ℓ.1.1 = j ∧ LG.garden.mark ℓ ≠ none := by
  by_cases h : ∃ ℓ' : GLeaf LG.garden.tree, ℓ'.1.1 = j ∧ LG.garden.mark ℓ' ≠ none
  · obtain ⟨ℓ', hℓ'⟩ := h
    exact ⟨ℓ', fun _ => hℓ'⟩
  · exact ⟨⟨(j, (tree_leaves_nonempty (LG.garden.tree j)).choose),
      (tree_leaves_nonempty (LG.garden.tree j)).choose_spec⟩, fun h' => absurd h' h⟩

/-- The marked leaf of tree `j` (the flower, in a flower garden). -/
noncomputable def flowerOf (j : Fin w) : GLeaf LG.garden.tree := (exists_flower_choice LG j).choose

variable {LG}

theorem exists_marked (hFG : LG.garden.IsFlowerGarden) (j : Fin w) :
    ∃ ℓ : GLeaf LG.garden.tree, ℓ.1.1 = j ∧ LG.garden.mark ℓ ≠ none := by
  classical
  obtain ⟨ℓ, hℓ⟩ := card_eq_one.mp (hFG.1 j)
  have h : ℓ ∈ univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.mark ℓ ≠ none := by
    rw [hℓ]
    exact mem_singleton_self ℓ
  exact ⟨ℓ, (mem_filter.mp h).2⟩

theorem flowerOf_spec (hFG : LG.garden.IsFlowerGarden) (j : Fin w) :
    (flowerOf LG j).1.1 = j ∧ LG.garden.mark (flowerOf LG j) ≠ none := by
  exact (exists_flower_choice LG j).choose_spec (exists_marked hFG j)

theorem eq_flowerOf (hFG : LG.garden.IsFlowerGarden) {ℓ : GLeaf LG.garden.tree}
    (hm : LG.garden.mark ℓ ≠ none) : ℓ = flowerOf LG ℓ.1.1 := by
  classical
  obtain ⟨m, hm1⟩ := card_eq_one.mp (hFG.1 ℓ.1.1)
  have h1 : ℓ ∈ univ.filter fun ℓ' : GLeaf LG.garden.tree => ℓ'.1.1 = ℓ.1.1 ∧ LG.garden.mark ℓ' ≠ none :=
    mem_filter.mpr ⟨mem_univ _, rfl, hm⟩
  have h2 : flowerOf LG ℓ.1.1 ∈
      univ.filter fun ℓ' : GLeaf LG.garden.tree => ℓ'.1.1 = ℓ.1.1 ∧ LG.garden.mark ℓ' ≠ none :=
    mem_filter.mpr ⟨mem_univ _, flowerOf_spec hFG ℓ.1.1⟩
  rw [hm1, mem_singleton] at h1 h2
  exact h1.trans h2.symm

theorem flowerOf_isFlower (hFG : LG.garden.IsFlowerGarden) (j : Fin w) :
    LG.garden.IsFlower (flowerOf LG j) :=
  hFG.2.1 _ (flowerOf_spec hFG j).2

end LayeredGarden'

open LayeredGarden'

section Pair

variable (LG : LayeredGarden w) (σ : Fin w → Fin w) (hσ : Function.Involutive σ) (hσne : ∀ j, σ j ≠ j)
  (hFG : LG.garden.IsFlowerGarden) (ζ : ℤˣ)
  (hsig : ∀ j, LG.garden.sig (σ j) = -LG.garden.sig j)
  (hfl : ∀ ℓ, LG.garden.IsFlower ℓ → LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1)
  (hlay : ∀ ℓ ℓ' : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.garden.IsFlower ℓ' →
    LG.layer ℓ.toNode = LG.layer ℓ'.toNode)

/-- The paired pairing: the flower of tree `j` goes to the flower of tree `σ j`. -/
noncomputable def pairFlPair (ℓ : GLeaf LG.garden.tree) : GLeaf LG.garden.tree := by
  classical
  exact if LG.garden.mark ℓ ≠ none then flowerOf LG (σ ℓ.1.1) else LG.garden.pair ℓ

theorem pairFlPair_marked {ℓ : GLeaf LG.garden.tree} (hm : LG.garden.mark ℓ ≠ none) :
    pairFlPair LG σ ℓ = flowerOf LG (σ ℓ.1.1) := by
  unfold pairFlPair
  split_ifs
  rfl

theorem pairFlPair_unmarked {ℓ : GLeaf LG.garden.tree} (hm : LG.garden.mark ℓ = none) :
    pairFlPair LG σ ℓ = LG.garden.pair ℓ := by
  unfold pairFlPair
  split_ifs with h
  · exact absurd hm h
  · rfl

theorem mark_pair_of_unmarked {ℓ : GLeaf LG.garden.tree} (hm : LG.garden.mark ℓ = none) :
    LG.garden.mark (LG.garden.pair ℓ) = none := by
  by_contra h
  have h1 : LG.garden.pair (LG.garden.pair ℓ) = LG.garden.pair ℓ := (LG.garden.pair_eq_iff _).mpr h
  rw [LG.garden.pair_pair] at h1
  exact ((LG.garden.pair_eq_iff ℓ).mp h1.symm) hm

include hσ hFG in
theorem pairFlPair_involutive : Function.Involutive (pairFlPair LG σ) := by
  intro ℓ
  by_cases hm : LG.garden.mark ℓ = none
  · rw [pairFlPair_unmarked LG σ hm, pairFlPair_unmarked LG σ (mark_pair_of_unmarked LG hm),
      LG.garden.pair_pair]
  · rw [pairFlPair_marked LG σ hm, pairFlPair_marked LG σ (flowerOf_spec hFG _).2,
      (flowerOf_spec hFG _).1, hσ]
    exact (eq_flowerOf hFG hm).symm

include hσne hFG in
theorem pairFlPair_ne (ℓ : GLeaf LG.garden.tree) : pairFlPair LG σ ℓ ≠ ℓ := by
  by_cases hm : LG.garden.mark ℓ = none
  · rw [pairFlPair_unmarked LG σ hm]
    intro h
    exact ((LG.garden.pair_eq_iff ℓ).mp h) hm
  · rw [pairFlPair_marked LG σ hm]
    intro h
    have h1 := congrArg (fun l : GLeaf LG.garden.tree => l.1.1) h
    simp only [(flowerOf_spec hFG _).1] at h1
    exact hσne _ h1

include hFG hsig hfl in
theorem pairFlPair_sign (ℓ : GLeaf LG.garden.tree) :
    nodeSign LG.garden.sig (pairFlPair LG σ ℓ).1 = -nodeSign LG.garden.sig ℓ.1 := by
  by_cases hm : LG.garden.mark ℓ = none
  · rw [pairFlPair_unmarked LG σ hm]
    exact LG.garden.pair_sign ℓ (fun h => ((LG.garden.pair_eq_iff ℓ).mp h) hm)
  · rw [pairFlPair_marked LG σ hm]
    have h1 := hfl _ (flowerOf_isFlower hFG (σ ℓ.1.1))
    have h2 := hfl ℓ (hFG.2.1 ℓ hm)
    change nodeSign LG.garden.sig (flowerOf LG (σ ℓ.1.1)).1 = ζ * LG.garden.sig (flowerOf LG (σ ℓ.1.1)).1.1 at h1
    change nodeSign LG.garden.sig ℓ.1 = ζ * LG.garden.sig ℓ.1.1 at h2
    rw [h1, h2, (flowerOf_spec hFG _).1, hsig, mul_neg]

/-- **The paired garden.** -/
noncomputable def pairFlGarden : Garden w where
  sig := LG.garden.sig
  tree := LG.garden.tree
  pair := pairFlPair LG σ
  mark := fun _ => none
  pair_pair := pairFlPair_involutive LG σ hσ hFG
  pair_eq_iff ℓ := by
    simp only [ne_eq, not_true_eq_false, iff_false]
    exact pairFlPair_ne LG σ hσne hFG ℓ
  pair_sign ℓ _ := pairFlPair_sign LG σ hFG ζ hsig hfl ℓ

/-- **The paired layered garden.** -/
noncomputable def pairFl : LayeredGarden w where
  garden := pairFlGarden LG σ hσ hσne hFG ζ hsig hfl
  layer := LG.layer
  isLayering := by
    refine ⟨LG.isLayering.1, fun ℓ => ?_⟩
    change LG.layer ℓ.toNode = LG.layer (pairFlPair LG σ ℓ).toNode
    by_cases hm : LG.garden.mark ℓ = none
    · rw [pairFlPair_unmarked LG σ hm]
      exact LG.isLayering.2 ℓ
    · rw [pairFlPair_marked LG σ hm]
      exact hlay _ _ (hFG.2.1 ℓ hm) (flowerOf_isFlower hFG _)

theorem pairFl_plain : (pairFl LG σ hσ hσne hFG ζ hsig hfl hlay).garden.IsPlain := fun _ => rfl

end Pair

/-! ## The criterion -/

section Criterion

variable {LG : LayeredGarden w} {σ : Fin w → Fin w} {hσ : Function.Involutive σ} {hσne : ∀ j, σ j ≠ j}
  {hFG : LG.garden.IsFlowerGarden} {ζ : ℤˣ}
  {hsig : ∀ j, LG.garden.sig (σ j) = -LG.garden.sig j}
  {hfl : ∀ ℓ, LG.garden.IsFlower ℓ → LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1}
  {hlay : ∀ ℓ ℓ' : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.garden.IsFlower ℓ' →
    LG.layer ℓ.toNode = LG.layer ℓ'.toNode}

theorem completelyPaired_pairFl_of (S : Finset (GLeaf LG.garden.tree)) (h : LG.garden.CompletelyPaired S) :
    (pairFl LG σ hσ hσne hFG ζ hsig hfl hlay).garden.CompletelyPaired S := by
  intro ℓ hℓ
  have hm : LG.garden.mark ℓ = none := by
    by_contra hm
    exact (h ℓ hℓ).1 ((LG.garden.pair_eq_iff ℓ).mpr hm)
  change pairFlPair LG σ ℓ ≠ ℓ ∧ pairFlPair LG σ ℓ ∈ S
  rw [pairFlPair_unmarked LG σ hm]
  exact h ℓ hℓ

theorem completelyPaired_of_pairFl (S : Finset (GLeaf LG.garden.tree)) (hS : ∀ ℓ ∈ S, LG.garden.mark ℓ = none)
    (h : (pairFl LG σ hσ hσne hFG ζ hsig hfl hlay).garden.CompletelyPaired S) :
    LG.garden.CompletelyPaired S := by
  intro ℓ hℓ
  have h1 := h ℓ hℓ
  change pairFlPair LG σ ℓ ≠ ℓ ∧ pairFlPair LG σ ℓ ∈ S at h1
  rw [pairFlPair_unmarked LG σ (hS ℓ hℓ)] at h1
  exact h1

/-- **`CanonCriterion` is unchanged by pairing the flowers**, when the stems are in layer `p`. -/
theorem canonCriterion_pairFl_iff (p : ℕ) (hstem : ∀ a, LG.OnStem a → LG.layer a = p) :
    (pairFl LG σ hσ hσne hFG ζ hsig hfl hlay).CanonCriterion p ↔ LG.CanonCriterion p := by
  constructor
  · rintro ⟨hb, hc⟩
    refine ⟨hb, fun a a' hinc hcp => ?_⟩
    exact hc a a' hinc (completelyPaired_pairFl_of _ hcp)
  · rintro ⟨hb, hc⟩
    refine ⟨hb, fun a a' hinc hcp => ?_⟩
    change min (LG.parentLayer p a) (LG.parentLayer p a') ≤ max (LG.layer a) (LG.layer a')
    by_cases hS : ∀ ℓ ∈ a.leavesBelow ∪ a'.leavesBelow, LG.garden.mark ℓ = none
    · exact hc a a' hinc (completelyPaired_of_pairFl _ hS hcp)
    · push Not at hS
      obtain ⟨ℓ, hℓ, hm⟩ := hS
      have hflo := hFG.2.1 ℓ hm
      have hpl : LG.parentLayer p a ≤ p := parentLayer_le_of_layer_le LG p hb a
      rcases mem_union.mp hℓ with h | h
      · have hd : a.IsDesc ℓ.toNode := by
          simp only [GNode.leavesBelow, mem_filter, mem_univ, true_and] at h
          exact h
        have hst : LG.OnStem a := ⟨ℓ, hflo, hd⟩
        rw [hstem a hst]
        exact (min_le_left _ _).trans (hpl.trans (le_max_left _ _))
      · have hpl' : LG.parentLayer p a' ≤ p := parentLayer_le_of_layer_le LG p hb a'
        have hd : a'.IsDesc ℓ.toNode := by
          simp only [GNode.leavesBelow, mem_filter, mem_univ, true_and] at h
          exact h
        have hst : LG.OnStem a' := ⟨ℓ, hflo, hd⟩
        rw [hstem a' hst]
        exact (min_le_right _ _).trans (hpl'.trans (le_max_right _ _))

end Criterion

end WaveTurbulence.X2E
