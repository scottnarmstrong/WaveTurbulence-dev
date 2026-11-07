/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Defs
/-! # FL-TYPED: the family weight is frontier cutoffs times pair-type profiles. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Typed
open Finset

theorem flowerFamilyWeight_split {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (tail small : Fin w → Bool) (z : Fin w → ℝ) (k : GNode LG.garden.tree → Mom d) :
    FC23.flowerFamilyWeight LG p M A tail small z k =
      frontierW LG p (fun j => some (if tail j && small j then M / 2 else M)) k *
      ∏ l : GLeaf LG.garden.tree, if LG.garden.IsFlower l then 1 else
        FC23.endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A (z l.1.1) ‖k l.toNode‖ := by
  simp only [FC23.flowerFamilyWeight, frontierW, Option.elim_some]

/-- Product over the non-flower leaves of a garden whose marks are all flowers, folded onto the
input leaves through the pairing. -/
theorem prod_nonflower_eq_prod_input {w : ℕ} (G : Garden w)
    (hf : ∀ ℓ, G.mark ℓ ≠ none → G.IsFlower ℓ) (g : GLeaf G.tree → ℝ) :
    (∏ l : GLeaf G.tree, if G.IsFlower l then 1 else g l) =
      ∏ ℓ ∈ inputLeaves G, g ℓ * g (G.pair ℓ) := by
  have hmk : ∀ l, G.mark l = none ↔ G.pair l ≠ l := fun l => by
    have := G.pair_eq_iff l
    constructor
    · intro h he; exact (this.1 he) h
    · intro h; by_contra hm; exact h (this.2 hm)
  have hmk' (l : GLeaf G.tree) (hl : G.mark l = none) : G.mark (G.pair l) = none := by
    rw [hmk]
    intro he
    apply (hmk l).1 hl
    rw [G.pair_pair] at he
    exact he.symm
  have hflip (l : GLeaf G.tree) (hl : G.mark l = none) : G.sign (G.pair l).toNode = -G.sign l.toNode :=
    G.pair_sign l ((hmk l).1 hl)
  have hnf : ∀ l, ¬ G.IsFlower l ↔ G.mark l = none := fun l => by
    constructor
    · intro h
      by_contra hm
      exact h (hf l hm)
    · intro h hfl
      have : G.mark l = some MarkTag.equal := hfl
      rw [h] at this
      exact absurd this (by simp)
  let S := inputLeaves G
  let T : Finset (GLeaf G.tree) := univ.filter fun l => G.mark l = none ∧ ¬ G.sign l.toNode = 1
  have hP : (univ.filter fun l : GLeaf G.tree => ¬ G.IsFlower l) = S ∪ T := by
    ext l
    simp only [S, T, inputLeaves, mem_filter, mem_univ, true_and, mem_union, hnf]
    tauto
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [S, T, inputLeaves, mem_filter, mem_univ, true_and] at h1 h2
    exact h2.2 h1.1
  have hlhs : (∏ l : GLeaf G.tree, if G.IsFlower l then 1 else g l) =
      ∏ l ∈ univ.filter (fun l : GLeaf G.tree => ¬ G.IsFlower l), g l := by
    rw [prod_filter]
    refine prod_congr rfl fun l _ => ?_
    by_cases h : G.IsFlower l <;> simp [h]
  have hT : ∏ l ∈ T, g l = ∏ l ∈ S, g (G.pair l) := by
    symm
    refine prod_nbij' (fun l => G.pair l) (fun l => G.pair l) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [S, T, inputLeaves, mem_filter, mem_univ, true_and, Finset.mem_coe] at hl ⊢
      refine ⟨hmk' l hl.2, ?_⟩
      rw [hflip l hl.2, hl.1]
      decide
    · intro l hl
      simp only [S, T, inputLeaves, mem_filter, mem_univ, true_and, Finset.mem_coe] at hl ⊢
      have hl0 := hl.1
      have h2 : G.mark (G.pair l) = none := hmk' l hl0
      have hs : G.sign l.toNode = -1 := (Int.units_eq_one_or _).resolve_left hl.2
      refine ⟨?_, hmk' l hl0⟩
      rw [hflip l hl0, hs, neg_neg]
    · intro l _; exact G.pair_pair l
    · intro l _; exact G.pair_pair l
    · intro l _; rfl
  rw [hlhs, hP, prod_union hdisj, hT, ← prod_mul_distrib]

end WaveTurbulence.Flower.Typed
