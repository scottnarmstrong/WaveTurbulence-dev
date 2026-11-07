/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.EndpointExtraction
public import WaveTurbulence.Foundations.FC23.FlowerSeries
/-! Exact T1/T2 assembly over every original tree, including the zero scale. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset Polynomial
variable {w d : ℕ}

theorem treeLeafPolynomial_tail_congr (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (k : GNode LG.garden.tree → Mom d) (j : Fin w) (a b : Fin w → Bool) (h : a j = b j) :
    treeLeafPolynomial LG p M A a k j = treeLeafPolynomial LG p M A b k j := by
  unfold treeLeafPolynomial affineProduct
  apply prod_congr rfl
  intro l hl
  dsimp only
  rw [(mem_filter.mp hl).2, h]

theorem attachedCut_product (P : WTParams) (LG : LayeredGarden w) (p : ℕ) (M : ℝ)
    (tail small : Fin w → Bool) (k : GNode LG.garden.tree → Mom P.d) :
    (∏ j, attachedCut LG p j k (if tail j && small j then M / 2 else M)) =
      flowerBondWeight P p LG M tail small k := by
  have hf (j : Fin w) : attachedCut LG p j k (if tail j && small j then M / 2 else M) =
      ∏ a ∈ univ.filter (fun a : GNode LG.garden.tree => a.1.1 = j),
        if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬LG.IsFlowerNode a then
          chi0 (‖k a‖ / (if tail a.1.1 && small a.1.1 then M / 2 else M)) else 1 := by
    unfold attachedCut attachedTopNodes
    rw [prod_filter, prod_filter]
    apply prod_congr rfl
    intro a _
    by_cases hj : a.1.1 = j
    · by_cases ht : LG.IsTopLeaf p a <;> by_cases hl : LG.layer a < p <;>
        by_cases hfl : LG.IsFlowerNode a <;> simp [hj, ht, hl, hfl]
    · simp [hj]
  simp_rw [hf]
  rw [prod_fiberwise]
  rfl

/-- Exact finite expansion with 3^w terms. Each term uses the original FC3
family; no bound for an individual original-order slice is assumed. -/
theorem native_garden_extraction (P : WTParams) (LG : LayeredGarden w) (p : ℕ)
    (hc : IsCanonH (p + 1) LG) (r : ℕ) (A : ℝ) (hL : 0 < P.L) (hA : 0 < A)
    (k : GNode LG.garden.tree → Mom P.d) (hk : IsDecoration LG.garden k)
    (hscale : ∀ j, ((freeTreeLeaves LG j).card : ℝ) * A ≤ (2 ^ (r + 1) * P.L) / 4) :
    (LG.cutWeight1P p P.L (r + 1) k : ℂ) =
      ∑ e : Fin w → Fin 3, (∏ j, (cutChoiceSign (e j) : ℂ)) *
        (flowerBondWeight P p LG (2 ^ (r + 1) * P.L)
          (fun j => cutChoiceTail (e j)) (fun j => cutChoiceSmall (e j)) k : ℂ) *
        ∏ j, ((treeLeafPolynomial LG p (2 ^ (r + 1) * P.L) A
          (fun j => cutChoiceTail (e j)) k j).eval (cutChoicePoint (e j) : ℂ) -
            (treeLeafPolynomial LG p (2 ^ (r + 1) * P.L) A
          (fun j => cutChoiceTail (e j)) k j).eval 0) := by
  unfold LayeredGarden.cutWeight1P
  push_cast
  simp_rw [fun j => native_tree_extraction hc j P.L r A hL hA k hk (hscale j)]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro e _
  have he (j : Fin w) := treeLeafPolynomial_tail_congr LG p (2 ^ (r + 1) * P.L) A k j
    (fun _ => cutChoiceTail (e j)) (fun j => cutChoiceTail (e j)) rfl
  simp_rw [he]
  rw [prod_mul_distrib, prod_mul_distrib]
  simp only [← Complex.ofReal_prod]
  rw [attachedCut_product]

/-- At dyadic index zero the cut is exactly an evaluation of the uniform
family, with no coefficient extraction and no auxiliary-scale assumption. -/
theorem native_garden_zero (P : WTParams) (LG : LayeredGarden w) (p : ℕ)
    (hc : IsCanonH (p + 1) LG) (A : ℝ) (k : GNode LG.garden.tree → Mom P.d) :
    LG.cutWeight1P p P.L 0 k = flowerFamilyWeight LG p P.L A
      (fun _ => false) (fun _ => false) (fun _ => 1) k := by
  have he (j : Fin w) : prodDyadicCut P.L 0
      (univ.filter fun a : GNode LG.garden.tree => a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬LG.IsFlowerNode a)
      (fun a => ‖k a‖) = directCut LG p j k P.L * attachedCut LG p j k P.L := by
    rw [topNodes_partition LG p hc j]
    simp only [prodDyadicCut, ite_true, pow_zero, one_mul]
    rw [prod_union (topNodes_disjoint LG p j)]
    rfl
  have hp := treeLeafPolynomial_product LG p P.L A (fun _ => false) k (fun _ => 1)
  have hdir : (∏ j, directCut LG p j k P.L) =
      ∏ l : GLeaf LG.garden.tree, if LG.garden.IsFlower l then 1 else
        endpointFactor p (LG.layer l.toNode) false P.L A 1 ‖k l.toNode‖ := by
    apply Complex.ofReal_injective
    push_cast
    simp only [Complex.ofReal_one] at hp
    simp_rw [treeLeafPolynomial_one hc _ P.L A (fun _ => false) rfl] at hp
    simpa only [apply_ite, Complex.ofReal_one] using hp
  rw [LayeredGarden.cutWeight1P]
  simp_rw [he]
  rw [prod_mul_distrib, hdir]
  have hb := attachedCut_product P LG p P.L (fun _ => false) (fun _ => false) k
  simp only [Bool.false_and, Bool.false_eq_true, ite_false] at hb
  rw [hb]
  exact mul_comm _ _
end WaveTurbulence.FC23
