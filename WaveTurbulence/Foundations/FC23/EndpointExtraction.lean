/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.EndpointCarriers
/-! Exact polynomial evaluations for the native T1 and T2 endpoint carriers. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset Polynomial
variable {w d : ℕ} {LG : LayeredGarden w} {p : ℕ}

def directCut (LG : LayeredGarden w) (p : ℕ) (j : Fin w)
    (k : GNode LG.garden.tree → Mom d) (R : ℝ) : ℝ :=
  ∏ a ∈ directTopNodes LG p j, chi0 (‖k a‖ / R)

def attachedCut (LG : LayeredGarden w) (p : ℕ) (j : Fin w)
    (k : GNode LG.garden.tree → Mom d) (R : ℝ) : ℝ :=
  ∏ a ∈ attachedTopNodes LG p j, chi0 (‖k a‖ / R)

theorem treeLeafPolynomial_zero (hc : IsCanonH (p + 1) LG) (j : Fin w)
    (M A : ℝ) (tail : Fin w → Bool) (k : GNode LG.garden.tree → Mom d) :
    (treeLeafPolynomial LG p M A tail k j).eval 0 = (directCut LG p j k (M / 2) : ℂ) := by
  rw [← Complex.ofReal_zero, treeLeafPolynomial_eval, directCut, directTopNodes_product hc j]
  push_cast
  apply prod_congr rfl
  intro l _
  cases tail l.1.1 <;> by_cases he : LG.layer l.toNode = p <;> simp [endpointFactor, he]

theorem treeLeafPolynomial_one (hc : IsCanonH (p + 1) LG) (j : Fin w)
    (M A : ℝ) (tail : Fin w → Bool) (ht : tail j = false)
    (k : GNode LG.garden.tree → Mom d) :
    (treeLeafPolynomial LG p M A tail k j).eval 1 = (directCut LG p j k M : ℂ) := by
  rw [← Complex.ofReal_one, treeLeafPolynomial_eval, directCut, directTopNodes_product hc j]
  push_cast
  apply prod_congr rfl
  intro l hl
  rw [(mem_filter.mp hl).2, ht]
  by_cases he : LG.layer l.toNode = p <;> simp [endpointFactor, he]

theorem treeLeafPolynomial_neg_one (hc : IsCanonH (p + 1) LG) (j : Fin w)
    (M A : ℝ) (tail : Fin w → Bool) (ht : tail j = true)
    (k : GNode LG.garden.tree → Mom d) :
    (treeLeafPolynomial LG p M A tail k j).eval (-1) =
      (directCut LG p j k (M / 2) * ∏ l ∈ freeTreeLeaves LG j, chi0 (‖k l.toNode‖ / A) : ℝ) := by
  rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, treeLeafPolynomial_eval,
    directCut, directTopNodes_product hc j]
  push_cast
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro l hl
  rw [(mem_filter.mp hl).2, ht]
  by_cases he : LG.layer l.toNode = p <;> simp [endpointFactor, he]

/-- The three choices are T1, the large-bond part of T2, and the small-bond
part of T2. The latter two use evaluation at -1. -/
def cutChoiceTail (e : Fin 3) : Bool := e ≠ 0
def cutChoiceSmall (e : Fin 3) : Bool := e = 2
def cutChoiceSign (e : Fin 3) : ℝ := if e = 1 then -1 else 1
def cutChoicePoint (e : Fin 3) : ℝ := if e = 0 then 1 else -1

theorem native_tree_extraction (hc : IsCanonH (p + 1) LG) (j : Fin w)
    (L : ℝ) (r : ℕ) (A : ℝ) (hL : 0 < L) (hA : 0 < A)
    (k : GNode LG.garden.tree → Mom d) (hk : IsDecoration LG.garden k)
    (hscale : ((freeTreeLeaves LG j).card : ℝ) * A ≤ (2 ^ (r + 1) * L) / 4) :
    (prodDyadicCut L (r + 1)
      (univ.filter fun a : GNode LG.garden.tree => a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬LG.IsFlowerNode a)
      (fun a => ‖k a‖) : ℂ) =
      ∑ e : Fin 3, (cutChoiceSign e : ℂ) *
        (attachedCut LG p j k (if cutChoiceTail e && cutChoiceSmall e then (2 ^ (r + 1) * L) / 2 else 2 ^ (r + 1) * L) : ℂ) *
        ((treeLeafPolynomial LG p (2 ^ (r + 1) * L) A (fun _ => cutChoiceTail e) k j).eval (cutChoicePoint e : ℂ) -
          (treeLeafPolynomial LG p (2 ^ (r + 1) * L) A (fun _ => cutChoiceTail e) k j).eval 0) := by
  have hhalf : (2 : ℝ) ^ (r + 1) * L / 2 = 2 ^ r * L := by rw [pow_succ]; ring
  have haux := native_T2_auxiliary hc j k hk (by positivity : 0 < 2 ^ (r + 1) * L) hA hscale
  change directCut LG p j k _ * (attachedCut LG p j k _ - attachedCut LG p j k _) = _ at haux
  rw [native_T1_T2 LG p hc j]
  change ((((directCut LG p j k _ - directCut LG p j k _) * attachedCut LG p j k _ +
    directCut LG p j k _ * (attachedCut LG p j k _ - attachedCut LG p j k _)) : ℝ) : ℂ) = _
  rw [Fin.sum_univ_three]
  norm_num [cutChoiceTail, cutChoiceSmall, cutChoiceSign, cutChoicePoint]
  rw [treeLeafPolynomial_one hc j _ _ _ rfl, treeLeafPolynomial_zero hc,
    treeLeafPolynomial_neg_one hc j _ _ _ rfl, treeLeafPolynomial_zero hc]
  rw [hhalf] at haux ⊢
  have hcaux := congrArg (fun x : ℝ => (x : ℂ)) haux
  dsimp only [directCut, attachedCut] at hcaux ⊢
  push_cast at hcaux ⊢
  linear_combination hcaux
end WaveTurbulence.FC23
