/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerFamily
public import WaveTurbulence.Foundations.FC23.CutSplit
/-! Exact polynomial structure of the proposed flower uniform family at each
source decoration. The degree counts all non-flower endpoints of one tree. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset Polynomial

theorem endpointFactor_affine (p q : ℕ) (tail : Bool) (M A z r : ℝ) :
    endpointFactor p q tail M A z r = endpointFactor p q tail M A 0 r +
      z * (endpointFactor p q tail M A 1 r - endpointFactor p q tail M A 0 r) := by
  cases tail <;> by_cases h : q = p <;> simp only [endpointFactor, h, Bool.false_eq_true, eq_self, ite_true, ite_false] <;> ring

def freeTreeLeaves {w : ℕ} (LG : LayeredGarden w) (j : Fin w) : Finset (GLeaf LG.garden.tree) :=
  (univ.filter fun l => ¬LG.garden.IsFlower l).filter fun l => l.1.1 = j

def treeLeafPolynomial {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (tail : Fin w → Bool) (k : GNode LG.garden.tree → Mom d) (j : Fin w) : ℂ[X] :=
  affineProduct (freeTreeLeaves LG j)
    (fun l => (endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A 0 ‖k l.toNode‖ : ℂ))
    (fun l => (endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A 1 ‖k l.toNode‖ -
      endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A 0 ‖k l.toNode‖ : ℝ))

theorem treeLeafPolynomial_degree {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (tail : Fin w → Bool) (k : GNode LG.garden.tree → Mom d) (j : Fin w) :
    (treeLeafPolynomial LG p M A tail k j).natDegree ≤ (freeTreeLeaves LG j).card :=
  affineProduct_natDegree _ _ _

theorem treeLeafPolynomial_eval {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (tail : Fin w → Bool) (k : GNode LG.garden.tree → Mom d) (j : Fin w) (z : ℝ) :
    (treeLeafPolynomial LG p M A tail k j).eval (z : ℂ) =
      ∏ l ∈ freeTreeLeaves LG j,
        (endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A z ‖k l.toNode‖ : ℂ) := by
  rw [treeLeafPolynomial, affineProduct_eval]
  apply prod_congr rfl
  intro l _
  rw [endpointFactor_affine p (LG.layer l.toNode) (tail l.1.1) M A z ‖k l.toNode‖]
  push_cast
  rfl

/-- Source endpoint products factor into one polynomial for each original tree. -/
theorem treeLeafPolynomial_product {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (M A : ℝ)
    (tail : Fin w → Bool) (k : GNode LG.garden.tree → Mom d) (z : Fin w → ℝ) :
    (∏ j, (treeLeafPolynomial LG p M A tail k j).eval (z j : ℂ)) =
      ∏ l : GLeaf LG.garden.tree, if LG.garden.IsFlower l then 1 else
        (endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A (z l.1.1) ‖k l.toNode‖ : ℂ) := by
  simp_rw [treeLeafPolynomial_eval]
  have he : (∏ j, ∏ l ∈ freeTreeLeaves LG j,
      (endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A (z j) ‖k l.toNode‖ : ℂ)) =
      ∏ j, ∏ l ∈ freeTreeLeaves LG j,
        (endpointFactor p (LG.layer l.toNode) (tail l.1.1) M A (z l.1.1) ‖k l.toNode‖ : ℂ) := by
    apply prod_congr rfl
    intro j _
    apply prod_congr rfl
    intro l hl
    rw [(mem_filter.mp hl).2]
  rw [he]
  unfold freeTreeLeaves
  rw [prod_fiberwise]
  simp only [prod_filter, ite_not]
end WaveTurbulence.FC23
