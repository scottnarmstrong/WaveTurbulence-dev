/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerPolynomial
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts
/-! Finite original-tree order slices of the literal flower carrier. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset

def flowerCarrier (P : WTParams) (p N : ℕ) {w : ℕ} (kind : FlowerKind)
    (pat : Fin w → FixPat) (ζ : ℤˣ) : Set (LayeredGarden w) :=
  {LG | IsCanonH (p + 1) LG ∧
    (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
    LG.FlowerKindOK p (P.N (p + 1)) kind ∧
    (∀ l : GLeaf LG.garden.tree, LG.garden.IsFlower l →
      LG.garden.sign l.toNode = ζ * LG.garden.sig l.1.1) ∧
    ∀ j, LG.PatValid p j (pat j)}

theorem flowerCarrier_finite (P : WTParams) (p N : ℕ) {w : ℕ} (kind : FlowerKind)
    (pat : Fin w → FixPat) (ζ : ℤˣ) : (flowerCarrier P p N kind pat ζ).Finite :=
  (Canon.finite_canonH (p + 1) N w).subset fun _ h => ⟨h.1, h.2.2.1.le⟩

def flowerKernel (P : WTParams) (F : ℕ → Mom P.d → ℝ) (_p : ℕ) {w : ℕ}
    (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (t s : ℝ) (n n' : Fin P.d → ℤ) (LG : LayeredGarden w) : ℂ :=
  kernelKgen P.L P.γ P.δ F LG (LG.fixPat pat t s)
    (if dagger.isSome then univ.filter LG.garden.IsFlowerParent else ∅)
    (fun k => weight LG k * (dagger.elim 1 fun c => LG.sibWeight c k))
    (fun _ => t) 0 (fun _ => n) n'

theorem flowerWeighted_eq_sum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    flowerWeighted P F p N kind pat dagger weight ζ t s n n' =
      ∑ LG ∈ (flowerCarrier_finite P p N kind pat ζ).toFinset,
        flowerKernel P F p pat dagger weight t s n n' LG := by
  rw [← finsum_mem_eq_finite_toFinset_sum]
  rfl

/-- The original-tree total orders, not merely their top-layer orders. -/
def originalOrders {w : ℕ} (LG : LayeredGarden w) : Fin w → ℕ :=
  fun j => (LG.garden.tree j).order

def flowerOrderSlices (N w : ℕ) : Finset (Fin w → ℕ) :=
  (Fintype.piFinset fun _ : Fin w => range (N + 1)).filter fun σ => ∑ j, σ j = N

theorem originalOrders_mem {w N : ℕ} (LG : LayeredGarden w) (hN : LG.garden.order = N) :
    originalOrders LG ∈ flowerOrderSlices N w := by
  apply mem_filter.mpr
  refine ⟨?_, hN⟩
  rw [Fintype.mem_piFinset]
  intro j
  apply mem_range.mpr
  have hj : (LG.garden.tree j).order ≤ LG.garden.order :=
    single_le_sum (f := fun j => (LG.garden.tree j).order) (fun _ _ => Nat.zero_le _) (mem_univ j)
  change (LG.garden.tree j).order < N + 1
  omega

theorem flowerOrderSlices_card_le (N w : ℕ) :
    (flowerOrderSlices N w).card ≤ (N + 1) ^ w := by
  apply (card_filter_le _ _).trans_eq
  simp only [Fintype.card_piFinset, card_range, prod_const, card_univ, Fintype.card_fin]

/-- Exact finite slicing of `flowerWeighted`; no estimates or cancellation
claims are introduced by this identity. -/
theorem flowerWeighted_order_slices (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    flowerWeighted P F p N kind pat dagger weight ζ t s n n' =
      ∑ σ ∈ flowerOrderSlices N w,
        ∑ LG ∈ (flowerCarrier_finite P p N kind pat ζ).toFinset.filter
          (fun LG => originalOrders LG = σ), flowerKernel P F p pat dagger weight t s n n' LG := by
  rw [flowerWeighted_eq_sum]
  exact (sum_fiberwise_of_maps_to (fun LG hLG => originalOrders_mem LG
    ((flowerCarrier_finite P p N kind pat ζ).mem_toFinset.mp hLG).2.2.1) _).symm

/-- A slice's interpolation degrees are positive, with total `2N+w`. -/
def orderSliceDegree {w : ℕ} (σ : Fin w → ℕ) (j : Fin w) : ℕ := 2 * σ j + 1

theorem orderSliceDegree_pos {w : ℕ} (σ : Fin w → ℕ) (j : Fin w) :
    0 < orderSliceDegree σ j := by unfold orderSliceDegree; omega

theorem orderSliceDegree_sum {N w : ℕ} {σ : Fin w → ℕ} (hσ : σ ∈ flowerOrderSlices N w) :
    ∑ j, orderSliceDegree σ j = 2 * N + w := by
  have hs := (mem_filter.mp hσ).2
  simp only [orderSliceDegree, sum_add_distrib, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, hs]

theorem freeTreeLeaves_card_le {w : ℕ} (LG : LayeredGarden w) (j : Fin w) :
    (freeTreeLeaves LG j).card ≤ 2 * (LG.garden.tree j).order + 1 := by
  rw [← Comb.card_leaves]
  apply card_le_card_of_injOn (fun l : GLeaf LG.garden.tree => l.1.2)
  · intro l hl
    have hj := (mem_filter.mp hl).2
    change l.1.2 ∈ (LG.garden.tree j).leaves
    simpa only [hj] using l.2
  · intro l hl l' hl' he
    have hj := (mem_filter.mp hl).2
    have hj' := (mem_filter.mp hl').2
    apply Subtype.ext
    exact Prod.ext (hj.trans hj'.symm) he

theorem treeLeafPolynomial_slice_degree {w d : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (M A : ℝ) (tail : Fin w → Bool) (k : GNode LG.garden.tree → Mom d)
    {σ : Fin w → ℕ} (hσ : originalOrders LG = σ) (j : Fin w) :
    (treeLeafPolynomial LG p M A tail k j).natDegree ≤ orderSliceDegree σ j := by
  apply (treeLeafPolynomial_degree LG p M A tail k j).trans
  simpa only [orderSliceDegree, ← hσ, originalOrders] using freeTreeLeaves_card_le LG j
end WaveTurbulence.FC23
