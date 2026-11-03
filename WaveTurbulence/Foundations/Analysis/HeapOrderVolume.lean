/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.PermutationChambers

/-!
# The linear-extension formula for heap-ordered volumes

For a relation `R` on `Fin n`, `R i j` means that coordinate `i` must be
larger than coordinate `j`. This includes the ancestor order of a rooted
tree or forest. No tree-specific carrier is needed for the volume formula.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- The region in `[0,D]^n` respecting a prescribed strict ordering relation. -/
@[expose] def heapOrderRegion {n : ℕ} (R : Fin n → Fin n → Prop) (D : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, x i ∈ Icc 0 D) ∧ ∀ i j, R i j → x j < x i}

/-- Permutations listing the coordinates from largest to smallest and
respecting `R`. For a tree order these are its linear extensions. -/
@[expose] noncomputable def linearExtensions {n : ℕ} (R : Fin n → Fin n → Prop) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter fun σ => ∀ i j, R i j → σ.symm i < σ.symm j

theorem mem_linearExtensions {n : ℕ} (R : Fin n → Fin n → Prop) (σ : Equiv.Perm (Fin n)) :
    σ ∈ linearExtensions R ↔ ∀ i j, R i j → σ.symm i < σ.symm j := by
  classical
  simp only [linearExtensions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Outside coordinate coincidences, the heap-order region is partitioned
by the chambers of its linear extensions. -/
theorem heapOrderRegion_ae_eq_chambers {n : ℕ} (R : Fin n → Fin n → Prop) (D : ℝ) :
    heapOrderRegion R D =ᵐ[volume] ⋃ σ ∈ linearExtensions R, strictOrderChamber D σ := by
  classical
  filter_upwards [ae_injective_coordinates n] with x hx
  apply propext
  change ((∀ i, x i ∈ Icc 0 D) ∧ ∀ i j, R i j → x j < x i) ↔ _
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hb, hR⟩
    let σ := Tuple.sort (fun i => OrderDual.toDual (x i))
    have ha : Antitone (x ∘ σ) := by
      intro i j hij
      exact Tuple.monotone_sort (fun i => OrderDual.toDual (x i)) hij
    have hs : StrictAnti (x ∘ σ) := ha.strictAnti_of_injective (hx.comp σ.injective)
    have he : σ ∈ linearExtensions R := by
      apply (mem_linearExtensions R σ).mpr
      intro i j hij
      apply hs.lt_iff_gt.mp
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hR i j hij
    exact ⟨σ, he, hb, hs⟩
  · rintro ⟨σ, hσ, hb, hs⟩
    refine ⟨hb, ?_⟩
    intro i j hij
    have hh := hs ((mem_linearExtensions R σ).mp hσ i j hij)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh

/-- TARGET L2029–2036: the volume of a heap-ordered domain is the number
of linear extensions times the volume of one standard simplex. This is
valid for every relation, hence in particular for all finite tree orders. -/
theorem volume_heapOrderRegion {n : ℕ} (R : Fin n → Fin n → Prop) {D : ℝ} (hD : 0 ≤ D) :
    volume (heapOrderRegion R D) = (linearExtensions R).card *
      ENNReal.ofReal (D ^ n / (Nat.factorial n : ℝ)) := by
  classical
  rw [measure_congr (heapOrderRegion_ae_eq_chambers R D),
    measure_biUnion_finset (fun σ _ τ _ hστ => disjoint_strictOrderChamber D hστ)
      (fun σ _ => measurableSet_strictOrderChamber D σ)]
  simp only [volume_strictOrderChamber hD, Finset.sum_const, nsmul_eq_mul]

end WaveTurbulence.Analysis
