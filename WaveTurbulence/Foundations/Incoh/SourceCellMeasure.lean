/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralMassBound
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The actual countable localization/spectral measure

Leaf-cell arrays are countable, the selected link-cell arrays are finite
in each fiber, and each has the same literal spectral Lebesgue measure.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual selected source cell indices, retaining their original integer centers. -/
abbrev SourceCellIndex {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) : Type :=
  Σ c : Fin m → Fin d → ℤ, {z : (Fin n × Fin 2) → Fin d → ℤ // z ∈ S c}

instance {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    MeasurableSpace (SourceCellIndex S) := ⊤

instance {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    MeasurableSingletonClass (SourceCellIndex S) := ⟨fun _ => trivial⟩

/-- Counting the actual selected cells, with the literal spectral Lebesgue measure. -/
@[expose] def sourceCellMeasure {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    Measure (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) :=
  Measure.count.prod volume

instance {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    SigmaFinite (sourceCellMeasure S) := by
  unfold sourceCellMeasure
  infer_instance

/-- Counting the actual selected cell index yields its literal finite fiber multiplicity. -/
theorem tsum_sourceCellIndex {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (a : (Fin m → Fin d → ℤ) → ℝ≥0∞) :
    (∑' u : SourceCellIndex S, a u.1) = ∑' c : Fin m → Fin d → ℤ, (S c).card * a c := by
  classical
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro c
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-- Tonelli computes the exact spectral mass, with the actual finite link-cell multiplicity. -/
theorem lintegral_sourceCellMeasure {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (E : (Fin m → Fin d → ℤ) → (LocalizedCellIndex n m → Fin d → ℝ) → ℝ≥0∞)
    (hE : ∀ c, Measurable (E c)) :
    (∫⁻ u, E u.1.1 u.2 ∂sourceCellMeasure S) =
      ∑' c : Fin m → Fin d → ℤ, (S c).card * ∫⁻ ξ, E c ξ := by
  classical
  have hm : Measurable (fun u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ) =>
      E u.1.1 u.2) := measurable_from_prod_countable_right (fun u => hE u.1)
  rw [sourceCellMeasure, lintegral_prod _ hm.aemeasurable, lintegral_count]
  change (∑' a : Σ c : Fin m → Fin d → ℤ,
    {z : (Fin n × Fin 2) → Fin d → ℤ // z ∈ S c}, ∫⁻ ξ, E a.1 ξ) = _
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro c
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end WaveTurbulence.Incoh
