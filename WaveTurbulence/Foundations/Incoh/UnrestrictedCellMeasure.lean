/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceCellMeasure

/-!
# A fixed measure for momentum-dependent source cell selections

All integer cell pairs are counted. A finite selection is retained as an
actual indicator in the amplitude, permitting its support to depend on
root momentum while the integration measure stays fixed.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- All actual integer leaf/link cell pairs, before selecting their finite active fibers. -/
abbrev UnrestrictedCellIndex (d n m : ℕ) :=
  (Fin m → Fin d → ℤ) × ((Fin n × Fin 2) → Fin d → ℤ)

/-- Fixed counting/Lebesgue measure, independent of every root momentum and selection. -/
@[expose] def unrestrictedCellMeasure (d n m : ℕ) :
    Measure (UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) :=
  Measure.count.prod volume

instance (d n m : ℕ) : SigmaFinite (unrestrictedCellMeasure d n m) := by
  unfold unrestrictedCellMeasure
  infer_instance

/-- The literal mass of a finite cell-selection indicator, on the fixed common measure. -/
theorem lintegral_unrestrictedCellMeasure_indicator {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (E : (Fin m → Fin d → ℤ) → (LocalizedCellIndex n m → Fin d → ℝ) → ℝ≥0∞)
    (hE : ∀ c, Measurable (E c)) :
    (∫⁻ u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ),
      (if u.1.2 ∈ S u.1.1 then E u.1.1 u.2 else 0) ∂unrestrictedCellMeasure d n m) =
      ∑' c : Fin m → Fin d → ℤ, (S c).card * ∫⁻ ξ, E c ξ := by
  classical
  have hm : Measurable (fun u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ) =>
      if u.1.2 ∈ S u.1.1 then E u.1.1 u.2 else 0) := by
    apply measurable_from_prod_countable_right
    intro u
    dsimp only
    split_ifs
    · exact hE u.1
    · exact measurable_const
  rw [unrestrictedCellMeasure, lintegral_prod _ hm.aemeasurable, lintegral_count]
  have he (u : UnrestrictedCellIndex d n m) :
      (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        if u.2 ∈ S u.1 then E u.1 ξ else 0) =
      if u.2 ∈ S u.1 then ∫⁻ ξ, E u.1 ξ else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro c
  rw [tsum_eq_sum (s := S c) (fun z hz => by rw [ite_eq_right hz])]
  calc
    _ = ∑ _z ∈ S c, ∫⁻ ξ, E c ξ := Finset.sum_congr rfl (fun z hz => ite_eq_left hz)
    _ = _ := by simp

end WaveTurbulence.Incoh
