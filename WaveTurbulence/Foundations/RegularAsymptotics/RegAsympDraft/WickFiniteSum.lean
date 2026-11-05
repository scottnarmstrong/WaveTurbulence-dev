/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSurvivorAmplitude
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFiniteSupport

/-! # Exact finite-free-vector expansion of a localized Wick correction -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset

/-- Actual local lattice terms on a Wick plane have finite support in
all independent surviving and free variables. -/
theorem summable_wickPattern_halfCell {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d)
    (P : (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) → ℂ) :
    Summable (fun u : WickPatternCoordinates d σ =>
      halfCellAmplitude z β γ (fun j => latticePoint L (wickPatternInsert σ u j).1)
        (fun j => latticePoint L (wickPatternInsert σ u j).2)*P (wickPatternInsert σ u)) := by
  apply summable_halfCell_lattice_pullback hL z β γ
    (fun u => ((fun j => (wickPatternInsert σ u j).1),(fun j => (wickPatternInsert σ u j).2)))
  intro u v huv
  have he : wickPatternInsert σ u = wickPatternInsert σ v := by
    funext j
    exact Prod.ext (congrFun (congrArg Prod.fst huv) j) (congrFun (congrArg Prod.snd huv) j)
  have hh := congrArg (wickPatternExtract σ) he
  simpa only [wickPatternExtract_insert] using hh

/-- The source Wick term is an exact finite sum of surviving oscillatory
sums. All coordinate Fubini steps use actual finite lattice support. -/
theorem tsum_wickPattern_halfCell_eq_sum_free {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d)
    (P : (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) → ℂ) :
    (∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ (fun j => latticePoint L (θ j).1)
        (fun j => latticePoint L (θ j).2)*P θ)) =
      (∏ j, wickPatternCoefficient (σ j)) *
        ∑ v ∈ wickFreeLatticeBox L σ z,
          ∑' a : {j : Fin n // σ j = 0} → (Fin d → ℤ) × (Fin d → ℤ),
            halfCellAmplitude z β γ (fun j => latticePoint L (wickPatternInsert σ (a,v) j).1)
              (fun j => latticePoint L (wickPatternInsert σ (a,v) j).2)*P (wickPatternInsert σ (a,v)) := by
  classical
  rw [tsum_wickPatternTerm_mul]
  congr 1
  have hs := summable_wickPattern_halfCell hL σ z β γ P
  rw [hs.tsum_prod,← hs.tsum_comm]
  apply tsum_eq_sum
  intro v hv
  calc
    _ = ∑' _a : {j : Fin n // σ j = 0} → (Fin d → ℤ) × (Fin d → ℤ), (0:ℂ) := by
      apply tsum_congr
      intro a
      by_cases hW : halfCellAmplitude z β γ
          (fun j => latticePoint L (wickPatternInsert σ (a,v) j).1)
          (fun j => latticePoint L (wickPatternInsert σ (a,v) j).2) = 0
      · rw [hW,zero_mul]
      · exact (hv (mem_wickFreeLatticeBox hL σ z β γ (a,v) hW)).elim
    _ = 0 := tsum_zero

end WaveTurbulence.RegAsymp
