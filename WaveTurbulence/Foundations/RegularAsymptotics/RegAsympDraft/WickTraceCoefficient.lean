/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickPatternSupport
public import WaveTurbulence.Foundations.RegAsymp.EnergyTracePartition

/-! # The actual Wick constraints give the simultaneous coefficient trace -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset Links ApproxNT

/-- A constrained source lattice vector makes its literal energy zero. -/
theorem wickPattern_energy_zero {d n : ℕ}
    (L μ : ℝ) {θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)} {σ : Fin n → Fin 4}
    (h : (∏ j, wickPatternTerm θ j (σ j)) ≠ 0) {j : Fin n} (hj : j ∈ wickTracedLinks σ) :
    μ*inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2) = 0 := by
  rcases wickPattern_zero_coordinate h hj with hx | hy
  · rw [hx]
    have he : latticePoint L (0 : Fin d → ℤ) = 0 := by
      ext i
      simp [latticePoint]
    rw [he,inner_zero_left,mul_zero]
  · rw [hy]
    have he : latticePoint L (0 : Fin d → ℤ) = 0 := by
      ext i
      simp [latticePoint]
    rw [he,inner_zero_right,mul_zero]

/-- Every surviving Wick pattern evaluates exactly the original source
coefficient on its energy zero planes. The special-link exclusion is
proved from the actual resonant profile, rather than assumed separately. -/
theorem wickPattern_energyTraceCoefficient_eq {d n : ℕ}
    (L μ : ℝ) {θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)} {σ : Fin n → Fin 4}
    (h : (∏ j, wickPatternTerm θ j (σ j)) ≠ 0)
    (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (hΨ : resProfile J Ψ (fun j => μ*inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2)) ≠ 0)
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    energyTraceCoefficient (wickTracedLinks σ) J
      (wickTracedLinks_disjoint_special L μ h J Ψ hΨ) C
      (fun j => μ*inner ℝ (latticePoint L (θ j.val).1) (latticePoint L (θ j.val).2)) lam =
      C (fun j => μ*inner ℝ (latticePoint L (θ j.val).1) (latticePoint L (θ j.val).2)) lam := by
  exact energyTraceCoefficient_eq_of_zero (wickTracedLinks σ) J
    (wickTracedLinks_disjoint_special L μ h J Ψ hΨ) C
    (fun j => μ*inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2))
    (fun _ hj => wickPattern_energy_zero L μ h hj) lam

end WaveTurbulence.RegAsymp
