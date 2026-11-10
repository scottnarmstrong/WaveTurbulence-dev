/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeHalfCellLatticeExchange

/-! # Exact original local tree lattice profiles as leaf and time Fourier mixtures -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh ClassJR ApproxNT WithLp

/-- An arbitrary original Wick weight preserves finite-support temporal Fubini. -/
theorem halfCell_weighted_temporal_interchange {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (μ t s : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (H : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (J : Finset (Fin n)) {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
      (halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*H g)*
        ∫ lam, resProfile J (fun Ω => C (ofLp Ω) lam)
          (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s) =
      ∫ lam, (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
        (halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
          (fun j => latticePoint L (g.2 j))*H g)*
          resProfile J (fun Ω => C (ofLp Ω) lam)
            (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j))))*e2 lam t s := by
  apply tsum_integral_resProfile_e2 (halfCellArrayLatticeBox L z)
  · intro g hg
    have hz : halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j)) = 0 := by
      by_contra hn
      exact hg (mem_halfCellArrayLatticeBox hL z β γ g hn)
    rw [hz, zero_mul]
  · exact hC

end WaveTurbulence.RegAsymp
