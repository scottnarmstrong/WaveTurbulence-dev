/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellLatticeCount
public import WaveTurbulence.Foundations.RegAsymp.FiniteProfileInterchange
public import Mathlib.Data.Fintype.Pi

/-! # Actual finite lattice support and temporal Fourier interchange of half cells -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh ApproxNT ClassJR WithLp

/-- The actual finite support box for all independent x/y lattice variables. -/
def halfCellArrayLatticeBox {d n : ℕ} (L : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    Finset ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) :=
  (Fintype.piFinset (fun j => halfCellLatticeBox L (z (j,0)))).product
    (Fintype.piFinset (fun j => halfCellLatticeBox L (z (j,1))))

/-- Modulation does not enlarge the actual finite lattice support. -/
theorem mem_halfCellArrayLatticeBox {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ))
    (hg : halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
      (fun j => latticePoint L (g.2 j)) ≠ 0) : g ∈ halfCellArrayLatticeBox L z := by
  have hp := mul_ne_zero_iff.mp hg
  apply Finset.mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro j
    apply mem_halfCellLatticeBox hL
    have hj := Finset.prod_ne_zero_iff.mp hp.1 j (Finset.mem_univ j)
    intro hc
    exact hj (by rw [hc,smul_zero])
  · apply Fintype.mem_piFinset.mpr
    intro j
    apply mem_halfCellLatticeBox hL
    have hj := Finset.prod_ne_zero_iff.mp hp.2 j (Finset.mem_univ j)
    intro hc
    exact hj (by rw [hc,smul_zero])

/-- The actual local unmasked lattice term is the temporal Fourier
integral of the exact NT sum, justified by its actual finite support. -/
theorem halfCell_approxSum_temporal_interchange {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (μ t s : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (J : Finset (Fin n)) {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
      halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j))*
        ∫ lam, resProfile J (fun Ω => C (ofLp Ω) lam)
          (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s) =
      ∫ lam, approxSum L μ (halfCellAmplitude z β γ)
        (resProfile J (fun Ω => C (ofLp Ω) lam))*e2 lam t s := by
  apply tsum_integral_resProfile_e2 (halfCellArrayLatticeBox L z)
    (fun g => halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
      (fun j => latticePoint L (g.2 j))) _ J hC
  intro g hg
  by_contra hn
  exact hg (mem_halfCellArrayLatticeBox hL z β γ g hn)

end WaveTurbulence.RegAsymp
