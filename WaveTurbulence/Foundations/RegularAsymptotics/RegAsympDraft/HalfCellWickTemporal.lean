/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalLocalSymbol
import Mathlib.Data.Finset.Preimage

/-! # Actual squared-Wick lattice sum and temporal profile integral commute on each half cell -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links ClassJR WithLp

/-- The exact squared-Wick half-cell lattice term is the temporal Fourier
integral of its original weighted NT profile. Its physical finite support
is fixed before the coefficient and spectral frequencies are chosen. -/
theorem halfCell_wick_temporal_interchange {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (μ t s : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (J : Finset (Fin n)) {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    (∑' θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
      (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
        halfCellAmplitude z β γ (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2))*
      ∫ lam, resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L μ θ)*e2 lam t s) =
    ∫ lam, (∑' θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
      (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
        halfCellAmplitude z β γ (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2))*
        resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L μ θ))*e2 lam t s := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let T := (halfCellArrayLatticeBox L z).preimage E E.injective.injOn
  apply tsum_integral_resProfile_e2 T _ _ J hC
  intro θ hθ
  by_contra hn
  have hh := (mul_ne_zero_iff.mp hn).2
  apply hθ
  apply Finset.mem_preimage.mpr
  exact mem_halfCellArrayLatticeBox hL z β γ (E θ) hh

/-- Retaining the original physical normalization gives precisely the
frequency density physicalWeightedCellSymbol, including the empty order. -/
theorem physicalWeightedCellSymbol_temporal_interchange {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (δ γ t s : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      (∑' θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
        (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
          halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2))*
        ∫ lam, resProfile J (fun Ω => C (ofLp Ω) lam)
          (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam t s) =
    ∫ lam, physicalWeightedCellSymbol L δ γ z β γ' J C lam*e2 lam t s := by
  rw [halfCell_wick_temporal_interchange hL (L^(2*γ)*(2*δ)) t s z β γ' J hC,
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro lam
  dsimp only
  unfold physicalWeightedCellSymbol
  simp only [mul_assoc]

end WaveTurbulence.RegAsymp
