/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalSymbolEnvelope
public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRestriction
public import WaveTurbulence.Foundations.RegAsymp.RemainderMeasurability

/-! # Actual localized remainders in the source time restriction norm

The supremum over all half-cell centers remains inside the Fourier
integral. The displayed spectral modulation factor is linear in its
first moment and therefore compatible with the leaf spectrum.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT ClassJR WaveTurbulence.Fourier WithLp
open scoped ENNReal

/-- The two J3 coefficient masses, including the fixed positive envelopes. -/
def localCoefficientMass {n : ℕ} (J : Finset (Fin n)) (η N A : ℝ) : ℝ≥0∞ :=
  (((ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
      Fintype.card {j : Fin n // j ∉ J}*ENNReal.ofReal N) +
        ∫⁻ lam, wL (η/4) lam*ENNReal.ofReal (frequencyGaussian lam)) +
    (ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
        ∫⁻ lam, wL (1-η/8) lam*ENNReal.ofReal (frequencyGaussian lam)))

/-- The literal normalized cell remainder as a source frequency density. -/
def localRemainder {d n : ℕ} (L δ γ : ℝ) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (β γ' : Fin n → Mom d) (lam : ℝ × ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) : ℂ :=
  (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    (approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J (fun Ω => C (ofLp Ω) lam)) -
      approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ'))

end WaveTurbulence.RegAsymp
