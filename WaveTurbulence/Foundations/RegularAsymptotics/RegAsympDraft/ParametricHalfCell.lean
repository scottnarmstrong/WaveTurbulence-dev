/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellAmplitudeSupport
public import WaveTurbulence.Foundations.RegAsymp.ParametricSingularIntegral

/-! # The actual half-cell singular integral is measurable in its modulations -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Incoh
open scoped ENNReal

/-- Joint continuity includes every spatial modulation and integration variable. -/
theorem continuous_halfCellAmplitude_joint {d n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ) :
    Continuous (fun p : ((Fin n → Mom d) × (Fin n → Mom d)) ×
      ((Fin n → Mom d) × (Fin n → Mom d)) => halfCellAmplitude z p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold halfCellAmplitude
  apply Continuous.mul
  · apply continuous_finsetProd
    intro j _
    have hb : Continuous (fun p : ((Fin n → Mom d) × (Fin n → Mom d)) × ((Fin n → Mom d) × (Fin n → Mom d)) => p.1.1 j) := by fun_prop
    have hx : Continuous (fun p : ((Fin n → Mom d) × (Fin n → Mom d)) × ((Fin n → Mom d) × (Fin n → Mom d)) => p.2.1 j) := by fun_prop
    exact (Real.continuous_fourierChar.comp (hb.inner hx)).smul
      ((contDiff_halfLinkCell (z (j,0))).continuous.comp hx)
  · apply continuous_finsetProd
    intro j _
    have hb : Continuous (fun p : ((Fin n → Mom d) × (Fin n → Mom d)) × ((Fin n → Mom d) × (Fin n → Mom d)) => p.1.2 j) := by fun_prop
    have hx : Continuous (fun p : ((Fin n → Mom d) × (Fin n → Mom d)) × ((Fin n → Mom d) × (Fin n → Mom d)) => p.2.2 j) := by fun_prop
    exact (Real.continuous_fourierChar.comp (hb.inner hx)).smul
      ((contDiff_halfLinkCell (z (j,1))).continuous.comp hx)

/-- The actual modulated compact amplitude has ordinary Fourier inversion. -/
theorem halfCellAmplitude_fourier_setup {d n : ℕ} (hn : 0 < n)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d) :
    Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      fourierW (halfCellAmplitude z β γ) τ.1 τ.2) ∧
    ∀ x y, halfCellAmplitude z β γ x y =
      ∫ τ, fourierW (halfCellAmplitude z β γ) τ.1 τ.2*wPhase x y τ := by
  let H := (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖)))*halfLinkFirstMomentConstant d^(2*n)
  have hD := (halfLinkFirstMomentConstant_pos d).le
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hW : (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW (halfCellAmplitude z β γ) τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H := by
    apply (halfCellAmplitude_fourier_budget z β γ).trans_eq
    dsimp only [H]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (halfLinkFirstMomentConstant_pos d).le]
    exact (mul_assoc _ _ _).symm
  obtain ⟨hF,hi,-,-⟩ := fourierAmplitude_setup (lt := fun i j : Fin n => i<j) hn
    (xs := fun _ => .zero) (ys := fun _ => .zero) (fun _ => trivial) (fun _ => trivial)
    (continuous_halfCellAmplitude z β γ) (halfCellAmplitude_support z β γ) hH hW
  exact ⟨hF,hi⟩

/-- Measurability of the literal singular operator, rather than of a substituted model. -/
theorem stronglyMeasurable_singInt_halfCellAmplitude {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (J : Finset (Fin n)) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (Fin n → Mom d) × (Fin n → Mom d) =>
      singInt J (halfCellAmplitude z p.1 p.2)) := by
  exact stronglyMeasurable_singInt_fixed_support (lt := fun i j : Fin n => i<j) hd J
    (xs := fun _ => .zero) (ys := fun _ => .zero) (fun _ => trivial) (fun _ => trivial)
    (continuous_halfCellAmplitude_joint z).stronglyMeasurable
    (fun p => halfCellAmplitude_support z p.1 p.2)
    (fun p => (halfCellAmplitude_fourier_setup hn z p.1 p.2).1)
    (fun p => (halfCellAmplitude_fourier_setup hn z p.1 p.2).2)

end WaveTurbulence.RegAsymp
