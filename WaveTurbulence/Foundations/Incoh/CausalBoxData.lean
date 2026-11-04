/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalBoxBound

/-!
# Structural parameters of a causal selected-clock kernel

The carrier stores only a balanced frequency tuple and interval endpoints.
There are no norm, mass, or decay fields. It has its ordinary measurable
subtype structure so actual internal-clock parameter maps can be integrated.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Balanced phases and ordered endpoints for two or four selected clocks. -/
abbrev CausalBoxData (m : ℕ) :=
  {p : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ) //
    (∑ j, p.1 j = 0) ∧ p.2.1 ≤ p.2.2}

@[expose] def CausalBoxData.phase {m : ℕ} (p : CausalBoxData m) : Fin (m + 2) → ℝ := p.val.1
@[expose] def CausalBoxData.lower {m : ℕ} (p : CausalBoxData m) : Fin (m + 2) → ℝ := p.val.2.1
@[expose] def CausalBoxData.upper {m : ℕ} (p : CausalBoxData m) : Fin (m + 2) → ℝ := p.val.2.2

theorem CausalBoxData.phase_sum {m : ℕ} (p : CausalBoxData m) : ∑ j, p.phase j = 0 := p.property.1
theorem CausalBoxData.lower_le_upper {m : ℕ} (p : CausalBoxData m) : p.lower ≤ p.upper := p.property.2

@[fun_prop] theorem CausalBoxData.measurable_phase (m : ℕ) : Measurable (CausalBoxData.phase (m := m)) :=
  measurable_fst.comp measurable_subtype_coe
@[fun_prop] theorem CausalBoxData.measurable_lower (m : ℕ) : Measurable (CausalBoxData.lower (m := m)) :=
  (measurable_fst.comp measurable_snd).comp measurable_subtype_coe
@[fun_prop] theorem CausalBoxData.measurable_upper (m : ℕ) : Measurable (CausalBoxData.upper (m := m)) :=
  (measurable_snd.comp measurable_snd).comp measurable_subtype_coe

/-- Bundle the actual phase coefficients and clock endpoints; the proof fields are structural identities. -/
@[expose] def CausalBoxData.ofValues {m : ℕ} (phase a b : Fin (m + 2) → ℝ)
    (hp : ∑ j, phase j = 0) (hab : a ≤ b) : CausalBoxData m := ⟨(phase, a, b), hp, hab⟩

/-- The universal literal causal box family, with every phase and interval choice included. -/
@[expose] def universalCausalBoxKernel (m : ℕ) (χ : ℝ → ℝ)
    (t : Fin 2 → ℝ) (p : CausalBoxData m) : ℂ :=
  causalBoxKernel m χ p.phase p.lower p.upper t

/-- A single mixed Fourier envelope controls all structural selected-clock data. -/
theorem exists_universalCausalBoxKernel_bound (m : ℕ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧
      Fourier.mixedFourierNorm00 (1 / 4) (universalCausalBoxKernel m χ) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := exists_causalBoxKernel_bound m hχ hcχ
  exact ⟨C, hC, hb (CausalBoxData m) CausalBoxData.phase CausalBoxData.lower CausalBoxData.upper
    CausalBoxData.phase_sum CausalBoxData.lower_le_upper⟩

end WaveTurbulence.Incoh
