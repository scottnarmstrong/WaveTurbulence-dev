/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CoordinateInsertion

/-! # The literal coefficient symbol with one energy variable frozen at zero -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WithLp
open scoped ContDiff ENNReal

/-- Insert one fixed energy coordinate among the coefficient variables. -/
def optionInsert {ι : Type} (r : ℝ) (β : ι → ℝ) : Option ι → ℝ :=
  fun o => match o with | none => r | some i => β i

/-- The trace appearing when a non-special link has a zero coordinate. -/
def traceSymbol {ι Γ : Type} (C : (Option ι → ℝ) → Γ → ℂ) (β : ι → ℝ) (lam : Γ) : ℂ :=
  C (optionInsert 0 β) lam

/-- The source ℓ¹ derivative norm contracts under this trace. -/
theorem dnorm_traceSymbol_le {ι Γ : Type} [Fintype ι]
    {C : (Option ι → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k : ℕ) (β : ι → ℝ) :
    dnorm k (traceSymbol C) β lam ≤ dnorm k C (optionInsert 0 β) lam := by
  have hh := norm_iteratedFDeriv_optionZero_le (contDiff_lift1 hs) k (toLp 1 β)
  have he : lift1 (traceSymbol C) lam = lift1 C lam ∘ optionZeroL1 := rfl
  unfold dnorm
  rw [he,← ofReal_norm,← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hh

/-- Joint source symbol regularity survives a one-coordinate trace. -/
theorem symReg_traceSymbol {ι Γ : Type} [Fintype ι] [MeasureSpace Γ]
    {C : (Option ι → ℝ) → Γ → ℂ} (hC : SymReg C) : SymReg (traceSymbol C) where
  smooth lam := (hC.smooth lam).comp (by
    apply contDiff_pi.mpr
    intro i
    cases i <;> fun_prop [optionInsert])
  meas := by
    have hm : Measurable (fun p : (ι → ℝ) × Γ => (optionInsert 0 p.1,p.2)) := by
      apply Measurable.prodMk _ measurable_snd
      apply measurable_pi_iff.mpr
      intro i
      cases i <;> fun_prop [optionInsert]
    exact hC.meas.comp_measurable hm
  dom k := by
    apply ne_top_of_le_ne_top (hC.dom k)
    apply lintegral_mono
    intro lam
    apply iSup_le
    intro β
    exact (dnorm_traceSymbol_le (hC.smooth lam) k β).trans (dnorm_le_supD k C _ lam)

end WaveTurbulence.RegAsymp
