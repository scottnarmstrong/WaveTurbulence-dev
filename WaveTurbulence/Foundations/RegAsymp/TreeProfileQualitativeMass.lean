/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PhiProfile
public import WaveTurbulence.Foundations.ClassJR.Lemma54a

/-! # Qualitative uniform frequency mass of the original tree profile symbols -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT WithLp

/-- The original qualitative symbol field already provides one integrable majorant
uniform over every active energy. No quantitative remainder estimate is assumed. -/
theorem tree_regular_symbol_uniform_integrable_envelope {ι Γ : Type*} [Fintype ι]
    [MeasureSpace Γ] {C : (ι → ℝ) → Γ → ℂ} (hC : SymReg C) :
    ∃ E : Γ → ℝ, Measurable E ∧ (∀ lam, 0 ≤ E lam) ∧ Integrable E ∧
      ∀ᵐ lam, ∀ α, ‖C α lam‖ ≤ E lam := by
  let E := fun lam => (supD 0 C lam).toReal
  have hm := measurable_supD hC.smooth hC.meas 0
  refine ⟨E, ENNReal.measurable_toReal.comp hm, fun _ => ENNReal.toReal_nonneg,
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable (hC.dom 0),?_⟩
  filter_upwards [ae_lt_top hm (hC.dom 0)] with lam hlam
  intro α
  have h := ENNReal.toReal_mono hlam.ne (dnorm_le_supD 0 C α lam)
  simpa only [dnorm_zero, toReal_enorm] using h

/-- A resonant profile has a uniform scalar bound from the unmarked symbol bound;
its fixed chi-infinity factors remain the literal original factors. -/
theorem tree_resProfile_norm_le {n : ℕ} (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℂ) {E : ℝ}
    (hC : ∀ α, ‖C α‖ ≤ E) (Ω : Fin n → ℝ) :
    ‖resProfile J (fun α => C (ofLp α)) Ω‖ ≤ CPhi^J.card*E := by
  have hp : ‖∏ j ∈ J, ((Fourier.chiInfinity (Ω j)/Ω j:ℝ):ℂ)‖ ≤ CPhi^J.card := by
    rw [norm_prod]
    apply (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun j _ => norm_chiInvR_le (Ω j))).trans_eq
    exact Finset.prod_const _
  rw [resProfile,norm_mul]
  exact mul_le_mul hp (hC _) (norm_nonneg _) (pow_nonneg CPhi_nonneg _)

/-- Every literal regular profile has one integrable temporal envelope uniform in
all physical energies; this is used only to justify exact Fourier exchanges. -/
theorem tree_regular_resProfile_uniform_integrable_envelope {n : ℕ}
    (J : Finset (Fin n)) {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : SymReg C) :
    ∃ E : (ℝ × ℝ) → ℝ, Measurable E ∧ (∀ lam, 0 ≤ E lam) ∧ Integrable E ∧
      ∀ᵐ lam, ∀ Ω, ‖resProfile J (fun α => C (ofLp α) lam) Ω‖ ≤ E lam := by
  obtain ⟨E,hmE,hpE,hiE,hbE⟩ := tree_regular_symbol_uniform_integrable_envelope hC
  refine ⟨fun lam => CPhi^J.card*E lam, measurable_const.mul hmE,
    fun lam => mul_nonneg (pow_nonneg CPhi_nonneg _) (hpE lam),hiE.const_mul _,?_⟩
  filter_upwards [hbE] with lam hlam
  intro Ω
  exact tree_resProfile_norm_le J (fun α => C α lam) hlam Ω

end WaveTurbulence.RegAsymp
