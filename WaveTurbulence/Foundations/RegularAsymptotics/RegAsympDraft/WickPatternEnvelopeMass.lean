/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSliceEnvelope
public import WaveTurbulence.Foundations.RegAsymp.WickTraceMass

/-! # Actual finite families of admissible Wick source envelopes -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR Finset
open scoped ENNReal

/-- Only nontrivial patterns avoiding special energies survive. -/
def wickAdmissiblePatterns {n : ℕ} (J : Finset (Fin n)) : Finset (Fin n → Fin 4) :=
  (univ.erase 0).filter (fun σ => Disjoint (wickTracedLinks σ) J)

theorem card_wickAdmissiblePatterns_le {n : ℕ} (J : Finset (Fin n)) :
    (wickAdmissiblePatterns J).card ≤ 4^n :=
  card_filter_le _ _ |>.trans (wick_patterns_card_le n)

/-- The codimension power scales each actual coefficient normalizer once. -/
def scaledWickEnvelope {n : ℕ} (d : ℕ) (L γ : ℝ) (J : Finset (Fin n))
    (g : {σ // σ ∈ wickAdmissiblePatterns J} → (ℝ × ℝ) → ℝ) (lam : ℝ × ℝ) : ℝ :=
  ∑ σ, (L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card * g σ lam

theorem measurable_scaledWickEnvelope {n : ℕ} (d : ℕ) (L γ : ℝ) (J : Finset (Fin n))
    (g : {σ // σ ∈ wickAdmissiblePatterns J} → (ℝ × ℝ) → ℝ)
    (hg : ∀ σ, Measurable (g σ)) : Measurable (scaledWickEnvelope d L γ J g) := by
  unfold scaledWickEnvelope
  apply Finset.measurable_sum
  intro σ _
  exact measurable_const.mul (hg σ)

theorem scaledWickEnvelope_nonneg {n : ℕ} (d : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (γ : ℝ) (J : Finset (Fin n))
    (g : {σ // σ ∈ wickAdmissiblePatterns J} → (ℝ × ℝ) → ℝ)
    (hg : ∀ σ lam, 0 ≤ g σ lam) (lam : ℝ × ℝ) : 0 ≤ scaledWickEnvelope d L γ J g lam := by
  apply sum_nonneg
  intro σ _
  exact mul_nonneg (pow_nonneg (Real.rpow_nonneg hL _) _) (hg σ lam)

/-- The literal finite source envelope has the sum of its scaled masses. -/
theorem lintegral_scaledWickEnvelope {n : ℕ} (d : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (γ θ : ℝ) (J : Finset (Fin n))
    (g : {σ // σ ∈ wickAdmissiblePatterns J} → (ℝ × ℝ) → ℝ)
    (hgm : ∀ σ, Measurable (g σ)) (hgn : ∀ σ lam, 0 ≤ g σ lam) :
    (∫⁻ lam, wL θ lam*ENNReal.ofReal (scaledWickEnvelope d L γ J g lam)) =
      ∑ σ, ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card)*
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g σ lam)) := by
  have he (lam : ℝ × ℝ) : ENNReal.ofReal (scaledWickEnvelope d L γ J g lam) =
      ∑ σ, ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card)*ENNReal.ofReal (g σ lam) := by
    unfold scaledWickEnvelope
    rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ =>
      mul_nonneg (pow_nonneg (Real.rpow_nonneg hL _) _) (hgn σ lam))]
    apply sum_congr rfl
    intro σ _
    exact ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg hL _) _)
  simp_rw [he,Finset.mul_sum]
  rw [lintegral_finsetSum (f := fun σ lam => wL θ lam*
    (ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card)*ENNReal.ofReal (g σ lam)))
    univ (fun σ _ => (measurable_wL θ).mul
      (measurable_const.mul (ENNReal.measurable_ofReal.comp (hgm σ))))]
  apply sum_congr rfl
  intro σ _
  calc
    _ = ∫⁻ lam, ENNReal.ofReal ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card)*
        (wL θ lam*ENNReal.ofReal (g σ lam)) := by
      apply lintegral_congr
      intro lam
      ring
    _ = _ := lintegral_const_mul _ ((measurable_wL θ).mul (ENNReal.measurable_ofReal.comp (hgm σ)))

/-- Every actual admissible pattern keeps the source decay after its
individual trace cost; the finite family costs at most4^n. -/
theorem lintegral_scaledWickEnvelope_le {d n : ℕ} (hd : 3 ≤ d) {L γ : ℝ}
    (hL : 1 ≤ L) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (θ : ℝ) (J : Finset (Fin n))
    (g : {σ // σ ∈ wickAdmissiblePatterns J} → (ℝ × ℝ) → ℝ)
    (hgm : ∀ σ, Measurable (g σ)) (hgn : ∀ σ lam, 0 ≤ g σ lam)
    (cost : {σ // σ ∈ wickAdmissiblePatterns J} → ℝ) (H G : ℝ≥0∞)
    (hcost : ∀ σ, cost σ ≤ L^(((wickTracedLinks σ.val).card:ℝ)/4))
    (hmass : ∀ σ, (∫⁻ lam, wL θ lam*ENNReal.ofReal (g σ lam)) ≤ ENNReal.ofReal (cost σ)*H+G) :
    (∫⁻ lam, wL θ lam*ENNReal.ofReal (scaledWickEnvelope d L γ J g lam)) ≤
      (4:ℝ≥0∞)^n*ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ))*(H+G) := by
  rw [lintegral_scaledWickEnvelope d (zero_le_one.trans hL) γ θ J g hgm hgn]
  calc
    _ ≤ ∑ σ : {σ // σ ∈ wickAdmissiblePatterns J},
        ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ))*(H+G) := by
      apply sum_le_sum
      intro σ _
      have hσ : σ.val ≠ 0 := (mem_erase.mp (mem_filter.mp σ.property).1).1
      have hr : 1 ≤ (wickTracedLinks σ.val).card := card_pos.mpr (wickTracedLinks_nonempty hσ)
      exact (mul_le_mul' le_rfl (hmass σ)).trans
        (wick_weighted_trace_mass_budget hd hL hγ hr (hcost σ) H G)
    _ = ((wickAdmissiblePatterns J).card:ℝ≥0∞)*
        (ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ))*(H+G)) := by simp
    _ ≤ (4:ℝ≥0∞)^n*(ENNReal.ofReal (L^(-ApproxNT.gamma1 d γ))*(H+G)) := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast card_wickAdmissiblePatterns_le J
    _ = _ := by ring

end WaveTurbulence.RegAsymp
