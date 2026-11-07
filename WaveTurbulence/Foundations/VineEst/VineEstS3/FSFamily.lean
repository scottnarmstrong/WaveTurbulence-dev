/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSDeriv
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSCoeff
public import WaveTurbulence.Foundations.Sumint.MultiIndices

/-! # A good representative of the frequency family of an extension (B2, step 6a)

For an extension `G` with `XNorm θ Λ₁ Λ₂ G < ⊤` (`Λ₁ ≠ 0`, `θ ≥ 0`), the transform family `λ ↦ timeFT G λ`
is modified on a null set to a family `Φ` that is `C^{Λ₁}` in the momentum for every `λ`, has finite
word envelopes `wenv`, and whose weighted envelope integrals are bounded by `XNorm`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.FS
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.NormBridgeScratch MeasureTheory Set Filter
open scoped ENNReal ContDiff

variable {r d : ℕ}

theorem wenv_zero (Λ₂ : ℕ) {n : ℕ} (σ : Fin n → Fin d) : wenv Λ₂ σ (fun _ : Mom d => (0 : ℂ)) = 0 := by
  unfold wenv momentumDerivative
  cases n with
  | zero => simp
  | succ n => simp

/-- A word envelope of the transform is bounded by the integrand of `XNorm`. -/
theorem wenv_eq_iSup (Λ₂ : ℕ) {n : ℕ} (σ : Fin n → Fin d) {f : Mom d → ℂ} (hf : ContDiff ℝ n f) :
    wenv Λ₂ σ f = ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ *
      ‖iterPartial (fun j => (List.ofFn σ).count j) f k‖) := by
  unfold wenv
  rw [NormBridgeScratch.momentumDerivative_eq_iterPartial_counts σ hf]
  rfl

theorem lintegral_wenv_le_XNorm {J : ℕ} (θ : ℝ) (Λ₂ : ℕ) (G : (Fin r → ℝ) → Mom d → ℂ)
    (h : (∀ k, Integrable fun t => G t k) ∧ (J = 0 ∨ ∀ᵐ lam, ContDiff ℝ J (timeFT G lam)))
    {n : ℕ} (hn : n ≤ J) (σ : Fin n → Fin d) {Ψ : (Fin r → ℝ) → Mom d → ℂ}
    (hΨ : ∀ᵐ lam, Ψ lam = timeFT G lam) (hJ : J ≠ 0) :
    ∫⁻ lam, maxBracketPow θ lam * wenv Λ₂ σ (Ψ lam) ≤ XNorm θ J Λ₂ G := by
  have hsm := h.2.resolve_left hJ
  unfold XNorm
  rw [ite_eq_left h]
  refine le_iSup₂_of_le (fun j => (List.ofFn σ).count j) ?_ ?_
  · simp only [NormBridgeScratch.sum_counts, List.length_ofFn]; exact hn
  · refine le_of_eq (lintegral_congr_ae ?_)
    filter_upwards [hsm, hΨ] with lam hlam hl
    rw [hl, wenv_eq_iSup Λ₂ σ (hlam.of_le (by exact_mod_cast hn))]


theorem one_le_maxBracketPow {θ : ℝ} (hθ : 0 ≤ θ) (lam : Fin r → ℝ) : 1 ≤ maxBracketPow θ lam := by
  unfold maxBracketPow
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (le_max_right _ _) hθ)

section Cutoff

/-- Zero the family outside the set `A`. -/
noncomputable def cutoffFamily (A : Set (Fin r → ℝ)) (Ψ : (Fin r → ℝ) → Mom d → ℂ) :
    (Fin r → ℝ) → Mom d → ℂ :=
  fun lam k => A.indicator (fun l => Ψ l k) lam

theorem cutoffFamily_of_mem {A : Set (Fin r → ℝ)} {Ψ : (Fin r → ℝ) → Mom d → ℂ} {lam : Fin r → ℝ}
    (h : lam ∈ A) : cutoffFamily A Ψ lam = Ψ lam :=
  funext fun k => Set.indicator_of_mem h _

theorem cutoffFamily_of_notMem {A : Set (Fin r → ℝ)} {Ψ : (Fin r → ℝ) → Mom d → ℂ} {lam : Fin r → ℝ}
    (h : lam ∉ A) : cutoffFamily A Ψ lam = fun _ => 0 :=
  funext fun k => Set.indicator_of_notMem h _

theorem contDiff_cutoffFamily {A : Set (Fin r → ℝ)} {Ψ : (Fin r → ℝ) → Mom d → ℂ} {N : ℕ}
    (h : ∀ lam ∈ A, ContDiff ℝ N (Ψ lam)) (lam : Fin r → ℝ) :
    ContDiff ℝ N (cutoffFamily A Ψ lam) := by
  by_cases hl : lam ∈ A
  · rw [cutoffFamily_of_mem hl]; exact h lam hl
  · rw [cutoffFamily_of_notMem hl]; exact contDiff_const

theorem stronglyMeasurable_cutoffFamily {A : Set (Fin r → ℝ)} {Ψ : (Fin r → ℝ) → Mom d → ℂ}
    (hA : MeasurableSet A) (hm : ∀ k, StronglyMeasurable fun lam => Ψ lam k) (k : Mom d) :
    StronglyMeasurable fun lam => cutoffFamily A Ψ lam k :=
  (hm k).indicator hA

end Cutoff

theorem continuous_timeFT_apply (G : (Fin r → ℝ) → Mom d → ℂ) (hG : ∀ k, Integrable fun t => G t k)
    (k : Mom d) : Continuous fun lam => timeFT G lam k := by
  have : (fun lam => timeFT G lam k) = timeFourier (fun t => G t k) :=
    funext fun lam => NormBridgeScratch.timeFT_eq_timeFourier G lam k
  rw [this]
  exact timeFourier_continuous (hG k)

/-- **A good representative of the transform family.** -/
theorem exists_good_family {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0)
    (G : (Fin r → ℝ) → Mom d → ℂ) (hG : XNorm θ Λ₁ Λ₂ G < ⊤) :
    ∃ Φ : (Fin r → ℝ) → Mom d → ℂ,
      (∀ᵐ lam, Φ lam = timeFT G lam) ∧ (∀ lam, ContDiff ℝ Λ₁ (Φ lam)) ∧
      (∀ k, StronglyMeasurable fun lam => Φ lam k) ∧
      (∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d, ∀ lam, wenv Λ₂ σ (Φ lam) < ⊤) ∧
      (∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d, ∫⁻ lam, maxBracketPow θ lam * wenv Λ₂ σ (Φ lam) ≤
        XNorm θ Λ₁ Λ₂ G) ∧
      (∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d, ∫⁻ lam, wenv Λ₂ σ (Φ lam) ≠ ⊤) := by
  classical
  have hadm : (∀ k, Integrable fun t => G t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT G lam)) := by
    by_contra h
    simp [XNorm, h] at hG
  have hsm := hadm.2.resolve_left hΛ
  obtain ⟨N1, hN1sub, hN1m, hN1z⟩ := exists_measurable_superset_of_null (ae_iff.1 hsm)
  set A1 : Set (Fin r → ℝ) := N1ᶜ with hA1
  have hA1m : MeasurableSet A1 := hN1m.compl
  have hA1ae : ∀ᵐ lam, lam ∈ A1 := by
    rw [ae_iff]; simpa [hA1] using hN1z
  have hA1cd : ∀ lam ∈ A1, ContDiff ℝ Λ₁ (timeFT G lam) := by
    intro lam hl
    by_contra hc
    exact hl (hN1sub hc)
  set Φ' := cutoffFamily A1 (timeFT G) with hΦ'
  have hΦ'cd := contDiff_cutoffFamily (N := Λ₁) hA1cd
  have hΦ'm : ∀ k, StronglyMeasurable fun lam => Φ' lam k := fun k =>
    stronglyMeasurable_cutoffFamily hA1m
      (fun k => (continuous_timeFT_apply G hadm.1 k).stronglyMeasurable) k
  have hΦ'ae : ∀ᵐ lam, Φ' lam = timeFT G lam := by
    filter_upwards [hA1ae] with lam hl using cutoffFamily_of_mem hl
  have hb' : ∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d,
      ∫⁻ lam, maxBracketPow θ lam * wenv Λ₂ σ (Φ' lam) ≤ XNorm θ Λ₁ Λ₂ G := fun n hn σ =>
    lintegral_wenv_le_XNorm θ Λ₂ G hadm hn σ hΦ'ae hΛ
  have hfin' : ∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d, ∀ᵐ lam, wenv Λ₂ σ (Φ' lam) < ⊤ := by
    intro n hn σ
    refine ae_lt_top (measurable_wenv hΦ'cd hΦ'm hn σ) ?_
    refine ne_top_of_le_ne_top (hG.ne) ((lintegral_mono fun lam => ?_).trans (hb' n hn σ))
    exact le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ lam)
  set A2 : Set (Fin r → ℝ) := {lam | ∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d, wenv Λ₂ σ (Φ' lam) < ⊤} with hA2
  have hA2m : MeasurableSet A2 := by
    simp only [hA2, Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun hn => MeasurableSet.iInter fun σ =>
      measurableSet_lt (measurable_wenv hΦ'cd hΦ'm hn σ) measurable_const
  have hA2ae : ∀ᵐ lam, lam ∈ A2 :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun hn => ae_all_iff.2 fun σ => hfin' n hn σ
  set Φ := cutoffFamily A2 Φ' with hΦ
  have hΦcd : ∀ lam, ContDiff ℝ Λ₁ (Φ lam) := contDiff_cutoffFamily (fun lam _ => hΦ'cd lam)
  have hΦm : ∀ k, StronglyMeasurable fun lam => Φ lam k := fun k =>
    stronglyMeasurable_cutoffFamily hA2m hΦ'm k
  have hΦae : ∀ᵐ lam, Φ lam = timeFT G lam := by
    filter_upwards [hA2ae, hΦ'ae] with lam hl h2 using by rw [hΦ, cutoffFamily_of_mem hl, h2]
  have hb : ∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d,
      ∫⁻ lam, maxBracketPow θ lam * wenv Λ₂ σ (Φ lam) ≤ XNorm θ Λ₁ Λ₂ G := fun n hn σ =>
    lintegral_wenv_le_XNorm θ Λ₂ G hadm hn σ hΦae hΛ
  refine ⟨Φ, hΦae, hΦcd, hΦm, ?_, hb, ?_⟩
  · intro n hn σ lam
    by_cases hl : lam ∈ A2
    · rw [hΦ, cutoffFamily_of_mem hl]; exact hl n hn σ
    · rw [hΦ, cutoffFamily_of_notMem hl, wenv_zero]; exact ENNReal.zero_lt_top
  · intro n hn σ
    refine ne_top_of_le_ne_top hG.ne ((lintegral_mono fun lam => ?_).trans (hb n hn σ))
    exact le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ lam)

end WaveTurbulence.VineEstS3.FS
