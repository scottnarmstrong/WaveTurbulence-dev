/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Regular

/-!
# The triangle inequality for `𝔛^{θ,Λ,Λ₂}` and its restriction norms (PL23-30D)

With the almost-everywhere `C^Λ` guard (F80) the word envelopes of a finite-norm family are a.e. equal to
measurable functions (`Good`), so `∫⁻` is a genuine integral and subadditive.

* `mixedFourierNorm_add_le`, `mixedFourierNorm_zero`;
* `restr_add_le`, `restr_add₃_le`, `restr_finsetSum_le`, `restr_congr`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

theorem momentumDerivative_add {Λ n : ℕ} (hn : n ≤ Λ) (ρ : Fin n → Fin d) {f g : Mom d → ℂ}
    (hf : ContDiff ℝ Λ f) (hg : ContDiff ℝ Λ g) :
    momentumDerivative ρ (fun k => f k + g k) = fun k => momentumDerivative ρ f k + momentumDerivative ρ g k := by
  funext k
  unfold momentumDerivative
  have h := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (f := f) (g := g) (x := k)
    (hf.contDiffAt.of_le (by exact_mod_cast hn)) (hg.contDiffAt.of_le (by exact_mod_cast hn))
  have h' : iteratedFDeriv ℝ n (fun k => f k + g k) k = iteratedFDeriv ℝ n f k + iteratedFDeriv ℝ n g k := h
  rw [h']
  rfl

theorem momentumSupNorm_add_le (Λ₂ : ℕ) (f g : Mom d → ℂ) :
    momentumSupNorm Λ₂ (fun k => f k + g k) ≤ momentumSupNorm Λ₂ f + momentumSupNorm Λ₂ g := by
  unfold momentumSupNorm
  refine iSup_le fun k => ?_
  calc ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖f k + g k‖ₑ
      ≤ ENNReal.ofReal (momentumBracket k ^ Λ₂) * (‖f k‖ₑ + ‖g k‖ₑ) :=
        mul_le_mul_right (enorm_add_le _ _) _
    _ = ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖f k‖ₑ + ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖g k‖ₑ :=
        mul_add _ _ _
    _ ≤ _ := add_le_add
        (le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖f k‖ₑ) k)
        (le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖g k‖ₑ) k)

theorem mixedTimeFourier_add {F G : (Fin r → ℝ) → Mom d → ℂ} (hF : ∀ k, Integrable fun t => F t k)
    (hG : ∀ k, Integrable fun t => G t k) (ξ : Fin r → ℝ) :
    mixedTimeFourier (fun t k => F t k + G t k) ξ = fun k => mixedTimeFourier F ξ k + mixedTimeFourier G ξ k := by
  funext k
  unfold mixedTimeFourier
  exact congrFun (timeFourier_add (hF k) (hG k)) ξ

/-- **The triangle inequality** for `𝔛^{θ,Λ,Λ₂}` (`Λ ≥ 1`, almost-everywhere smoothness guard). -/
theorem mixedFourierNorm_add_le {Λ : ℕ} (hΛ : Λ ≠ 0) (θ : ℝ) (Λ₂ : ℕ) (F G : (Fin r → ℝ) → Mom d → ℂ) :
    mixedFourierNorm θ Λ Λ₂ (fun t k => F t k + G t k) ≤
      mixedFourierNorm θ Λ Λ₂ F + mixedFourierNorm θ Λ Λ₂ G := by
  by_cases hF : mixedFourierNorm θ Λ Λ₂ F < ⊤
  swap
  · rw [not_lt, top_le_iff] at hF
    rw [hF, top_add]
    exact le_top
  by_cases hG : mixedFourierNorm θ Λ Λ₂ G < ⊤
  swap
  · rw [not_lt, top_le_iff] at hG
    rw [hG, add_top]
    exact le_top
  obtain ⟨GF⟩ := exists_good hΛ hF
  obtain ⟨GG⟩ := exists_good hΛ hG
  have hadF := admissible_of_lt_top hF
  have hadG := admissible_of_lt_top hG
  have hsmF := hadF.2.resolve_left hΛ
  have hsmG := hadG.2.resolve_left hΛ
  have hadS : MixedFourierAdmissible Λ (fun t k => F t k + G t k) := by
    refine ⟨fun k => (hadF.1 k).add (hadG.1 k), Or.inr ?_⟩
    filter_upwards [hsmF, hsmG] with ξ h1 h2
    rw [mixedTimeFourier_add hadF.1 hadG.1 ξ]
    exact h1.add h2
  refine (mixedFourierNorm_le_of_bound (θ := θ) (Λ₂ := Λ₂) hadS
    (fun n ρ ξ => momentumSupNorm Λ₂ (momentumDerivative ρ (GF.Φ ξ)) +
      momentumSupNorm Λ₂ (momentumDerivative ρ (GG.Φ ξ))) ?_ (M := mixedFourierNorm θ Λ Λ₂ F +
        mixedFourierNorm θ Λ Λ₂ G) ?_)
  · intro n hn ρ
    filter_upwards [hsmF, hsmG, GF.ae, GG.ae] with ξ h1 h2 h3 h4
    rw [mixedTimeFourier_add hadF.1 hadG.1 ξ, momentumDerivative_add hn ρ h1 h2, h3, h4]
    exact momentumSupNorm_add_le Λ₂ _ _
  · intro n hn ρ
    have hmF := (timeWeight_measurable θ).mul (GF.env_meas Λ₂ hn ρ)
    calc ∫⁻ ξ, timeWeight θ ξ * (momentumSupNorm Λ₂ (momentumDerivative ρ (GF.Φ ξ)) +
          momentumSupNorm Λ₂ (momentumDerivative ρ (GG.Φ ξ)))
        = nInt θ Λ₂ ρ GF.Φ + nInt θ Λ₂ ρ GG.Φ := by
          unfold nInt
          simp only [mul_add]
          exact lintegral_add_left hmF _
      _ ≤ _ := add_le_add (GF.nInt_le hadF hn ρ) (GG.nInt_le hadG hn ρ)

theorem mixedFourierNorm_zero (θ : ℝ) (Λ Λ₂ : ℕ) :
    mixedFourierNorm θ Λ Λ₂ (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) = 0 := by
  have h0 : ∀ ξ, mixedTimeFourier (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) ξ = fun _ => 0 := by
    intro ξ
    funext k
    simp [mixedTimeFourier, timeFourier, VectorFourier.fourierIntegral]
  have hadm : MixedFourierAdmissible Λ (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) :=
    ⟨fun _ => integrable_zero _ _ _, Or.inr (ae_of_all _ fun ξ => by rw [h0]; exact contDiff_const)⟩
  rw [mixedFourierNorm_eq_iSup hadm]
  refine le_antisymm (iSup₂_le fun n _ => iSup_le fun ρ => ?_) zero_le
  simp only [h0, momentumDerivative_zero_fun]
  have : momentumSupNorm Λ₂ (fun _ : Mom d => (0 : ℂ)) = 0 := by simp [momentumSupNorm]
  simp [this]

/-! ### Restriction norms -/

variable {θ : ℝ} {Λ Λ₂ : ℕ}

/-- The restriction norm `𝔛^{θ,Λ,Λ₂}(ℬ)` of an ambient function (all momenta). -/
noncomputable abbrev rN (θ : ℝ) (Λ Λ₂ : ℕ) (B : Set (Fin r → ℝ)) (F : (Fin r → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  mixedRestrictionNorm θ Λ Λ₂ B Set.univ (fun (t : B) (k : (Set.univ : Set (Mom d))) => F t.1 k.1)

theorem rN_eq_agreement (B : Set (Fin r → ℝ)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    rN θ Λ Λ₂ B F = ⨅ (G : (Fin r → ℝ) → Mom d → ℂ) (_ : ∀ t ∈ B, ∀ k ∈ (Set.univ : Set (Mom d)), G t k = F t k),
      mixedFourierNorm θ Λ Λ₂ G :=
  mixedRestrictionNorm_eq_agreement B Set.univ F

theorem rN_le_extension (B : Set (Fin r → ℝ)) (F G : (Fin r → ℝ) → Mom d → ℂ)
    (hG : ∀ t ∈ B, G t = F t) : rN θ Λ Λ₂ B F ≤ mixedFourierNorm θ Λ Λ₂ G := by
  rw [rN_eq_agreement]
  exact iInf₂_le G fun t ht k _ => by rw [hG t ht]

theorem restr_congr (B : Set (Fin r → ℝ)) (K : Set (Mom d)) {F G : (Fin r → ℝ) → Mom d → ℂ}
    (h : ∀ t ∈ B, ∀ k ∈ K, F t k = G t k) :
    mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => F t k) = mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => G t k) := by
  have he : (fun (t : B) (k : K) => F t k) = (fun (t : B) (k : K) => G t k) :=
    funext fun t => funext fun k => h t t.2 k k.2
  rw [he]

theorem restr_add_le (hΛ : Λ ≠ 0) (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F G : (Fin r → ℝ) → Mom d → ℂ) :
    mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => F t k + G t k) ≤
      mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => F t k) + mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => G t k) := by
  rw [mixedRestrictionNorm_eq_agreement B K (fun t k => F t k + G t k),
    mixedRestrictionNorm_eq_agreement B K F, mixedRestrictionNorm_eq_agreement B K G]
  apply ENNReal.le_iInf₂_add_iInf₂
  intro H hH I hI
  refine (iInf₂_le (fun t k => H t k + I t k) fun t ht k hk => by
    show H t k + I t k = F t k + G t k
    rw [hH t ht k hk, hI t ht k hk]).trans ?_
  exact mixedFourierNorm_add_le hΛ θ Λ₂ H I

theorem restr_add₃_le (hΛ : Λ ≠ 0) (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F G H : (Fin r → ℝ) → Mom d → ℂ) :
    mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => F t k + G t k + H t k) ≤
      mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => F t k) + mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => G t k) +
        mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => H t k) :=
  (restr_add_le hΛ B K (fun t k => F t k + G t k) H).trans
    (add_le_add_left (restr_add_le hΛ B K F G) _)

theorem restr_zero (B : Set (Fin r → ℝ)) (K : Set (Mom d)) :
    mixedRestrictionNorm θ Λ Λ₂ B K (fun (_ : B) (_ : K) => (0 : ℂ)) = 0 := by
  refine le_antisymm ?_ zero_le
  exact (mixedRestrictionNorm_le_extension (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ))
    (fun _ _ => rfl)).trans_eq (mixedFourierNorm_zero θ Λ Λ₂)

theorem restr_finsetSum_le (hΛ : Λ ≠ 0) {ι : Type*} (s : Finset ι) (B : Set (Fin r → ℝ)) (K : Set (Mom d))
    (F : ι → (Fin r → ℝ) → Mom d → ℂ) :
    mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => ∑ i ∈ s, F i t k) ≤
      ∑ i ∈ s, mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => F i t k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (restr_zero B K).le
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (restr_add_le hΛ B K (F a) (fun t k => ∑ i ∈ s, F i t k)).trans (add_le_add le_rfl ih)

end WaveTurbulence.PL2330
