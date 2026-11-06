/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Shift

/-!
# Pointwise values in time: the `𝔖^{Λ,Λ₂}` norm of `k ↦ F(t₀, k)` (PL23-30D)

For `G` of finite norm `𝔛^{θ,Λ,Λ₂}`, the continuous representative `rep G(t₀, ·)` is `C^Λ` and

`‖k ↦ rep G(t₀,k)‖_{𝔖^{Λ,Λ₂}} ≤ ‖G‖_{𝔛^{θ,Λ,Λ₂}}`

(`spatialNorm_point_le`), by Fourier inversion and differentiation under the frequency integral. The restriction
version `spatialNorm_point_rN_le` evaluates at a point of `closure (interior ℬ)` of a function continuous in time.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ} {Λ Λ₂ : ℕ} {θ : ℝ}

theorem spatialNorm_point_le (hθ : 0 ≤ θ) (hΛ : Λ ≠ 0) {G : (Fin r → ℝ) → Mom d → ℂ}
    (hG : mixedFourierNorm θ Λ Λ₂ G < ⊤) (t₀ : Fin r → ℝ) :
    ContDiff ℝ Λ (fun k => rep (fun u => G u k) t₀) ∧
      spatialNorm Λ Λ₂ (fun k => rep (fun u => G u k) t₀) ≤ mixedFourierNorm θ Λ Λ₂ G := by
  classical
  have hadm := admissible_of_lt_top hG
  have hiG : ∀ k, Integrable (fun t => G t k) := hadm.1
  have hsm : ∀ᵐ ξ, ContDiff ℝ Λ (mixedTimeFourier G ξ) := hadm.2.resolve_left hΛ
  obtain ⟨Gd⟩ := Good.exists hiG hsm
  set M := mixedFourierNorm θ Λ Λ₂ G with hMdef
  let Φ : (Fin r → ℝ) → Mom d → ℂ := Gd.Φ
  have hΦs : ∀ ξ, ContDiff ℝ Λ (Φ ξ) := Gd.smooth
  have hΦm : ∀ k, StronglyMeasurable fun ξ => Φ ξ k := Gd.meas
  have hΦae : ∀ k, (fun ξ => Φ ξ k) =ᵐ[volume] fun ξ => mixedTimeFourier G ξ k := fun k => by
    filter_upwards [Gd.ae] with ξ hξ
    exact congrFun hξ k
  let E : (n : ℕ) → (Fin n → Fin d) → (Fin r → ℝ) → ℝ≥0∞ :=
    fun n ρ ξ => ⨆ k, ‖momentumDerivative ρ (Φ ξ) k‖ₑ
  let Ew : (n : ℕ) → (Fin n → Fin d) → (Fin r → ℝ) → ℝ≥0∞ :=
    fun n ρ ξ => momentumSupNorm Λ₂ (momentumDerivative ρ (Φ ξ))
  have hEm : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Measurable (E n ρ) :=
    fun n hn ρ => measurable_wordEnvelope hΦs hΦm hn ρ
  have hEwm : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Measurable (Ew n ρ) :=
    fun n hn ρ => Gd.env_meas Λ₂ hn ρ
  have hEEw : ∀ n (ρ : Fin n → Fin d) ξ, E n ρ ξ ≤ Ew n ρ ξ := fun n ρ ξ => by
    have h0 : E n ρ ξ = momentumSupNorm 0 (momentumDerivative ρ (Φ ξ)) := (momentumSupNorm_zero_eq _).symm
    rw [h0]
    exact momentumSupNorm_mono_weight (Nat.zero_le _) _
  have hEw : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, timeWeight θ ξ * Ew n ρ ξ ≤ M :=
    fun n hn ρ => Gd.nInt_le hadm hn ρ
  have hw1 : ∀ ξ : Fin r → ℝ, (1 : ℝ≥0∞) ≤ timeWeight θ ξ := fun ξ => one_le_timeWeight hθ ξ
  have hEw1 : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, Ew n ρ ξ ≤ M := by
    intro n hn ρ
    refine le_trans (lintegral_mono fun ξ => ?_) (hEw n hn ρ)
    calc Ew n ρ ξ = 1 * Ew n ρ ξ := (one_mul _).symm
      _ ≤ timeWeight θ ξ * Ew n ρ ξ := mul_le_mul_left (hw1 ξ) _
  have hE1 : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, E n ρ ξ ≠ ⊤ := fun n hn ρ =>
    ne_top_of_le_ne_top (((hEw1 n hn ρ).trans_lt hG).ne) (lintegral_mono fun ξ => hEEw n ρ ξ)
  have hEfin : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∀ᵐ ξ, E n ρ ξ < ⊤ := fun n hn ρ =>
    ae_lt_top (hEm n hn ρ) (hE1 n hn ρ)
  have hEint : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Integrable fun ξ => (E n ρ ξ).toReal := fun n hn ρ =>
    integrable_toReal_of_lintegral_ne_top (hEm n hn ρ).aemeasurable (hE1 n hn ρ)
  have hmD : ∀ n (ρ : Fin n → Fin d) ξ k, ‖momentumDerivative ρ (Φ ξ) k‖ₑ ≤ E n ρ ξ :=
    fun n ρ ξ k => le_iSup (fun k => ‖momentumDerivative ρ (Φ ξ) k‖ₑ) k
  -- the point evaluation as a frequency integral
  have hslice : ∀ k, timeFourierNorm θ (fun t => G t k) < ⊤ := fun k =>
    (timeFourierNorm_slice_le (θ := θ) (Λ := Λ) (Λ₂ := Λ₂) G k).trans_lt hG
  let ε : (Fin r → ℝ) → ℂ := fun η => ((Real.fourierChar (-timePairing r η (-t₀)) : Circle) : ℂ)
  have hε1 : ∀ η, ‖ε η‖ = 1 := fun η => Circle.norm_coe _
  have hεm : StronglyMeasurable ε := by
    have hcoe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    refine (hcoe.comp (Real.continuous_fourierChar.comp ?_)).stronglyMeasurable
    change Continuous fun η : Fin r → ℝ => -(∑ j, η j * (-t₀) j)
    fun_prop
  have hv : ∀ k, rep (fun u => G u k) t₀ = ∫ η, ε η * Φ η k := by
    intro k
    unfold rep timeFourier VectorFourier.fourierIntegral
    refine integral_congr_ae ?_
    filter_upwards [hΦae k] with η hη
    simp only [Circle.smul_def, smul_eq_mul, ε]
    rw [hη]
    rfl
  let f : Mom d → (Fin r → ℝ) → ℂ := fun k η => ε η * Φ η k
  have hfs : ∀ η, ContDiff ℝ Λ fun k => f k η := fun η => contDiff_const.mul (hΦs η)
  have hfm : ∀ k, StronglyMeasurable (f k) := fun k => hεm.mul (hΦm k)
  have hfd : ∀ η (n : ℕ), n ≤ Λ → ∀ k, iteratedFDeriv ℝ n (fun k => f k η) k =
      ε η • iteratedFDeriv ℝ n (Φ η) k := by
    intro η n hn k
    have : (fun k => f k η) = ε η • Φ η := by
      funext k; simp [f, smul_eq_mul]
    rw [this, iteratedFDeriv_const_smul_apply ((hΦs η).contDiffAt.of_le (by exact_mod_cast hn))]
  have hfmeas : ∀ n : ℕ, n ≤ Λ → ∀ k, AEStronglyMeasurable (fun η => iteratedFDeriv ℝ n (fun k => f k η) k) volume :=
    fun n hn k => (stronglyMeasurable_iteratedFDeriv_param_of_le (f := f) hfs hfm n hn k).aestronglyMeasurable
  have hfb : ∀ n : ℕ, n ≤ Λ → ∃ B : (Fin r → ℝ) → ℝ, Integrable B ∧
      ∀ᵐ η, ∀ k, ‖iteratedFDeriv ℝ n (fun k => f k η) k‖ ≤ B η := by
    intro n hn
    refine ⟨fun η => ∑ ρ : Fin n → Fin d, (E n ρ η).toReal,
      integrable_finsetSum _ fun ρ _ => hEint n hn ρ, ?_⟩
    filter_upwards [ae_all_iff.2 (hEfin n hn)] with η hη k
    rw [hfd η n hn k, norm_smul, hε1, one_mul]
    refine (norm_le_sum_coordWords _).trans (Finset.sum_le_sum fun ρ _ => ?_)
    have h1 := hmD n ρ η k
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal (hη ρ).ne).1 h1
  have hvf : (fun k => rep (fun u => G u k) t₀) = fun k => ∫ η, f k η := funext hv
  have hcd : ContDiff ℝ Λ (fun k => rep (fun u => G u k) t₀) := by
    rw [hvf]
    exact contDiff_integral_param_of_le hfs hfmeas hfb
  have hder : ∀ n : ℕ, n ≤ Λ → ∀ (ρ : Fin n → Fin d) k,
      momentumDerivative ρ (fun k => rep (fun u => G u k) t₀) k = ∫ η, ε η * momentumDerivative ρ (Φ η) k := by
    intro n hn ρ k
    have hint : Integrable (fun η => iteratedFDeriv ℝ n (fun k => f k η) k) := by
      obtain ⟨B, hBi, hBb⟩ := hfb n hn
      exact hBi.mono' (hfmeas n hn k) (by filter_upwards [hBb] with η hη using hη k)
    rw [momentumDerivative_apply, hvf,
      iteratedFDeriv_integral_param_of_le hfs hfmeas hfb n hn,
      ContinuousMultilinearMap.integral_apply hint]
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    beta_reduce
    rw [hfd η n hn k]
    rfl
  refine ⟨hcd, ?_⟩
  unfold spatialNorm
  simp only [hcd, or_true, ↓reduceIte]
  refine iSup₂_le fun n hn => iSup_le fun ρ => ?_
  unfold momentumSupNorm
  refine iSup_le fun k => ?_
  rw [hder n hn ρ k]
  have hint : ‖∫ η, ε η * momentumDerivative ρ (Φ η) k‖ₑ ≤ ∫⁻ η, ‖ε η * momentumDerivative ρ (Φ η) k‖ₑ :=
    enorm_integral_le_lintegral_enorm _
  calc ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖∫ η, ε η * momentumDerivative ρ (Φ η) k‖ₑ
      ≤ ENNReal.ofReal (momentumBracket k ^ Λ₂) * ∫⁻ η, ‖ε η * momentumDerivative ρ (Φ η) k‖ₑ :=
        mul_le_mul_right hint _
    _ = ∫⁻ η, ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖ε η * momentumDerivative ρ (Φ η) k‖ₑ := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ η, Ew n ρ η := by
        refine lintegral_mono fun η => ?_
        rw [enorm_mul, ← ofReal_norm (ε η), hε1, ENNReal.ofReal_one, one_mul]
        exact le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖momentumDerivative ρ (Φ η) k‖ₑ) k
    _ ≤ M := hEw1 n hn ρ

/-- **Point values of a function of finite restriction norm.** -/
theorem spatialNorm_point_rN_le (hθ : 0 ≤ θ) (hΛ : Λ ≠ 0) {B : Set (Fin r → ℝ)}
    (h : (Fin r → ℝ) → Mom d → ℂ) (hh : ∀ k, Continuous fun t => h t k) {t₀ : Fin r → ℝ}
    (ht₀ : t₀ ∈ closure (interior B)) {e : ℝ≥0∞} (hfin : rN θ Λ Λ₂ B h ≤ e) (he : e < ⊤) :
    ContDiff ℝ Λ (fun k => h t₀ k) ∧ spatialNorm Λ Λ₂ (fun k => h t₀ k) ≤ e := by
  have hfin' : rN θ Λ Λ₂ B h < ⊤ := hfin.trans_lt he
  obtain ⟨G₀⟩ := nonempty_finiteExt hfin'
  have hslice : ∀ G : {G : (Fin r → ℝ) → Mom d → ℂ // (∀ t ∈ B, ∀ k ∈ (Set.univ : Set (Mom d)), G t k = h t k) ∧
      mixedFourierNorm θ Λ Λ₂ G < ⊤}, ∀ k, rep (fun u => G.1 u k) t₀ = h t₀ k := fun G k =>
    rep_eq_of_mem_closure_interior hθ
      ((timeFourierNorm_slice_le (θ := θ) (Λ := Λ) (Λ₂ := Λ₂) G.1 k).trans_lt G.2.2)
      (fun s hs => G.2.1 s hs k (mem_univ _)) (hh k) ht₀
  have hfun : (fun k => h t₀ k) = fun k => rep (fun u => G₀.1 u k) t₀ := funext fun k => (hslice G₀ k).symm
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (spatialNorm_point_le hθ hΛ G₀.2.2 t₀).1
  · refine le_trans ?_ hfin
    rw [rN_eq_agreement B h]
    refine le_iInf₂ fun G hG => ?_
    by_cases hGt : mixedFourierNorm θ Λ Λ₂ G < ⊤
    · have hf2 : (fun k => h t₀ k) = fun k => rep (fun u => G u k) t₀ := funext fun k =>
        (hslice ⟨G, hG, hGt⟩ k).symm
      rw [hf2]
      exact (spatialNorm_point_le hθ hΛ hGt t₀).2
    · rw [not_lt, top_le_iff] at hGt
      rw [hGt]
      exact le_top

end WaveTurbulence.PL2330
