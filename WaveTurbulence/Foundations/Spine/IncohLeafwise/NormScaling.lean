/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Fourier.TimeBasic

/-! # Scalar homogeneity of the weighted spatial and mixed Fourier norms

Used to normalize individual leaf inputs in the leafwise B2.2 (TARGET Prop 5.1 at L2062-L2067):
`spatialNorm (c • f) = ‖c‖ * spatialNorm f` and `mixedRestrictionNorm (c • F) ≤ ‖c‖ * mixedRestrictionNorm F`
for a nonzero scalar. -/

public section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.Fourier

theorem contDiff_smul_iff {d : ℕ} {n : WithTop ℕ∞} {c : ℂ} (hc : c ≠ 0) (f : Mom d → ℂ) :
    ContDiff ℝ n (fun k => c • f k) ↔ ContDiff ℝ n f := by
  constructor
  · intro h
    have := h.const_smul c⁻¹
    simpa [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc] using this
  · intro h
    exact h.const_smul c

theorem reg_of_le {d Λ n : ℕ} {f : Mom d → ℂ} (h : Λ = 0 ∨ ContDiff ℝ Λ f) (hn : n ≤ Λ) :
    n = 0 ∨ ContDiff ℝ n f := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact Or.inl h0
  · right
    rcases h with h | h
    · omega
    · exact h.of_le (by exact_mod_cast hn)

theorem momentumDerivative_smul {d n : ℕ} (c : ℂ) (ρ : Fin n → Fin d) (f : Mom d → ℂ)
    (hf : n = 0 ∨ ContDiff ℝ n f) (k : Mom d) :
    momentumDerivative ρ (fun x => c • f x) k = c • momentumDerivative ρ f k := by
  rcases hf with rfl | hf
  · simp only [momentumDerivative_zero]
  · unfold momentumDerivative
    rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt]
    rfl

theorem momentumSupNorm_smul {d : ℕ} (Λ : ℕ) (c : ℂ) (f : Mom d → ℂ) :
    momentumSupNorm Λ (fun k => c • f k) = ‖c‖ₑ * momentumSupNorm Λ f := by
  unfold momentumSupNorm
  rw [ENNReal.mul_iSup]
  congr 1
  funext k
  rw [enorm_smul]
  ring

theorem spatialNorm_smul {d : ℕ} (Λ₁ Λ₂ : ℕ) {c : ℂ} (hc : c ≠ 0) (f : Mom d → ℂ) :
    spatialNorm Λ₁ Λ₂ (fun k => c • f k) = ‖c‖ₑ * spatialNorm Λ₁ Λ₂ f := by
  classical
  have hiff : (Λ₁ = 0 ∨ ContDiff ℝ Λ₁ (fun k => c • f k)) ↔ (Λ₁ = 0 ∨ ContDiff ℝ Λ₁ f) :=
    or_congr_right (contDiff_smul_iff hc f)
  unfold spatialNorm
  by_cases h : Λ₁ = 0 ∨ ContDiff ℝ Λ₁ f
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h, ENNReal.mul_iSup]
    congr 1; funext n
    rw [ENNReal.mul_iSup]
    congr 1; funext hn
    rw [ENNReal.mul_iSup]
    congr 1; funext ρ
    have hreg := reg_of_le h hn
    have : momentumDerivative ρ (fun k => c • f k) = fun k => c • momentumDerivative ρ f k :=
      funext (momentumDerivative_smul c ρ f hreg)
    rw [this, momentumSupNorm_smul]
  · rw [ite_eq_right (mt hiff.1 h), ite_eq_right h]
    simp [hc]

theorem mixedTimeFourier_smul {r d : ℕ} (c : ℂ) (F : (Fin r → ℝ) → Mom d → ℂ) (ξ : Fin r → ℝ) :
    mixedTimeFourier (fun t k => c • F t k) ξ = fun k => c • mixedTimeFourier F ξ k := by
  funext k
  exact congrFun (timeFourier_smul c fun t => F t k) ξ

theorem mixedFourierNorm_smul {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) {c : ℂ} (hc : c ≠ 0)
    (F : (Fin r → ℝ) → Mom d → ℂ) :
    mixedFourierNorm θ Λ₁ Λ₂ (fun t k => c • F t k) = ‖c‖ₑ * mixedFourierNorm θ Λ₁ Λ₂ F := by
  classical
  have hadm : MixedFourierAdmissible Λ₁ (fun t k => c • F t k) ↔ MixedFourierAdmissible Λ₁ F := by
    unfold MixedFourierAdmissible
    refine and_congr (forall_congr' fun k => integrable_smul_iff hc _) (or_congr_right ?_)
    simp_rw [mixedTimeFourier_smul]
    exact Filter.eventually_congr (Filter.Eventually.of_forall fun ξ =>
      contDiff_smul_iff hc _)
  have hne : ‖c‖ₑ ≠ ⊤ := by simp
  unfold mixedFourierNorm
  by_cases h : MixedFourierAdmissible Λ₁ F
  · rw [ite_eq_left (hadm.2 h), ite_eq_left h, ENNReal.mul_iSup]
    congr 1; funext n
    rw [ENNReal.mul_iSup]
    congr 1; funext hn
    rw [ENNReal.mul_iSup]
    congr 1; funext ρ
    rw [← lintegral_const_mul' _ _ hne]
    have hae : ∀ᵐ ξ, n = 0 ∨ ContDiff ℝ n (mixedTimeFourier F ξ) := by
      rcases h.2 with h0 | h1
      · exact Filter.Eventually.of_forall (fun _ => Or.inl (by omega))
      · filter_upwards [h1] with ξ hξ
        exact reg_of_le (Or.inr hξ) hn
    apply lintegral_congr_ae
    filter_upwards [hae] with ξ hξ
    rw [mixedTimeFourier_smul]
    have : momentumDerivative ρ (fun k => c • mixedTimeFourier F ξ k) =
        fun k => c • momentumDerivative ρ (mixedTimeFourier F ξ) k :=
      funext (momentumDerivative_smul c ρ _ hξ)
    rw [this, momentumSupNorm_smul]
    ring
  · rw [ite_eq_right (mt hadm.1 h), ite_eq_right h]
    simp [hc]

theorem mixedRestrictionNorm_smul_le {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ))
    (K : Set (Mom d)) {c : ℝ} (hc : 0 < c) (F : B → K → ℂ) :
    mixedRestrictionNorm θ Λ₁ Λ₂ B K (fun t k => (c : ℂ) • F t k) ≤
      ENNReal.ofReal c * mixedRestrictionNorm θ Λ₁ Λ₂ B K F := by
  have h0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  have htop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold mixedRestrictionNorm
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun hG => ?_
  refine (iInf₂_le (fun t k => (c : ℂ) • G t k) (fun t k => by simp [hG t k])).trans ?_
  rw [mixedFourierNorm_smul θ Λ₁ Λ₂ hc' G]
  apply le_of_eq
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc.le]

end WaveTurbulence.IncohLeafwise
