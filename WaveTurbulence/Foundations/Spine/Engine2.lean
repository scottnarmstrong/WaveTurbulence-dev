/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Engine1
/-! # Factorization engine, pointwise-in-time expansion (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint
open scoped FourierTransform ENNReal

variable {d n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product of Fourier transforms of the localized amplitudes. -/
noncomputable def Phi (F : ι → Mom d → ℂ) (a : ι → Fin d → ℤ) (ξ : ι → Mom d) : ℂ :=
  ∏ b, 𝓕 (localizedWeight (a b) (F b)) (ξ b)

lemma continuous_e_inner {d : ℕ} (v : Mom d) : Continuous (fun ξ : Mom d => e (inner ℝ ξ v)) := by
  unfold e
  exact Complex.continuous_exp.comp (by fun_prop)

lemma prod_fc_mul {ι : Type*} [Fintype ι] (x : ι → ℝ) (y : ι → ℂ) :
    ∏ b, ((Real.fourierChar (x b) : ℂ) * y b) = (∏ b, e (x b)) * ∏ b, y b := by
  rw [Finset.prod_mul_distrib]
  simp only [fourierChar_eq_e]

omit [DecidableEq ι] in
lemma integrable_phi_mul (hd : 1 ≤ d) (F : ι → Mom d → ℂ)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1) (a : ι → Fin d → ℤ)
    (q : ι → Mom d) (c : ℂ) :
    Integrable (fun ξ : ι → Mom d =>
      c * ∏ b, ((Real.fourierChar (inner ℝ (ξ b) (q b)) : ℂ) *
        𝓕 (localizedWeight (a b) (F b)) (ξ b))) := by
  have hI := (amp_expansion_mass hd F hF a).1
  have h1 : ∀ ξ : ι → Mom d, ∏ b, ((Real.fourierChar (inner ℝ (ξ b) (q b)) : ℂ) *
        𝓕 (localizedWeight (a b) (F b)) (ξ b)) =
      (∏ b, e (inner ℝ (ξ b) (q b))) * Phi F a ξ := by
    intro ξ
    simp only [prod_fc_mul, Phi]
  simp_rw [h1]
  have hc : Continuous (fun ξ : ι → Mom d => ∏ b, e (inner ℝ (ξ b) (q b))) :=
    continuous_finsetProd _ (fun b _ => (continuous_e_inner (q b)).comp (continuous_apply b))
  have hI' : Integrable (fun ξ : ι → Mom d => Phi F a ξ) := hI
  have := hI'.bdd_mul (c := 1) hc.aestronglyMeasurable (ae_of_all _ (fun ξ => by
    rw [norm_prod]; simp))
  exact (this.const_mul c).congr (ae_of_all _ (fun ξ => by simp [mul_comm]))


/-- Exchange of the finite configuration sum with the modulation integral. -/
theorem expand_sum (hd : 1 ≤ d) (L : ℝ) (base : Mom d) (F : ι → Mom d → ℂ) (ctr : ι → Mom d)
    (lab : ι → AffLab d n)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1)
    (hsupp : ∀ b x, 1 < ‖x - ctr b‖ → F b x = 0)
    (S : Fin n → Finset (Pt d)) (Δ : Fin n → (Pt d →+ (Fin d → ℤ))) (c0 : Fin d → ℤ)
    (Wt : Fin n → Pt d → ℂ) :
    ∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then
        (∏ b, F b (base + latticePoint L ((lab b).eval P))) * ∏ k, Wt k (P k) else 0) =
      ∑ a ∈ Fintype.piFinset (fun b => cellsAround (ctr b)), ∫ ξ : ι → Mom d,
        Phi F a ξ * ∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then
          (∏ b, e (inner ℝ (ξ b) (base + latticePoint L ((lab b).eval P)))) *
            ∏ k, Wt k (P k) else 0) := by
  classical
  have h1 : ∀ P : Fin n → Pt d, (if ∑ k, Δ k (P k) = c0 then
        (∏ b, F b (base + latticePoint L ((lab b).eval P))) * ∏ k, Wt k (P k) else 0) =
      ∑ a ∈ Fintype.piFinset (fun b => cellsAround (ctr b)), ∫ ξ : ι → Mom d,
        (if ∑ k, Δ k (P k) = c0 then (∏ b, ((Real.fourierChar
          (inner ℝ (ξ b) (base + latticePoint L ((lab b).eval P))) : ℂ) *
            𝓕 (localizedWeight (a b) (F b)) (ξ b))) * ∏ k, Wt k (P k) else 0) := by
    intro P
    split_ifs with hc
    · rw [amp_expansion hd F ctr hF hsupp, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← integral_mul_const]
    · simp
  have h2 : ∀ (a : ι → Fin d → ℤ) (P : Fin n → Pt d),
      (∫ ξ : ι → Mom d, (if ∑ k, Δ k (P k) = c0 then (∏ b, ((Real.fourierChar
          (inner ℝ (ξ b) (base + latticePoint L ((lab b).eval P))) : ℂ) *
            𝓕 (localizedWeight (a b) (F b)) (ξ b))) * ∏ k, Wt k (P k) else 0)) =
      ∫ ξ : ι → Mom d, Phi F a ξ * (if ∑ k, Δ k (P k) = c0 then
          (∏ b, e (inner ℝ (ξ b) (base + latticePoint L ((lab b).eval P)))) *
            ∏ k, Wt k (P k) else 0) := by
    intro a P
    refine integral_congr_ae (ae_of_all _ (fun ξ => ?_))
    split_ifs
    · simp only [prod_fc_mul, Phi]
      ring
    · simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp_rw [h2 a]
  rw [← integral_finsetSum]
  · refine integral_congr_ae (ae_of_all _ (fun ξ => ?_))
    simp [Finset.mul_sum]
  · intro P _
    by_cases hc : ∑ k, Δ k (P k) = c0
    · simp only [hc, ite_true]
      have := integrable_phi_mul hd F hF a (fun b => base + latticePoint L ((lab b).eval P))
        (∏ k, Wt k (P k))
      refine this.congr (ae_of_all _ (fun ξ => ?_))
      simp only [Phi, prod_fc_mul]
      ring
    · simp [hc]


/-- The twisted-sum majorant for fixed time data. -/
noncomputable def Gmaj (L : ℝ) (lab : ι → AffLab d n) (S : Fin n → Finset (Pt d))
    (Δ : Fin n → (Pt d →+ (Fin d → ℤ))) (M : ℕ) (Wt : Fin n → Pt d → ℂ)
    (ξ : ι → Mom d) : ℝ :=
  ((M : ℝ) ^ d)⁻¹ * ∑ j : Fin d → Fin M,
    ∏ k, ‖∑ p ∈ S k, Wt k p * e ((nuK L lab ξ k + psiK M (Δ k) j) p)‖

/-- **Pointwise-in-time expansion bound** (extended-norm form). -/
theorem stepA (hd : 1 ≤ d) (L : ℝ) (base : Mom d) (F : ι → Mom d → ℂ) (ctr : ι → Mom d)
    (lab : ι → AffLab d n)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1)
    (hsupp : ∀ b x, 1 < ‖x - ctr b‖ → F b x = 0)
    (S : Fin n → Finset (Pt d)) (Δ : Fin n → (Pt d →+ (Fin d → ℤ))) (c0 : Fin d → ℤ)
    (M : ℕ) (hM : 0 < M)
    (hb : ∀ P ∈ Fintype.piFinset S, ∀ i, |(∑ k, Δ k (P k)) i - c0 i| < M)
    (Wt : Fin n → Pt d → ℂ) :
    ‖∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then
        (∏ b, F b (base + latticePoint L ((lab b).eval P))) * ∏ k, Wt k (P k) else 0)‖ₑ ≤
      ∑ a ∈ Fintype.piFinset (fun b => cellsAround (ctr b)),
        ∫⁻ ξ : ι → Mom d, ‖Phi F a ξ‖ₑ * ENNReal.ofReal (Gmaj L lab S Δ M Wt ξ) := by
  rw [expand_sum hd L base F ctr lab hF hsupp S Δ c0 Wt]
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono (fun ξ => ?_))
  rw [enorm_mul]
  refine mul_le_mul' le_rfl ?_
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (constrained_phase_sum_norm_le L base lab ξ Wt Δ c0 M hM hb)

end WaveTurbulence.LadderDecay
