/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltNT.Cell

/-! # FILT-NT: the continuous cell integral of the filtered profile

Main's `RegAsymp.exists_continuous_cell_size_bound` for `filtProf J S Ψ`: `‖multiInt μ (filtProf J S Ψ) …‖ ≤ (K/μ)^{|ι|} D₀`
uniformly in the scales `S_j ≥ 1`. The `J`-factors are `∫ ĝ_S(t) cellInt(μt) dt`, bounded by `‖ĝ_S‖_∞ μ⁻¹ cellCa`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset WithLp WaveTurbulence.ApproxNT
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.Flower.FiltNT

variable {d : ℕ}

theorem norm_jfactor_le (hd : 3 ≤ d) {μ : ℝ} (hμ : 0 < μ) {S Kp : ℝ} (hb : ∀ s, ‖ghat S s‖ ≤ Kp)
    (p q ξ η : Mom d) :
    ‖∫ t, ghat S t * cellInt p q ξ η (μ * t)‖ ≤ Kp * (μ⁻¹ * cellCa d) := by
  have hKp : 0 ≤ Kp := le_trans (norm_nonneg _) (hb 0)
  have h1 := enorm_integral_le_lintegral_enorm (μ := (volume : Measure ℝ))
    (fun t => ghat S t * cellInt p q ξ η (μ * t))
  have h2 : ∫⁻ t, ‖ghat S t * cellInt p q ξ η (μ * t)‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal Kp * ‖cellInt p q ξ η (μ * t)‖ₑ := by
    refine lintegral_mono fun t => ?_
    rw [enorm_mul]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb t)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h2
  have h3 := (h1.trans h2).trans (mul_le_mul_of_nonneg_left
    (lintegral_cellInt_scale_le (by omega) hμ p q ξ η) zero_le)
  have hCa := one_le_cellCa d
  have h4 : ‖∫ t, ghat S t * cellInt p q ξ η (μ * t)‖ ≤ Kp * (μ⁻¹ * (cellK0 d * NTSP.sInt d)) := by
    rw [← ENNReal.ofReal_mul hKp, ← ofReal_norm] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have := cellK0_nonneg d
      have := NTSP.sInt_nonneg d
      positivity)).1 h3
  refine h4.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hμ.le)) hKp)
  exact le_max_left _ _

/-- The continuous cell integral of the filtered profile has its natural size, uniformly in the filter scales. -/
theorem filt_continuous_cell_size (hd : 3 ≤ d) (Kp : ℝ)
    (hb : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ ≤ Kp) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι],
      ∀ (J : Finset ι) (S : ι → ℝ), (∀ j, 1 ≤ S j) → ∀ (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (D : ℕ → ℝ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ D → (∀ k, 0 ≤ D k) →
      ∀ D0 : ℝ, (∫ Ω, ‖Ψ Ω‖) ≤ D0 → ∀ μ : ℝ, 0 < μ → ∀ c : CellData d ι,
      ‖multiInt μ (filtProf J S Ψ) c.p c.q c.ξ c.ζ‖ ≤ (K / μ) ^ Fintype.card ι * D0 := by
  have hKp : 0 ≤ Kp := le_trans (norm_nonneg _) (hb 1 le_rfl 0)
  let K := max 1 Kp * cellCa d
  have hCa := one_le_cellCa d
  have hK1 : 1 ≤ K := by
    have : 1 ≤ max 1 Kp := le_max_left _ _
    nlinarith
  refine ⟨K, hK1, ?_⟩
  intro ι _ _ J S hS Ψ D hΨ hD hD0 D0 hD0' μ hμ0 c
  have hμi : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμ0.le
  have hD00 : 0 ≤ D0 := (integral_nonneg (fun _ => norm_nonneg _)).trans hD0'
  let g : ι → ℝ → ℂ := fun i t => cellInt (c.p i) (c.q i) (c.ξ i) (c.ζ i) (μ * t)
  let B := ∫ b : {j // j ∉ J} → ℝ, 𝓕 Ψ (toLp 2 b) * ∏ i : {j // j ∉ J}, g i (b i)
  have hrep := isFourierRep_filtProf (d := d) (by omega) J S hS hΨ hD hD0
  have hmain : multiInt μ (filtProf J S Ψ) c.p c.q c.ξ c.ζ =
      (∏ j ∈ J, ∫ t, ghat (S j) t * g j t) * B := by
    rw [multiInt_eq μ hrep, integral_filtHat_split J S Ψ g]
  have hPt (j : ι) : ‖∫ t, ghat (S j) t * g j t‖ ≤ μ⁻¹ * K := by
    refine (norm_jfactor_le hd hμ0 (hb (S j) (hS j)) _ _ _ _).trans ?_
    have : Kp ≤ max 1 Kp := le_max_right _ _
    calc Kp * (μ⁻¹ * cellCa d) = μ⁻¹ * (Kp * cellCa d) := by ring
      _ ≤ μ⁻¹ * K := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (by linarith)) hμi
  have hB : ‖B‖ ≤ D0 * (μ⁻¹ * K) ^ Fintype.card {j // j ∉ J} := by
    have hh := norm_B_le hd hμ0 hD0'
      (fun i : {j // j ∉ J} => c.p i) (fun i : {j // j ∉ J} => c.q i)
      (fun i : {j // j ∉ J} => c.ξ i) (fun i : {j // j ∉ J} => c.ζ i)
    refine hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hD00)
    exact mul_le_mul_of_nonneg_left (by
      have : 1 ≤ max 1 Kp := le_max_left _ _
      nlinarith) hμi
  have hprod : ‖∏ j ∈ J, ∫ t, ghat (S j) t * g j t‖ ≤ (μ⁻¹ * K) ^ J.card := by
    apply (Finset.norm_prod_le _ _).trans
    calc _ ≤ ∏ _j ∈ J, μ⁻¹ * K := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hPt j)
      _ = _ := by simp
  have hcard : J.card + Fintype.card {j // j ∉ J} = Fintype.card ι := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    have hh := card_le_univ J
    omega
  rw [hmain, norm_mul]
  calc _ ≤ (μ⁻¹ * K) ^ J.card * (D0 * (μ⁻¹ * K) ^ Fintype.card {j // j ∉ J}) :=
        mul_le_mul hprod hB (norm_nonneg _) (by positivity)
    _ = (μ⁻¹ * K) ^ Fintype.card ι * D0 := by rw [← hcard, pow_add]; ring
    _ = _ := by rw [div_eq_mul_inv, mul_comm K μ⁻¹]

end WaveTurbulence.Flower.FiltNT
