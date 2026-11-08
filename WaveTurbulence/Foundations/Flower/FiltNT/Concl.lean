/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltNT.Cell
public import WaveTurbulence.Foundations.ApproxNT.Conclusion1

/-! # FILT-NT: DH23 Prop 6.4 conclusion (1) for the filtered profile

Main's `ApproxNT.approxnt_conclusion1` with `resProfile J Ψ₁` replaced by `filtProf J S Ψ₁`, uniformly in the filter
scales `S_j ≥ 1`. The proof is main's, with the truncated-profile cell identification dropped (the filtered profile
needs no truncation) and the cell estimate `exists_filt_cell_bound`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset WithLp WaveTurbulence.ApproxNT
open scoped FourierTransform ContDiff ENNReal

namespace WaveTurbulence.Flower.FiltNT

variable {d n : ℕ}

theorem continuous_filtProf {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι) (S : ι → ℝ)
    {Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ} (hΨ : Continuous Ψ₁) : Continuous (filtProf J S Ψ₁) := by
  refine (continuous_finsetProd _ fun j _ => ?_).mul (hΨ.comp ?_)
  · exact (continuous_gS _).comp (continuous_apply j)
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply (i : ι))

/-- **DH23 Prop 6.4, conclusion (1), for the filtered profile**, uniformly in the scales `S_j ≥ 1`. -/
theorem filt_conclusion1 (hd : 3 ≤ d) (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hb : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ * (1 + s ^ 2) ^ d ≤ Kp) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1 / 20) (hηγ : η ≤ ((d : ℝ) - 1) * (1 - γ)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A → ∀ Cplus : ℝ, 0 ≤ Cplus →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) →
      ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
          ENNReal.ofReal (1 + 2 * Real.pi * freqNorm τ.1 τ.2) ≤ ENNReal.ofReal (Cplus ^ n) →
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ‖approxSum L (L ^ (2 * γ) * δ) W (filtProf J S Ψ₁) -
          (L : ℂ) ^ (2 * d * n) * approxInt (L ^ (2 * γ) * δ) W (filtProf J S Ψ₁)‖ ≤
        (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n *
          L ^ (-gamma1 d γ + η) := by
  obtain ⟨K, hK0, hcell⟩ := exists_filt_cell_bound hd Kp hKp hb hγ (η := η / 4) (by positivity) (by linarith) hC₀
  set K' := K * max 1 (Kp) * C₀ with hK'
  have hmax : 0 ≤ max 1 Kp := le_trans zero_le_one (le_max_left _ _)
  have hK'0 : 0 ≤ K' := mul_nonneg (mul_nonneg hK0 hmax) (by linarith)
  set C₁ := (7 : ℝ) ^ (2 * d) * (K' + 1) * 2 ^ (d + 3)
  refine ⟨C₁, by positivity, fun A => ?_⟩
  have hgap : 3 * η / 4 < 2 * ((d : ℝ) - 1) * (1 - γ) := by
    have h1 : 0 < ((d : ℝ) - 1) * (1 - γ) :=
      mul_pos (by have h3 : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith) (by linarith [hγ.2])
    nlinarith
  obtain ⟨L₀, hL₀⟩ := exists_large_L (by omega : 1 ≤ d) hη0 hgap A
  refine ⟨L₀, fun L hL δ hδ n hn Cplus hCp lt _ xs ys hxs hys a b lam hlam W hWc hWs hW J S hS Ψ₁ hΨ
    hD => ?_⟩
  obtain ⟨hL2, hLη, hpoly, hsmall⟩ := hL₀ L hL
  have : SigmaFinite (volume : Measure (Fin n → Mom d)) := Measure.pi.sigmaFinite _
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hδ0 := hδ.1
  set μ := L ^ (2 * γ) * δ with hμdef
  have hμ' : μ = δ * L ^ (2 * γ) := mul_comm _ _
  have hμ0 : 0 < μ := mul_pos (Real.rpow_pos_of_pos hL0 _) hδ0
  set Q := (cellBox_finite hxs hys a b lam).toFinset
  set Ψ := filtProf J S Ψ₁
  have hΨc : Continuous Ψ := continuous_filtProf J S hΨ.continuous
  have hΩc : Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      (fun j => μ * inner ℝ (z.1 j) (z.2 j))) :=
    continuous_pi fun j => continuous_const.mul
      (((continuous_apply j).comp continuous_fst).inner ((continuous_apply j).comp continuous_snd))
  -- regularity of the cell pieces
  have hhm : ∀ pq, Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) :=
    fun pq => (continuous_cellWeight pq).mul (hΨc.comp hΩc)
  have hhs : ∀ pq, HasCompactSupport (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) :=
    fun pq => (hasCompactSupport_cellWeight pq).mul_right
  have hh : ∀ pq, Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) :=
    fun pq => (hhm pq).integrable_of_hasCompactSupport (hhs pq)
  have hcelli : ∀ pq, Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      W z.1 z.2 * cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) := by
    intro pq
    have hc : Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
        W z.1 z.2 * (cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j)))) :=
      hWc.mul (hhm pq)
    exact (hc.integrable_of_hasCompactSupport (hhs pq).mul_left).congr
      (Filter.Eventually.of_forall fun z => by simp only [mul_assoc])
  -- `W` and `Ŵ` are integrable
  have hWi : Integrable (Function.uncurry W) := by
    have hwc : ∀ pq, Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
        W z.1 z.2 * cellWeight pq z.1 z.2) := fun pq =>
      (hWc.mul (continuous_cellWeight pq)).integrable_of_hasCompactSupport
        (hasCompactSupport_cellWeight pq).mul_left
    refine (integrable_finsetSum Q fun pq _ => hwc pq).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry]
    exact (W_eq_sum_cells hxs hys hWs z.1 z.2).symm
  have hFc := continuous_fourierW hWi
  have hWlin : ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ ≤
      ENNReal.ofReal (Cplus ^ n) := by
    refine le_trans (lintegral_mono fun τ => ?_) hW
    refine le_mul_of_one_le_right zero_le ?_
    rw [ENNReal.one_le_ofReal]
    have := freqNorm_nonneg τ.1 τ.2
    nlinarith [Real.pi_pos]
  have hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2) :=
    ⟨hFc.aestronglyMeasurable, lt_of_le_of_lt hWlin ENNReal.ofReal_lt_top⟩
  have hinv : ∀ x y, W x y = ∫ τ, fourierW W τ.1 τ.2 * wPhase x y τ :=
    fun x y => fourierW_inversion hWc hWi hF x y
  -- the weight `‖Ŵ‖ (1 + 2π|τ|)` is integrable
  have hGi : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      ‖fourierW W τ.1 τ.2‖ * (1 + 2 * Real.pi * freqNorm τ.1 τ.2)) := by
    refine ⟨(hFc.norm.mul (continuous_const.add (continuous_const.mul ?_))).aestronglyMeasurable,
      ?_⟩
    · exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
        (((continuous_apply j).comp continuous_fst).norm.pow 2).add
          (((continuous_apply j).comp continuous_snd).norm.pow 2))
    · refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hW ENNReal.ofReal_lt_top)
      refine lintegral_congr fun τ => ?_
      have hp : 0 ≤ 1 + 2 * Real.pi * freqNorm τ.1 τ.2 := by
        have := freqNorm_nonneg τ.1 τ.2; positivity
      rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hp),
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  have hGint : ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW W τ.1 τ.2‖ * (1 + 2 * Real.pi * freqNorm τ.1 τ.2) ≤ Cplus ^ n := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun τ => by
      have := freqNorm_nonneg τ.1 τ.2; positivity) hGi.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans (le_of_eq ?_) hW)
    refine lintegral_congr fun τ => ?_
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  -- the per-cell bound
  set q : ℝ := 2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
    L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)
  have hq : 0 ≤ q := by positivity
  have hnq : (n : ℝ) * q ≤ 1 / 2 := by
    have hp := hpoly n hn
    calc (n : ℝ) * q = 2 ^ (d + 1) * ((n : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) *
          L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4) := by simp only [q]; ring
      _ ≤ 2 ^ (d + 1) * L ^ (η / 2) * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4) := by
          gcongr
      _ ≤ 1 / 2 := hsmall
  set E : ℝ := 2 * n * L ^ (-1 + η / 2) + 2 * n * q
  have hE : E ≤ (2 ^ (d + 3)) ^ n * L ^ (-gamma1 d γ + η) := E_bound hL1 (hpoly n hn) hη0.le
  have hE0 : 0 ≤ E := by have := Real.rpow_nonneg hL0.le (-1 + η / 2); positivity
  set X : ℝ := K' * L ^ (2 * d) / μ
  have hX0 : 0 ≤ X := by positivity
  have hDτ : ∀ pq (τ : (Fin n → Mom d) × (Fin n → Mom d)),
      ‖multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ -
        (L : ℂ) ^ (2 * d * n) * multiInt μ Ψ (cellData pq τ).p (cellData pq τ).q
          (cellData pq τ).ξ (cellData pq τ).ζ‖ ≤ X ^ n * ((1 + freqNorm τ.1 τ.2) * E) := by
    intro pq τ
    rw [← complex_Lpow]
    have h := hcell n L δ hL2 hLη hδ hnq J Ψ₁ hΨ hD S hS (cellData pq τ)
    rw [← hμ'] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact cell_bracket_le hL1 hη0.le τ.1 τ.2 hq
  have hcellb : ∀ pq, ‖∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
      (multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ -
        (L : ℂ) ^ (2 * d * n) * multiInt μ Ψ (cellData pq τ).p (cellData pq τ).q
          (cellData pq τ).ξ (cellData pq τ).ζ)‖ ≤ X ^ n * E * Cplus ^ n := by
    intro pq
    refine (norm_integral_le_of_norm_le (hGi.const_mul (X ^ n * E))
      (Filter.Eventually.of_forall fun τ => ?_)).trans ?_
    · rw [norm_mul]
      have hfN := freqNorm_nonneg τ.1 τ.2
      calc ‖fourierW W τ.1 τ.2‖ * ‖multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q
            (cellData pq τ).ξ (cellData pq τ).ζ - (L : ℂ) ^ (2 * d * n) * multiInt μ Ψ
              (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ‖
          ≤ ‖fourierW W τ.1 τ.2‖ * (X ^ n * ((1 + freqNorm τ.1 τ.2) * E)) :=
            mul_le_mul_of_nonneg_left (hDτ pq τ) (norm_nonneg _)
        _ ≤ X ^ n * E * (‖fourierW W τ.1 τ.2‖ * (1 + 2 * Real.pi * freqNorm τ.1 τ.2)) := by
            have h1 : 1 + freqNorm τ.1 τ.2 ≤ 1 + 2 * Real.pi * freqNorm τ.1 τ.2 := by
              nlinarith [Real.pi_gt_three]
            have h2 : 0 ≤ ‖fourierW W τ.1 τ.2‖ * (X ^ n * E) := by positivity
            nlinarith
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hGint (by positivity)
  have hdec : approxSum L μ W Ψ - (L : ℂ) ^ (2 * d * n) * approxInt μ W Ψ =
      ∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
        (multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ -
          (L : ℂ) ^ (2 * d * n) * multiInt μ Ψ (cellData pq τ).p (cellData pq τ).q
            (cellData pq τ).ξ (cellData pq τ).ζ) := by
    rw [approxSum_eq_sum_cells hxs hys hWs hL0 μ Ψ, approxInt_eq_sum_cells hxs hys hWs μ Ψ hcelli,
      mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun pq _ => ?_
    obtain ⟨hTi, hTeq⟩ := approxInt_cell μ hinv hF Ψ pq (hh pq) (hhm pq)
    rw [approxSum_cell hL0 μ hinv hF Ψ pq, hTeq, ← integral_const_mul,
      ← integral_sub (integrable_fourierW_mul_multiSum hL0 μ hF Ψ pq) (hTi.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    ring
  rw [hdec]
  have hY : X = K' * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) := by
    simp only [X]; rw [mul_div_assoc, Lpow_div_mu hL0]
  have hprod0 : 0 ≤ ∏ j, lam j := prod_nonneg fun j _ => by linarith [hlam j]
  have hLY : 0 ≤ L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.2 hδ0.le)
  calc ‖∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
        (multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ -
          (L : ℂ) ^ (2 * d * n) * multiInt μ Ψ (cellData pq τ).p (cellData pq τ).q
            (cellData pq τ).ξ (cellData pq τ).ζ)‖
      ≤ ∑ _pq ∈ Q, X ^ n * E * Cplus ^ n :=
        (norm_sum_le _ _).trans (sum_le_sum fun pq _ => hcellb pq)
    _ = Q.card * (X ^ n * E * Cplus ^ n) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (7 : ℝ) ^ (2 * d * n) * (∏ j, lam j) ^ (2 * d) * (X ^ n * E * Cplus ^ n) :=
        mul_le_mul_of_nonneg_right (card_cells_le hxs hys a b hlam) (by positivity)
    _ ≤ (7 : ℝ) ^ (2 * d * n) * (∏ j, lam j) ^ (2 * d) *
          (X ^ n * ((2 ^ (d + 3)) ^ n * L ^ (-gamma1 d γ + η)) * Cplus ^ n) := by
        gcongr
    _ = (∏ j, lam j) ^ (2 * d) * ((7 : ℝ) ^ (2 * d) * X * 2 ^ (d + 3) * Cplus) ^ n *
          L ^ (-gamma1 d γ + η) := by
        rw [mul_pow, mul_pow, mul_pow, ← pow_mul, mul_comm (2 * d) n, pow_mul]
        ring
    _ ≤ (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n *
          L ^ (-gamma1 d γ + η) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (Real.rpow_nonneg hL0.le _)
        refine pow_le_pow_left₀ (by positivity) ?_ n
        rw [hY]
        simp only [C₁]
        have : K' ≤ K' + 1 := by linarith
        calc (7 : ℝ) ^ (2 * d) * (K' * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹)) * 2 ^ (d + 3) * Cplus
            ≤ (7 : ℝ) ^ (2 * d) * ((K' + 1) * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹)) * 2 ^ (d + 3) *
                Cplus := by gcongr
          _ = _ := by ring


end WaveTurbulence.Flower.FiltNT
