/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.CellSplit
public import WaveTurbulence.Foundations.ApproxNT.LargeOrder

/-!
# DH23 Prop 6.4, conclusion (1), uniformly for orders `n ≤ (log L)^A` (packet NT6)

DH23 `Revision_Submit.tex` L984–L1004 (proof: DH21 Prop 6.1, `Inventiones-Final_Version.tex`
L1504–L1648), extended to the large-order range of FINDINGS F33 (route R14(a),
blueprint `GAP.largeOrder.nt`).
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped FourierTransform ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d n : ℕ}

theorem norm_le_freqNorm_fst (ξ η : Fin n → Mom d) (j : Fin n) : ‖ξ j‖ ≤ freqNorm ξ η := by
  rw [freqNorm]
  refine Real.le_sqrt_of_sq_le ?_
  calc ‖ξ j‖ ^ 2 ≤ ‖ξ j‖ ^ 2 + ‖η j‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    _ ≤ ∑ i, (‖ξ i‖ ^ 2 + ‖η i‖ ^ 2) :=
        single_le_sum (f := fun i => ‖ξ i‖ ^ 2 + ‖η i‖ ^ 2) (fun _ _ => by positivity) (mem_univ j)

theorem norm_le_freqNorm_snd (ξ η : Fin n → Mom d) (j : Fin n) : ‖η j‖ ≤ freqNorm ξ η := by
  rw [freqNorm]
  refine Real.le_sqrt_of_sq_le ?_
  calc ‖η j‖ ^ 2 ≤ ‖ξ j‖ ^ 2 + ‖η j‖ ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
    _ ≤ ∑ i, (‖ξ i‖ ^ 2 + ‖η i‖ ^ 2) :=
        single_le_sum (f := fun i => ‖ξ i‖ ^ 2 + ‖η i‖ ^ 2) (fun _ _ => by positivity) (mem_univ j)

theorem freqNorm_nonneg (ξ η : Fin n → Mom d) : 0 ≤ freqNorm ξ η := Real.sqrt_nonneg _

/-- The bracket of the cell estimate, in terms of `|(ξ, η)|`. -/
theorem cell_bracket_le {L : ℝ} (hL : 1 ≤ L) {η : ℝ} (hη : 0 ≤ η) (ξ ζ : Fin n → Mom d) {q : ℝ}
    (hq : 0 ≤ q) :
    ∑ i, (L ^ (-1 + 2 * (η / 4)) * (1 + ‖ξ i‖ + ‖ζ i‖) + L⁻¹) + 2 * n * q ≤
      (1 + freqNorm ξ ζ) * (2 * n * L ^ (-1 + η / 2) + 2 * n * q) := by
  have hL0 : 0 < L := by linarith
  have hfN := freqNorm_nonneg ξ ζ
  have hLp : 0 ≤ L ^ (-1 + η / 2) := Real.rpow_nonneg hL0.le _
  have hinv : L⁻¹ ≤ L ^ (-1 + η / 2) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h2 : 2 * (η / 4) = η / 2 := by ring
  rw [h2]
  calc ∑ i, (L ^ (-1 + η / 2) * (1 + ‖ξ i‖ + ‖ζ i‖) + L⁻¹) + 2 * n * q
      ≤ ∑ _i : Fin n, (L ^ (-1 + η / 2) * (2 + 2 * freqNorm ξ ζ)) + 2 * n * q := by
        gcongr with i
        calc L ^ (-1 + η / 2) * (1 + ‖ξ i‖ + ‖ζ i‖) + L⁻¹
            ≤ L ^ (-1 + η / 2) * (1 + freqNorm ξ ζ + freqNorm ξ ζ) + L ^ (-1 + η / 2) := by
              gcongr
              · exact norm_le_freqNorm_fst ξ ζ i
              · exact norm_le_freqNorm_snd ξ ζ i
          _ = L ^ (-1 + η / 2) * (2 + 2 * freqNorm ξ ζ) := by ring
    _ ≤ (1 + freqNorm ξ ζ) * (2 * n * L ^ (-1 + η / 2) + 2 * n * q) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : 2 * (n : ℝ) * q ≤ (1 + freqNorm ξ ζ) * (2 * n * q) := by
          nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg (α := ℝ) n)) hq]
        nlinarith

theorem E_bound {L η γ : ℝ} (hL : 1 ≤ L) {n : ℕ} (hpoly : (n : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) ≤ L ^ (η / 2))
    (hη : 0 ≤ η) :
    2 * n * L ^ (-1 + η / 2) + 2 * n * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
        L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)) ≤
      (2 ^ (d + 3)) ^ n * L ^ (-gamma1 d γ + η) := by
  have hL0 : 0 < L := by linarith
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp; positivity
  have hP1 : (n : ℝ) ≤ (n : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) := by
    refine le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ ?_)
    exact_mod_cast Nat.le_add_left 1 _
  have hg1 : gamma1 d γ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hg2 : gamma1 d γ ≤ 2 * ((d : ℝ) - 1) * (1 - γ) := (min_le_right _ _).trans (min_le_right _ _)
  have ha : 2 * n * L ^ (-1 + η / 2) ≤ 2 * L ^ (-gamma1 d γ + η) := by
    calc 2 * (n : ℝ) * L ^ (-1 + η / 2) ≤ 2 * (L ^ (η / 2) * L ^ (-1 + η / 2)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hP1.trans hpoly)
            (Real.rpow_nonneg hL0.le _)) (by norm_num)
      _ = 2 * L ^ (-1 + η) := by rw [← Real.rpow_add hL0]; ring_nf
      _ ≤ 2 * L ^ (-gamma1 d γ + η) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
            (by norm_num)
  have hb : 2 * n * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
        L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)) ≤ 2 ^ (d + 2) * L ^ (-gamma1 d γ + η) := by
    calc 2 * (n : ℝ) * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
          L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4))
        = 2 ^ (d + 2) * (((n : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) *
            L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)) := by ring
      _ ≤ 2 ^ (d + 2) * (L ^ (η / 2) * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)) := by
          gcongr
      _ = 2 ^ (d + 2) * L ^ (η / 2 + (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)) := by
          rw [← Real.rpow_add hL0]
      _ ≤ 2 ^ (d + 2) * L ^ (-gamma1 d γ + η) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
            (by positivity)
  have hc : (2 : ℝ) + 2 ^ (d + 2) ≤ (2 ^ (d + 3)) ^ n := by
    calc (2 : ℝ) + 2 ^ (d + 2) ≤ 2 ^ (d + 3) := by
          rw [pow_succ (2 : ℝ) (d + 2)]
          have : (2 : ℝ) ≤ 2 ^ (d + 2) := le_self_pow₀ (by norm_num) (by omega)
          linarith
      _ ≤ (2 ^ (d + 3)) ^ n := le_self_pow₀ (one_le_pow₀ (by norm_num)) (by omega)
  have hLp : 0 ≤ L ^ (-gamma1 d γ + η) := Real.rpow_nonneg hL0.le _
  calc _ ≤ 2 * L ^ (-gamma1 d γ + η) + 2 ^ (d + 2) * L ^ (-gamma1 d γ + η) := add_le_add ha hb
    _ = (2 + 2 ^ (d + 2)) * L ^ (-gamma1 d γ + η) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hLp

theorem card_cells_le {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    (a b : Fin n → Mom d) {lam : Fin n → ℝ} (hlam : ∀ j, 1 ≤ lam j) :
    ((cellBox_finite hxs hys a b lam).toFinset.card : ℝ) ≤
      (7 : ℝ) ^ (2 * d * n) * (∏ j, lam j) ^ (2 * d) := by
  refine (card_cellBox_le hxs hys a b fun j => by linarith [hlam j]).trans ?_
  calc ∏ j, (2 * lam j + 5) ^ (2 * d) ≤ ∏ j, (7 * lam j) ^ (2 * d) :=
        prod_le_prod₀ (fun j _ => by have := hlam j; positivity) fun j _ =>
          pow_le_pow_left₀ (by linarith [hlam j]) (by linarith [hlam j]) _
    _ = (7 : ℝ) ^ (2 * d * n) * (∏ j, lam j) ^ (2 * d) := by
        rw [prod_pow, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, mul_pow,
          ← pow_mul, mul_comm n]

theorem isFiniteMeasureOnCompacts_pairs :
    IsFiniteMeasureOnCompacts (volume : Measure ((Fin n → Mom d) × (Fin n → Mom d))) := by
  have h1 : (volume : Measure (Fin n → Mom d)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h2 : SigmaFinite (volume : Measure (Fin n → Mom d)) := Measure.pi.sigmaFinite _
  have h3 : ((volume : Measure (Fin n → Mom d)).prod
      (volume : Measure (Fin n → Mom d))).IsAddHaarMeasure := inferInstance
  rw [Measure.volume_eq_prod]
  infer_instance

theorem Lpow_div_mu {L δ γ : ℝ} (hL : 0 < L) :
    L ^ (2 * d) / (L ^ (2 * γ) * δ) = L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹ := by
  rw [div_mul_eq_div_div, Real.rpow_sub hL, ← Real.rpow_natCast]
  push_cast
  ring

theorem complex_Lpow (L : ℝ) : ((L ^ (2 * d) : ℝ) : ℂ) ^ n = (L : ℂ) ^ (2 * d * n) := by
  push_cast; simp only [← pow_mul]

/-- **DH23 Prop 6.4, conclusion (1)** (`Revision_Submit.tex` L984–L1004; proof as DH21 Prop 6.1,
`Inventiones-Final_Version.tex` L1504–L1648), uniformly for orders `n ≤ (log L)^A` and arbitrary
box sizes `λ_j ≥ 1` (FINDINGS F33, `GAP.largeOrder.nt`).

Quantifiers: `d ≥ 3`, `γ ∈ (0,1)`, `η` small (`η ≤ 1/20`, `η ≤ (d-1)(1-γ)`), and the constant `C₀`
of (propertypsi2) are fixed; then `C₁` is chosen; then for every exponent `A` a threshold `L₀`;
the bound holds for all `L ≥ L₀`, `δ ∈ (0,1]`, all orders `n ≤ (log L)^A`, every constant `C⁺ ≥ 0`
of (propertyw1), every triangular structure, box, `W`, `J`, `Ψ₁`. The source's `(λ₁⋯λ_n)^C` is
`(λ₁⋯λ_n)^{2d}`, its `(C^+ L^{2d-2γ} δ^{-1})^n` is `(C₁ C⁺ L^{2d-2γ} δ^{-1})^n`.

Hypotheses: (propertyw1) as `∫ |Ŵ| (1 + 2π|(ξ,η)|) ≤ (C⁺)^n` (for `W ∈ C¹_c` this is
`‖Ŵ‖_{L¹} + ‖(∂W)^‖_{L¹}`); `W` continuous (it is evaluated at lattice points); (propertyw2) as
`W ≠ 0 → (x,y) ∈ E`; (propertypsi1) through `resProfile J Ψ₁`; the first half of (propertypsi2)
as `WordDerivL1 Ψ₁ (k ↦ C₀^n (4k)!)`, with `Ψ₁` smooth. -/
theorem approxnt_conclusion1 (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ}
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
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ‖approxSum L (L ^ (2 * γ) * δ) W (resProfile J Ψ₁) -
          (L : ℂ) ^ (2 * d * n) * approxInt (L ^ (2 * γ) * δ) W (resProfile J Ψ₁)‖ ≤
        (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n *
          L ^ (-gamma1 d γ + η) := by
  obtain ⟨K, hK0, hcell⟩ := exists_cell_bound hd hγ (η := η / 4) (by positivity) (by linarith) hC₀
  set K' := K * max 1 (kerConst d) * C₀ with hK'
  have hmax : 0 ≤ max 1 (kerConst d) := le_trans zero_le_one (le_max_left _ _)
  have hK'0 : 0 ≤ K' := mul_nonneg (mul_nonneg hK0 hmax) (by linarith)
  set C₁ := (7 : ℝ) ^ (2 * d) * (K' + 1) * 2 ^ (d + 3)
  refine ⟨C₁, by positivity, fun A => ?_⟩
  have hgap : 3 * η / 4 < 2 * ((d : ℝ) - 1) * (1 - γ) := by
    have h1 : 0 < ((d : ℝ) - 1) * (1 - γ) :=
      mul_pos (by have h3 : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith) (by linarith [hγ.2])
    nlinarith
  obtain ⟨L₀, hL₀⟩ := exists_large_L (by omega : 1 ≤ d) hη0 hgap A
  refine ⟨L₀, fun L hL δ hδ n hn Cplus hCp lt _ xs ys hxs hys a b lam hlam W hWc hWs hW J Ψ₁ hΨ
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
  set Ψ := resProfile J Ψ₁
  have hΨc : Continuous Ψ := continuous_resProfile J hΨ.continuous
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
    rw [multiSum_res_eq_trunc hμ0.le J Ψ₁ pq τ, multiInt_res_eq_trunc hμ0.le J Ψ₁ pq τ,
      ← complex_Lpow]
    have h := hcell n L δ hL2 hLη hδ hnq J Ψ₁ hΨ hD (cellLevels μ pq) (cellData pq τ)
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

end WaveTurbulence.ApproxNT
