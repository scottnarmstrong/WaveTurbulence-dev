/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CrudeCore
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellCrudeSum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellAmplitude
public import WaveTurbulence.Foundations.RegAsymp.Normalization

/-! # FILT-COH (b): the modulation-uniform crude normalized sum (o82 Thm 10.1 (10.5))

`filt_crude_sum_uniform`: for a localized amplitude `W` whose Fourier transform has MASS (no moment) at most
`Cplus^n`, the lattice sum with D5c's filtered profile is `≤ 2 (∏λ)^{2d} (C₁ Cplus L^{2d-2γ}/δ)^n`. The proof is
main's cell decomposition (`approxSum_eq_sum_cells`, `approxSum_cell`) with the crude cell estimate in place of
the difference estimate (skeleton of D5c's `filt_conclusion1`).

`halfCell_crude_uniform` / `halfCell_crude_uniform_res`: the actual half-cell amplitude, normalized, at any
modulations `β, γ'`: `≤ 2 (C δ/4)^n`. The unfiltered pole is the filtered one at a scale above the cell energies. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open MeasureTheory WaveTurbulence.ApproxNT WaveTurbulence.RegAsymp Finset Set
open WaveTurbulence.Flower.FiltNT WaveTurbulence.Incoh
open scoped ENNReal ContDiff FourierTransform

variable {d : ℕ}

/-- **o82 (10.5) for a localized amplitude**: only the Fourier mass of `W` enters. -/
theorem filt_crude_sum_uniform (hd : 3 ≤ d) (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hb : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ * (1 + s ^ 2) ^ d ≤ Kp) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 20)
    (hηγ : η ≤ ((d : ℝ) - 1) * (1 - γ)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
      ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A → ∀ Cplus : ℝ, 0 ≤ Cplus →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) →
      ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ ≤ ENNReal.ofReal (Cplus ^ n) →
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ‖approxSum L (L ^ (2 * γ) * δ) W (filtProf J S Ψ₁)‖ ≤
        2 * (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n := by
  obtain ⟨K, hK0, hcell⟩ := exists_filt_crude_cell_bound hd Kp hKp hb hγ (η := η / 4) (by positivity)
    (by linarith) hC₀
  set K' := K * max 1 Kp * C₀ with hK'
  have hmax : 0 ≤ max 1 Kp := le_trans zero_le_one (le_max_left _ _)
  have hK'0 : 0 ≤ K' := mul_nonneg (mul_nonneg hK0 hmax) (by linarith)
  set C₁ := (7 : ℝ) ^ (2 * d) * (K' + 1)
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
  have hhm : ∀ pq, Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))) :=
    fun pq => (continuous_cellWeight pq).mul (hΨc.comp hΩc)
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
  have hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2) :=
    ⟨hFc.aestronglyMeasurable, lt_of_le_of_lt hW ENNReal.ofReal_lt_top⟩
  have hinv : ∀ x y, W x y = ∫ τ, fourierW W τ.1 τ.2 * wPhase x y τ :=
    fun x y => fourierW_inversion hWc hWi hF x y
  have hGint : ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ ≤ Cplus ^ n := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun τ => norm_nonneg _)
      hF.norm.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans (le_of_eq ?_) hW)
    exact lintegral_congr fun τ => ofReal_norm _
  -- the per-cell bound
  set q : ℝ := 2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
    L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4)
  have hnq : (n : ℝ) * q ≤ 1 / 2 := by
    have hp := hpoly n hn
    calc (n : ℝ) * q = 2 ^ (d + 1) * ((n : ℝ) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) *
          L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4) := by simp only [q]; ring
      _ ≤ 2 ^ (d + 1) * L ^ (η / 2) * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η / 4) := by
          gcongr
      _ ≤ 1 / 2 := hsmall
  set X : ℝ := K' * L ^ (2 * d) / μ
  have hX0 : 0 ≤ X := by positivity
  have hDτ : ∀ pq (τ : (Fin n → Mom d) × (Fin n → Mom d)),
      ‖multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ‖ ≤
        2 * X ^ n := by
    intro pq τ
    have h := hcell n L δ hL2 hLη hδ hnq J Ψ₁ hΨ hD S hS (cellData pq τ)
    rw [← hμ'] at h
    exact h
  have hcellb : ∀ pq, ‖∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
      multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ‖ ≤
        2 * X ^ n * Cplus ^ n := by
    intro pq
    refine (norm_integral_le_of_norm_le (hF.norm.const_mul (2 * X ^ n))
      (Filter.Eventually.of_forall fun τ => ?_)).trans ?_
    · rw [norm_mul, mul_comm (2 * X ^ n)]
      exact mul_le_mul_of_nonneg_left (hDτ pq τ) (norm_nonneg _)
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hGint (by positivity)
  have hdec : approxSum L μ W Ψ =
      ∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
        multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ := by
    rw [approxSum_eq_sum_cells hxs hys hWs hL0 μ Ψ]
    exact sum_congr rfl fun pq _ => approxSum_cell hL0 μ hinv hF Ψ pq
  rw [hdec]
  have hY : X = K' * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) := by
    simp only [X]; rw [mul_div_assoc, Lpow_div_mu hL0]
  have hprod0 : 0 ≤ ∏ j, lam j := prod_nonneg fun j _ => by linarith [hlam j]
  have hLY : 0 ≤ L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.2 hδ0.le)
  calc ‖∑ pq ∈ Q, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
        multiSum L μ Ψ (cellData pq τ).p (cellData pq τ).q (cellData pq τ).ξ (cellData pq τ).ζ‖
      ≤ ∑ _pq ∈ Q, 2 * X ^ n * Cplus ^ n :=
        (norm_sum_le _ _).trans (sum_le_sum fun pq _ => hcellb pq)
    _ = Q.card * (2 * X ^ n * Cplus ^ n) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (7 : ℝ) ^ (2 * d * n) * (∏ j, lam j) ^ (2 * d) * (2 * X ^ n * Cplus ^ n) :=
        mul_le_mul_of_nonneg_right (card_cells_le hxs hys a b hlam) (by positivity)
    _ = 2 * (∏ j, lam j) ^ (2 * d) * ((7 : ℝ) ^ (2 * d) * X * Cplus) ^ n := by
        rw [mul_pow, mul_pow, ← pow_mul, mul_comm (2 * d) n, pow_mul]
        ring
    _ ≤ 2 * (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine pow_le_pow_left₀ (by positivity) ?_ n
        rw [hY]
        simp only [C₁]
        have : K' ≤ K' + 1 := by linarith
        calc (7 : ℝ) ^ (2 * d) * (K' * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹)) * Cplus
            ≤ (7 : ℝ) ^ (2 * d) * ((K' + 1) * (L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹)) * Cplus := by gcongr
          _ = _ := by ring

/-- The Fourier MASS of the half-cell amplitude is independent of the modulations. -/
theorem halfCellAmplitude_fourier_mass {n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d) :
    ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW (halfCellAmplitude z β γ) τ.1 τ.2‖ₑ ≤
      ENNReal.ofReal (halfLinkFirstMomentConstant d ^ (2 * n)) := by
  set f : Fin n → Mom d → ℂ := fun j => halfLinkCell (z (j,0))
  set g : Fin n → Mom d → ℂ := fun j => halfLinkCell (z (j,1))
  have hFourier (ξ η : Fin n → Mom d) :
      fourierW (halfCellAmplitude z β γ) ξ η = (∏ j, 𝓕 (f j) (ξ j-β j))*(∏ j, 𝓕 (g j) (η j-γ j)) := by
    unfold halfCellAmplitude
    rw [fourierW_tensor_factorization
      (fun j x => Real.fourierChar (inner ℝ (β j) x) • f j x)
      (fun j y => Real.fourierChar (inner ℝ (γ j) y) • g j y) ξ η]
    simp only [fourier_positive_modulation]
  set F : (Fin n → Mom d) × (Fin n → Mom d) → ℝ≥0∞ := fun τ =>
    (∏ j, ‖𝓕 (f j) (τ.1 j)‖ₑ)*(∏ j, ‖𝓕 (g j) (τ.2 j)‖ₑ)
  have hshift : ∀ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW (halfCellAmplitude z β γ) τ.1 τ.2‖ₑ = F (τ - (β, γ)) := by
    intro τ
    rw [hFourier, enorm_mul, enorm_finset_prod, enorm_finset_prod]
    rfl
  simp_rw [hshift]
  have hR : (volume : Measure ((Fin n → Mom d) × (Fin n → Mom d))).IsAddRightInvariant := by
    have h1 : (volume : Measure (Fin n → Mom d)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have h2 : SigmaFinite (volume : Measure (Fin n → Mom d)) := Measure.pi.sigmaFinite _
    have h3 : (volume : Measure (Fin n → Mom d)).IsAddRightInvariant := inferInstance
    rw [Measure.volume_eq_prod]; infer_instance
  rw [lintegral_sub_right_eq_self F (β, γ)]
  have hmono : ∀ τ, F τ ≤ ENNReal.ofReal (1+((∑ i, ‖τ.1 i‖)+(∑ i, ‖τ.2 i‖))) *
      ((∏ i, ‖𝓕 (f i) (τ.1 i - (0 : Fin n → Mom d) i)‖ₑ)*(∏ i, ‖𝓕 (g i) (τ.2 i - (0 : Fin n → Mom d) i)‖ₑ)) := by
    intro τ
    simp only [Pi.zero_apply, sub_zero, F]
    refine le_mul_of_one_le_left zero_le ?_
    rw [ENNReal.one_le_ofReal]
    have : 0 ≤ (∑ i, ‖τ.1 i‖)+(∑ i, ‖τ.2 i‖) := by positivity
    linarith
  refine (lintegral_mono hmono).trans ?_
  refine (lintegral_shifted_pair_frequency_moment_le 0 0 (fun j ξ => ‖𝓕 (f j) ξ‖ₑ)
    (fun j ξ => ‖𝓕 (g j) ξ‖ₑ) (fun j => (measurable_fourier_halfLinkCell (z (j,0))).enorm)
    (fun j => (measurable_fourier_halfLinkCell (z (j,1))).enorm)).trans ?_
  simp only [Pi.zero_apply, norm_zero, Finset.sum_const_zero, add_zero, ENNReal.ofReal_one, one_mul]
  calc (∏ j, ∫⁻ ξ : Mom d, ENNReal.ofReal (1+‖ξ‖)*‖𝓕 (f j) ξ‖ₑ) *
        (∏ j, ∫⁻ ξ : Mom d, ENNReal.ofReal (1+‖ξ‖)*‖𝓕 (g j) ξ‖ₑ)
      ≤ (∏ _j : Fin n, ENNReal.ofReal (halfLinkFirstMomentConstant d)) *
        (∏ _j : Fin n, ENNReal.ofReal (halfLinkFirstMomentConstant d)) :=
      mul_le_mul' (Finset.prod_le_prod (fun j _ => halfLinkCell_euclidean_firstMoment_lintegral_le (z (j,0))))
        (Finset.prod_le_prod (fun j _ => halfLinkCell_euclidean_firstMoment_lintegral_le (z (j,1))))
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_add, ← ENNReal.ofReal_pow (halfLinkFirstMomentConstant_pos d).le]
      congr 2; omega

/-- **The actual half-cell sum with D5c's filtered profile, uniform in the modulations** (o82 (10.5)). -/
theorem halfCell_crude_uniform (hd : 3 ≤ d) {γ η : ℝ} (hγ : γ ∈ Ioo (0:ℝ) 1) (hη0 : 0 < η)
    (hη : η ≤ 1/20) (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L ^ A →
      ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
        WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4*k).factorial:ℝ)) →
        ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
          approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (filtProf J S Ψ₁)‖ ≤ 2*(C*δ/4)^n := by
  obtain ⟨Kp, hKp, hb⟩ := filtPole_bound d (by omega)
  obtain ⟨C₁, hC₁, hNT⟩ := filt_crude_sum_uniform hd Kp hKp hb hγ hη0 hη hηγ hC₀
  set r : ℝ := max 1 (Real.sqrt d)
  set D : ℝ := halfLinkFirstMomentConstant d
  have hr : 1 ≤ r := le_max_left _ _
  have hD : 0 < D := halfLinkFirstMomentConstant_pos d
  refine ⟨C₁ * D ^ 2 * r ^ (2 * d), by positivity, fun A => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hNT A
  refine ⟨max L₀ 2, fun L hL δ hδ n hn z β γ' J S hS Ψ₁ hΨ hDer => ?_⟩
  have hL0 : 0 < L := by linarith [le_max_right L₀ 2]
  have hmass : ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW (halfCellAmplitude z β γ') τ.1 τ.2‖ₑ ≤ ENNReal.ofReal ((D ^ 2) ^ n) := by
    rw [← pow_mul]; exact halfCellAmplitude_fourier_mass z β γ'
  have hh := hL₀ L ((le_max_left _ _).trans hL) δ hδ n hn (D ^ 2) (by positivity) (fun i j : Fin n => i<j)
    (fun _ => .zero) (fun _ => .zero) (fun _ => trivial) (fun _ => trivial)
    (fun j => halfCellCenter (z (j,0))) (fun j => halfCellCenter (z (j,1)))
    (fun _ => r) (fun _ => hr) (halfCellAmplitude z β γ')
    (continuous_halfCellAmplitude z β γ') (halfCellAmplitude_support z β γ') hmass J S hS Ψ₁ hΨ hDer
  set q : ℝ := (δ/(2*L^((d:ℝ)-γ)))^(2*n)
  have hq : 0 ≤ q := by have := hδ.1; positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq]
  have hs := normalized_scale (γ := γ) n d hL0 hδ.1.ne' (C₁*D^2)
  calc q * ‖approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (filtProf J S Ψ₁)‖
      ≤ q * (2 * (∏ _j : Fin n, r) ^ (2 * d) * (C₁ * D ^ 2 * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n) :=
        mul_le_mul_of_nonneg_left hh hq
    _ = 2 * (∏ _j : Fin n, r) ^ (2 * d) * (q * (C₁ * D ^ 2 * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n) := by
        ring
    _ = 2 * ((C₁ * D ^ 2 * r ^ (2 * d)) * δ / 4) ^ n := by
        rw [hs]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [show (C₁ * D ^ 2 * r ^ (2 * d)) * δ / 4 = r ^ (2 * d) * (C₁ * D ^ 2 * δ / 4) by ring,
          mul_pow, ← pow_mul, ← pow_mul, mul_comm n (2 * d)]
        ring

/-- On the support of the half-cell amplitude, the unfiltered pole is the filtered pole at any scale above twice
the cell energy, so the unfiltered sum is a filtered one. -/
theorem approxSum_res_eq_filt {n : ℕ} (L μ : ℝ) (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ)
    (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (S : Fin n → ℝ) (hS : ∀ j, 0 < S j)
    (hsupp : ∀ x y, W x y ≠ 0 → ∀ j, |μ * inner ℝ (x j) (y j)| ≤ S j / 2) :
    approxSum L μ W (resProfile J Ψ₁) = approxSum L μ W (filtProf J S Ψ₁) := by
  unfold approxSum
  refine tsum_congr fun g => ?_
  by_cases hW : W (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) = 0
  · rw [hW, zero_mul, zero_mul]
  congr 1
  unfold resProfile filtProf
  congr 1
  refine prod_congr rfl fun j _ => ?_
  have h := hsupp _ _ hW j
  have hu : |μ * inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)) / S j| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (hS j), div_le_iff₀ (hS j)]; linarith
  simp only [gS, Fourier.chi0_eq_one hu, mul_one]

/-- **The actual half-cell sum with the unfiltered pole, uniform in the modulations.** -/
theorem halfCell_crude_uniform_res (hd : 3 ≤ d) {γ η : ℝ} (hγ : γ ∈ Ioo (0:ℝ) 1) (hη0 : 0 < η)
    (hη : η ≤ 1/20) (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L ^ A →
      ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
        WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4*k).factorial:ℝ)) →
        ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
          approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J Ψ₁)‖ ≤ 2*(C*δ/4)^n := by
  obtain ⟨C, hC, hNT⟩ := halfCell_crude_uniform hd hγ hη0 hη hηγ hC₀
  refine ⟨C, hC, fun A => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hNT A
  refine ⟨L₀, fun L hL δ hδ n hn z β γ' J Ψ₁ hΨ hDer => ?_⟩
  set r : ℝ := max 1 (Real.sqrt d)
  set μ := L^(2*γ)*δ
  set S : Fin n → ℝ := fun j =>
    2 * (|μ| * ((‖halfCellCenter (z (j,0))‖ + r) * (‖halfCellCenter (z (j,1))‖ + r))) + 2
  have hr0 : 0 ≤ r := le_trans zero_le_one (le_max_left _ _)
  have hS1 : ∀ j, 1 ≤ S j := fun j => by
    have : 0 ≤ |μ| * ((‖halfCellCenter (z (j,0))‖ + r) * (‖halfCellCenter (z (j,1))‖ + r)) := by positivity
    simp only [S]; linarith
  have hsupp : ∀ x y, halfCellAmplitude z β γ' x y ≠ 0 → ∀ j, |μ * inner ℝ (x j) (y j)| ≤ S j / 2 := by
    intro x y hW j
    have hs := halfCellAmplitude_support z β γ' x y hW j
    simp only [Shift.eval, add_zero] at hs
    have hx : ‖x j‖ ≤ ‖halfCellCenter (z (j,0))‖ + r := by
      have := norm_le_norm_add_norm_sub' (x j) (halfCellCenter (z (j,0)))
      linarith [hs.1]
    have hy : ‖y j‖ ≤ ‖halfCellCenter (z (j,1))‖ + r := by
      have := norm_le_norm_add_norm_sub' (y j) (halfCellCenter (z (j,1)))
      linarith [hs.2]
    rw [abs_mul]
    have hi := abs_real_inner_le_norm (x j) (y j)
    have h1 : |inner ℝ (x j) (y j)| ≤ (‖halfCellCenter (z (j,0))‖ + r) * (‖halfCellCenter (z (j,1))‖ + r) :=
      hi.trans (mul_le_mul hx hy (norm_nonneg _) (by positivity))
    have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg μ)
    simp only [S]
    linarith
  rw [approxSum_res_eq_filt L μ _ J Ψ₁ S (fun j => by linarith [hS1 j]) hsupp]
  exact hL₀ L hL δ hδ n hn z β γ' J S hS1 Ψ₁ hΨ hDer

end WaveTurbulence.Flower.FiltCoh
