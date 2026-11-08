/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltNT.Concl
public import WaveTurbulence.Foundations.Flower.FiltNT.ContCell
public import WaveTurbulence.Foundations.RegAsymp.CrudeNormalizedSum
public import WaveTurbulence.Foundations.RegAsymp.Normalization

/-! # FILT-NT: the crude normalized sum for the filtered profile (o82 Thm 10.1 (10.5))

The chain of main's `RegAsymp.crude_normalized_sum` (`ContinuousIntegralSize`, `NormalizedContinuousSize`,
`SumIntegralError`, `CrudeNormalizedSum`) with `resProfile J Ψ` replaced by `filtProf J S Ψ`, uniformly in `S_j ≥ 1`,
and with the Gevrey constant `C₀^n (4k)!` (so `∫‖Ψ‖ ≤ C₀^n`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.ApproxNT WaveTurbulence.RegAsymp Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltNT

theorem filt_integral_size {d : ℕ} (hd : 3 ≤ d) (Kp : ℝ)
    (hb1 : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ ≤ Kp) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      ∀ H : ℝ, 0 ≤ H →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (D : ℕ → ℝ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ D → (∀ k, 0 ≤ D k) →
      ∀ D0 : ℝ, (∫ Ω, ‖Ψ Ω‖) ≤ D0 → ∀ μ : ℝ, 1 < μ →
      ‖approxInt μ W (filtProf J S Ψ)‖ ≤ (∏ j, lam j)^(2*d)*(C/μ)^n*D0*H := by
  obtain ⟨K,hK,hcell⟩ := filt_continuous_cell_size hd Kp hb1
  let C : ℝ := 7^(2*d)*K
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro n hn lt _ xs ys hxs hys a b lam hlam W hWc hWs H hH hW J S hS Ψ D hΨ hD hD0 D0 hD0' μ hμ
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  have hμ0 : 0 < μ := by linarith
  have hD00 : 0 ≤ D0 := (integral_nonneg (fun _ => norm_nonneg _)).trans hD0'
  obtain ⟨hF,hinv,hI,hInt⟩ := fourierAmplitude_setup hn hxs hys hWc hWs hH hW
  have hFmass := integral_norm_fourierW_le hF hI hInt
  let Q := (cellBox_finite hxs hys a b lam).toFinset
  let P := fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
    filtProf J S Ψ (fun j => μ*inner ℝ (z.1 j) (z.2 j))
  have hPc : Continuous P := (continuous_filtProf J S hΨ.continuous).comp
    (continuous_pi (fun j => continuous_const.mul
      (((continuous_apply j).comp continuous_fst).inner ((continuous_apply j).comp continuous_snd))))
  have hhm (pq) : Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2*P z) := (continuous_cellWeight pq).mul hPc
  have hhs (pq) : HasCompactSupport (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2*P z) := (hasCompactSupport_cellWeight pq).mul_right
  have hh (pq) : Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2*P z) := (hhm pq).integrable_of_hasCompactSupport (hhs pq)
  have hcelli (pq) : Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      W z.1 z.2*cellWeight pq z.1 z.2*P z) := by
    apply ((hWc.mul (hhm pq)).integrable_of_hasCompactSupport (hhs pq).mul_left).congr
    exact Filter.Eventually.of_forall (fun z => by simp only [Function.uncurry,Pi.mul_apply,mul_assoc])
  have hbound (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
      (τ : (Fin n → Mom d) × (Fin n → Mom d)) :
      ‖multiInt μ (filtProf J S Ψ) (cellData pq τ).p (cellData pq τ).q
        (cellData pq τ).ξ (cellData pq τ).ζ‖ ≤ (K/μ)^n*D0 := by
    simpa only [Fintype.card_fin] using hcell J S hS Ψ D hΨ hD hD0 D0 hD0' μ hμ0
      (cellData pq τ)
  have hpiece (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
      ‖∫ z : (Fin n → Mom d) × (Fin n → Mom d), W z.1 z.2*cellWeight pq z.1 z.2*P z‖ ≤
        H*((K/μ)^n*D0) := by
    obtain ⟨_,heq⟩ := approxInt_cell μ hinv hF (filtProf J S Ψ) pq (hh pq) (hhm pq)
    change ‖approxInt μ (fun x y => W x y*cellWeight pq x y) (filtProf J S Ψ)‖ ≤ _
    rw [heq]
    apply (norm_integral_le_of_norm_le (hF.norm.mul_const ((K/μ)^n*D0)) (Filter.Eventually.of_forall fun τ => ?_)).trans
      (show (∫ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖*((K/μ)^n*D0)) ≤
        H*((K/μ)^n*D0) by rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right hFmass (by positivity))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound pq τ) (norm_nonneg _)
  rw [approxInt_eq_sum_cells hxs hys hWs μ (filtProf J S Ψ) hcelli]
  calc
    _ ≤ ∑ pq ∈ Q, ‖∫ z : (Fin n → Mom d) × (Fin n → Mom d),
        W z.1 z.2*cellWeight pq z.1 z.2*P z‖ := norm_sum_le _ _
    _ ≤ ∑ _pq ∈ Q, H*((K/μ)^n*D0) := sum_le_sum (fun pq _ => hpiece pq)
    _ = (Q.card:ℝ)*(H*((K/μ)^n*D0)) := by simp
    _ ≤ (7^(2*d*n)*(∏ j, lam j)^(2*d))*(H*((K/μ)^n*D0)) :=
      mul_le_mul_of_nonneg_right (card_cells_le hxs hys a b hlam) (by positivity)
    _ = _ := by
      have he : (C/μ)^n = (7^(2*d))^n*(K/μ)^n := by dsimp only [C]; rw [mul_div_assoc,mul_pow]
      rw [he,pow_mul]
      ring


theorem filt_normalized_continuous_size {d : ℕ} (hd : 3 ≤ d) (Kp : ℝ)
    (hb1 : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ ≤ Kp) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      ∀ H : ℝ, 0 ≤ H →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (D : ℕ → ℝ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ D → (∀ k, 0 ≤ D k) →
      ∀ D0 : ℝ, (∫ Ω, ‖Ψ Ω‖) ≤ D0 → ∀ L δ γ : ℝ, 0 < L → 0 < δ → 1 < L^(2*γ)*δ →
      ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) * (L:ℂ)^(2*d*n) * approxInt (L^(2*γ)*δ) W (filtProf J S Ψ)‖ ≤
        (∏ j, lam j)^(2*d)*(C*δ/4)^n*D0*H := by
  obtain ⟨C,hC,hSz⟩ := filt_integral_size hd Kp hb1
  refine ⟨C,hC,?_⟩
  intro n hn lt _ xs ys hxs hys a b lam hlam W hWc hWs H hH hW J S hS Ψ D hΨ hD hD0 D0 hΨ0 L δ γ hL hδ hμ
  have hInt := hSz n hn lt xs ys hxs hys a b lam hlam W hWc hWs H hH hW J S hS Ψ D hΨ hD hD0 D0 hΨ0
    (L^(2*γ)*δ) hμ
  have hD00 : 0 ≤ D0 := (integral_nonneg (fun _ => norm_nonneg _)).trans hΨ0
  let q : ℝ := (δ/(2*L^((d:ℝ)-γ)))^(2*n)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  change ‖(q:ℂ)*(L:ℂ)^(2*d*n)*approxInt (L^(2*γ)*δ) W (filtProf J S Ψ)‖ ≤ _
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hq,abs_of_pos hL]
  calc
    _ ≤ (q*L^(2*d*n))*((∏ j, lam j)^(2*d)*(C/(L^(2*γ)*δ))^n*D0*H) :=
      mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = _ := by
      have he : L^(2*d)*(C/(L^(2*γ)*δ)) = C*(L^(2*(d:ℝ)-2*γ)*δ⁻¹) := by
        calc _ = C*(L^(2*d)/(L^(2*γ)*δ)) := by ring
             _ = _ := by rw [Lpow_div_mu hL]
      have hs := normalized_scale (γ := γ) n d hL hδ.ne' C
      change q*(C*L^(2*(d:ℝ)-2*γ)*δ⁻¹)^n = (C*δ/4)^n at hs
      calc
        _ = (∏ j, lam j)^(2*d)*(q*(L^(2*d)*(C/(L^(2*γ)*δ)))^n)*D0*H := by
          rw [mul_pow,← pow_mul]; ring
        _ = _ := by rw [he,show C*(L^(2*(d:ℝ)-2*γ)*δ⁻¹)=C*L^(2*(d:ℝ)-2*γ)*δ⁻¹ by ring,hs]


theorem filt_normalized_sum_integral_error {d : ℕ} (hd : 3 ≤ d) (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hb : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ * (1 + s ^ 2) ^ d ≤ Kp) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L ^ A →
      ∀ H : ℝ, 0 ≤ H →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ (fun k => C₀ ^ n * ((4*k).factorial:ℝ)) →
      ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        (approxSum L (L^(2*γ)*δ) W (filtProf J S Ψ) -
          (L:ℂ)^(2*d*n)*approxInt (L^(2*γ)*δ) W (filtProf J S Ψ))‖ ≤
        (∏ j, lam j)^(2*d)*(C*δ/4)^n*H*L^(-gamma1 d γ+η) := by
  obtain ⟨C,hC,hNT⟩ := filt_conclusion1 hd Kp hKp hb hγ hη0 hη hηγ hC₀
  refine ⟨C,hC,fun A => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT A
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hnp hn H hH lt _ xs ys hxs hys a b lam hlam W hWc hWs hW J S hS Ψ hΨ hD
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hL)
  let Cp : ℝ := H^((n:ℝ)⁻¹)
  have hCp : 0 ≤ Cp := Real.rpow_nonneg hH _
  have hpow : Cp^n=H := Real.rpow_inv_natCast_pow hH (Nat.ne_of_gt hnp)
  have hW' : (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
      ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal (Cp^n) := by rwa [hpow]
  have herr := hL₀ L ((le_max_left _ _).trans hL) δ ⟨hδ,hδ1⟩ n hn Cp hCp lt xs ys hxs hys
    a b lam hlam W hWc hWs hW' J S hS Ψ hΨ hD
  let q : ℝ := (δ/(2*L^((d:ℝ)-γ)))^(2*n)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  change ‖(q:ℂ)*_‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq]
  apply (mul_le_mul_of_nonneg_left herr hq).trans_eq
  have hs := normalized_scale (γ := γ) n d hL0 hδ.ne' (C*Cp)
  change q*(C*Cp*L^(2*(d:ℝ)-2*γ)*δ⁻¹)^n = (C*Cp*δ/4)^n at hs
  have hp : (C*Cp*δ/4)^n = (C*δ/4)^n*H := by
    rw [show C*Cp*δ/4=(C*δ/4)*Cp by ring,mul_pow,hpow]
  calc
    _ = (∏ j, lam j)^(2*d)*(q*(C*Cp*L^(2*(d:ℝ)-2*γ)*δ⁻¹)^n)*L^(-gamma1 d γ+η) := by ring
    _ = _ := by rw [hs,hp]; ring


/-- **o82 Thm 10.1 (10.5), the crude normalized sum for the filtered profile**: main's `RegAsymp.crude_normalized_sum`
with `filtProf J S Ψ`, scales `S_j ≥ 1`, and Gevrey constant `C₀^n (4k)!`. -/
theorem filt_crude_normalized_sum {d : ℕ} (hd : 3 ≤ d) (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hb : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ * (1 + s ^ 2) ^ d ≤ Kp) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L ^ (-(η/2)) ≤ δ → δ ≤ 1 → ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L ^ A →
      ∀ H : ℝ, 0 ≤ H →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (S : Fin n → ℝ), (∀ j, 1 ≤ S j) →
      ∀ (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ (fun k => C₀ ^ n * ((4*k).factorial:ℝ)) →
      ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*δ) W (filtProf J S Ψ)‖ ≤
        (∏ j, lam j)^(2*d)*(C*δ/4)^n*H := by
  have hb1 : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ ≤ Kp := fun S hS s =>
    le_trans (le_mul_of_one_le_right (norm_nonneg _)
      (one_le_pow₀ (by nlinarith [sq_nonneg s]))) (hb S hS s)
  obtain ⟨Ce,hCe,hErr⟩ := filt_normalized_sum_integral_error hd Kp hKp hb hγ hη0 hη hηγ hC₀
  obtain ⟨Ci,hCi,hInt⟩ := filt_normalized_continuous_size hd Kp hb1
  let K := max Ce (Ci * C₀)
  have hCiC : 0 < Ci * C₀ := mul_pos hCi (by linarith)
  have hK : 0 < K := hCe.trans_le (le_max_left _ _)
  have hCeK : Ce ≤ K := le_max_left _ _
  have hCiK : Ci * C₀ ≤ K := le_max_right _ _
  refine ⟨2*K,by positivity,fun A => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hErr A
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hn hnlog H hH lt _ xs ys hxs hys a b lam hlam W hWc hWs hW J S hS Ψ hΨ hD
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hδ0 : 0 < δ := (Real.rpow_pos_of_pos hL0 _).trans_le hδ
  have hμ := (mu_bounds (d := d) hη0 (by linarith : η ≤ 1) hηγ' hL1 hδ).1
  have hD0 (k : ℕ) : 0 ≤ C₀ ^ n * ((4*k).factorial:ℝ) := by
    have : 0 ≤ C₀ := by linarith
    positivity
  have hΨ0 : (∫ Ω, ‖Ψ Ω‖) ≤ C₀ ^ n := by
    have hh := integral_norm_wordDeriv_le hΨ hD hD0 (k := 0) Fin.elim0
    simpa [wordDeriv,iteratedFDeriv_zero_apply] using hh
  have he := hL₀ L ((le_max_left _ _).trans hL) δ hδ0 hδ1 n hn hnlog H hH
    lt xs ys hxs hys a b lam hlam W hWc hWs hW J S hS Ψ hΨ hD
  have hi := hInt n hn lt xs ys hxs hys a b lam hlam W hWc hWs H hH hW J S hS Ψ _ hΨ hD hD0
    (C₀ ^ n) hΨ0 L δ γ hL0 hδ0 hμ
  have hgain : η ≤ gamma1 d γ := by
    unfold gamma1
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  have hLp : L^(-gamma1 d γ+η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1.le (by linarith)
  let B := (∏ j, lam j)^(2*d)*(K*δ/4)^n*H
  have hbox : 0 ≤ (∏ j, lam j)^(2*d) := by
    exact pow_nonneg (prod_nonneg (fun j _ => zero_le_one.trans (hlam j))) _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hb' (c : ℝ) (hc : 0 < c) (hcK : c ≤ K) :
      (∏ j, lam j)^(2*d)*(c*δ/4)^n*H ≤ B := by
    have hh : c*δ/4 ≤ K*δ/4 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcK hδ0.le) (by norm_num : 0 ≤ (4:ℝ))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hh n) hbox) hH
  have he' := he.trans ((mul_le_of_le_one_right (by positivity) hLp).trans (hb' Ce hCe hCeK))
  have hi2 : ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) * (L:ℂ)^(2*d*n) *
      approxInt (L^(2*γ)*δ) W (filtProf J S Ψ)‖ ≤
      (∏ j, lam j)^(2*d)*((Ci*C₀)*δ/4)^n*H := by
    refine hi.trans (le_of_eq ?_)
    rw [show (Ci*C₀)*δ/4 = (Ci*δ/4)*C₀ by ring, mul_pow]
    ring
  have hi' := hi2.trans (hb' _ hCiC hCiK)
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)
  let S' := approxSum L (L^(2*γ)*δ) W (filtProf J S Ψ)
  let I := (L:ℂ)^(2*d*n)*approxInt (L^(2*γ)*δ) W (filtProf J S Ψ)
  change ‖q*S'‖ ≤ _
  have htri : ‖q*S'‖ ≤ ‖q*(S'-I)‖+‖q*I‖ := by
    rw [show q*S'=q*(S'-I)+q*I by ring]
    exact norm_add_le _ _
  have hi'' : ‖q*I‖ ≤ B := by simpa only [q,I,mul_assoc] using hi'
  have h2 : (2:ℝ) ≤ 2^n := le_self_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  calc
    _ ≤ 2*B := htri.trans (by linarith [he',hi''])
    _ ≤ (∏ j, lam j)^(2*d)*((2*K)*δ/4)^n*H := by
      rw [show (2*K)*δ/4=2*(K*δ/4) by ring,mul_pow]
      have hh := mul_le_mul_of_nonneg_right h2 hB
      dsimp only [B] at hh ⊢
      nlinarith

end WaveTurbulence.Flower.FiltNT
