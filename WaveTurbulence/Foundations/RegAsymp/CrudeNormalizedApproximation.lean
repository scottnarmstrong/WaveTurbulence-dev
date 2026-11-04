/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.SumIntegralError
public import WaveTurbulence.Foundations.RegAsymp.NormalizedAppSize
public import WaveTurbulence.Foundations.RegAsymp.NormalizedContinuousSize

/-! # The high-temporal-frequency bound requires derivatives alone -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset
open scoped ENNReal ContDiff

/-- Crude size of the actual normalized remainder, without the maximum
moment premise. This is the high-frequency branch of the DH23 split. -/
theorem crude_normalized_approximation {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
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
      ∀ (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ (fun k => ((4*k).factorial:ℝ)) →
      ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        (approxSum L (L^(2*γ)*δ) W (resProfile J Ψ) - approxApp L δ γ J Ψ W)‖ ≤
        (∏ j, lam j)^(2*d)*(C*δ/4)^n*H := by
  obtain ⟨Ce,hCe,hErr⟩ := normalized_sum_integral_error hd hγ hη0 hη hηγ
  obtain ⟨Ci,hCi,hInt⟩ := exists_normalized_continuous_size_bound d hd
  obtain ⟨Ca,hCa,hApp⟩ := exists_normalized_app_size_bound d hd
  let K := max Ce (max Ci Ca)
  have hK : 0 < K := hCe.trans_le (le_max_left _ _)
  have hCeK : Ce ≤ K := le_max_left _ _
  have hCiK : Ci ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hCaK : Ca ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨3*K,by positivity,fun A => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hErr A
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hn hnlog H hH lt _ xs ys hxs hys a b lam hlam W hWc hWs hW J Ψ hΨ hD
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hδ0 : 0 < δ := (Real.rpow_pos_of_pos hL0 _).trans_le hδ
  have hμ := (mu_bounds (d := d) hη0 (by linarith : η ≤ 1) hηγ' hL1 hδ).1
  have hD0 (k : ℕ) : 0 ≤ ((4*k).factorial:ℝ) := by positivity
  have hΨ0 : (∫ Ω, ‖Ψ Ω‖) ≤ 1 := by
    have hh := integral_norm_wordDeriv_le hΨ hD hD0 (k := 0) Fin.elim0
    simpa [wordDeriv,iteratedFDeriv_zero_apply] using hh
  have he := hL₀ L ((le_max_left _ _).trans hL) δ hδ0 hδ1 n hn hnlog H hH
    lt xs ys hxs hys a b lam hlam W hWc hWs hW J Ψ hΨ hD
  have hi := hInt n hn lt xs ys hxs hys a b lam hlam W hWc hWs H hH hW J Ψ _ hΨ hD hD0
    1 hΨ0 L δ γ hL0 hδ0 hμ
  have ha := hApp n hn lt xs ys hxs hys a b lam hlam W hWc hWs H hH hW J Ψ 1 hΨ0 L δ γ hL0 hδ0
  simp only [mul_one] at hi ha
  have hgain : η ≤ gamma1 d γ := by
    unfold gamma1
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  have hLp : L^(-gamma1 d γ+η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1.le (by linarith)
  let B := (∏ j, lam j)^(2*d)*(K*δ/4)^n*H
  have hbox : 0 ≤ (∏ j, lam j)^(2*d) := by
    exact pow_nonneg (prod_nonneg (fun j _ => zero_le_one.trans (hlam j))) _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hb (c : ℝ) (hc : 0 < c) (hcK : c ≤ K) :
      (∏ j, lam j)^(2*d)*(c*δ/4)^n*H ≤ B := by
    have hh : c*δ/4 ≤ K*δ/4 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcK hδ0.le) (by norm_num : 0 ≤ (4:ℝ))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hh n) hbox) hH
  have he' := he.trans ((mul_le_of_le_one_right (by positivity) hLp).trans (hb Ce hCe hCeK))
  have hi' := hi.trans (hb Ci hCi hCiK)
  have ha' := ha.trans (hb Ca hCa hCaK)
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)
  let S := approxSum L (L^(2*γ)*δ) W (resProfile J Ψ)
  let I := (L:ℂ)^(2*d*n)*approxInt (L^(2*γ)*δ) W (resProfile J Ψ)
  let P := approxApp L δ γ J Ψ W
  change ‖q*(S-P)‖ ≤ _
  have htri : ‖q*(S-P)‖ ≤ ‖q*(S-I)‖+‖q*I‖+‖q*P‖ := by
    rw [show q*(S-P)=q*(S-I)+q*I-q*P by ring]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hi'' : ‖q*I‖ ≤ B := by simpa only [q,I,mul_assoc] using hi'
  have h3 : (3:ℝ) ≤ 3^n := le_self_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  calc
    _ ≤ 3*B := htri.trans (by linarith [he',hi'',ha'])
    _ ≤ (∏ j, lam j)^(2*d)*((3*K)*δ/4)^n*H := by
      rw [show (3*K)*δ/4=3*(K*δ/4) by ring,mul_pow]
      have hh := mul_le_mul_of_nonneg_right h3 hB
      dsimp only [B] at hh ⊢
      nlinarith

end WaveTurbulence.RegAsymp
