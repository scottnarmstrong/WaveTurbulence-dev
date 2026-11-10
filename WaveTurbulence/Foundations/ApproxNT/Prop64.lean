/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Conclusion2

/-!
# DH23 Proposition 6.4 (`approxnt`), all conclusions, in the large-order range (packet NT6)

`dh23_prop_6_4` packages `approxnt_conclusion1` and `approxnt_conclusion2` with one constant `C₁`:
for `I = approxSum` (DH23 (defi)), `L^{2dn} ∫ WΨ` (`approxInt`) and `I_app = approxApp`
(DH23 (intappr)), with `B = (λ₁⋯λ_n)^{2d} (C₁ C⁺ L^{2d-2γ} δ⁻¹)^n`,

* `|I - L^{2dn} ∫ W Ψ| ≤ B L^{-γ₁+η}` (conclusion1),
* `|I_app| ≤ B` and `|I - I_app| ≤ B L^{-γ₁+η}` (conclusion2),

uniformly in `n ≤ (log L)^A` (any fixed `A`; FINDINGS F33 route R14(a)), in the box sizes
`λ_j ≥ 1`, in the triangular structure, `W`, `J` and `Ψ₁`. For a fixed `δ ∈ (0,1]` the condition
`L^{-η/2} ≤ δ` holds once `L ≥ δ^{-2/η}` (`rpow_neg_half_le`).
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-- **DH23 Proposition 6.4** (`approxnt`, `Revision_Submit.tex` L984–L1010; proof DH21 Prop 6.1,
`Inventiones-Final_Version.tex` L1504–L1657), extended to orders `n ≤ (log L)^A` and arbitrary box
sizes (`GAP.largeOrder.nt`). See `approxnt_conclusion1` and `approxnt_conclusion2` for the reading
of the hypotheses. -/
theorem dh23_prop_6_4 (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1 / 20) (hηγ : η ≤ ((d : ℝ) - 1) * (1 - γ)) (hηγ' : η ≤ γ) {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ δ : ℝ, L ^ (-(η / 2)) ≤ δ →
      δ ≤ 1 → ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A → ∀ Cplus : ℝ, 0 ≤ Cplus →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) →
      ∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
          ENNReal.ofReal (1 + 2 * Real.pi * freqNorm τ.1 τ.2) ≤ ENNReal.ofReal (Cplus ^ n) →
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ∫⁻ Ω, ENNReal.ofReal (wmax (1 - η / 2) (fun i => Ω i)) * ‖Ψ₁ Ω‖ₑ ≤
        ENNReal.ofReal (C₀ ^ n) →
      ‖approxSum L (L ^ (2 * γ) * δ) W (resProfile J Ψ₁) -
          (L : ℂ) ^ (2 * d * n) * approxInt (L ^ (2 * γ) * δ) W (resProfile J Ψ₁)‖ ≤
        (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n *
          L ^ (-gamma1 d γ + η) ∧
      ‖approxApp L δ γ J Ψ₁ W‖ ≤
          (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n ∧
      ‖approxSum L (L ^ (2 * γ) * δ) W (resProfile J Ψ₁) - approxApp L δ γ J Ψ₁ W‖ ≤
        (∏ j, lam j) ^ (2 * d) * (C₁ * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n *
          L ^ (-gamma1 d γ + η) := by
  obtain ⟨Ca, hCa, h1⟩ := approxnt_conclusion1 hd hγ hη0 hη hηγ hC₀
  obtain ⟨Cb, hCb, h2⟩ := approxnt_conclusion2 hd hγ hη0 hη hηγ hηγ' hC₀
  refine ⟨max Ca Cb, lt_max_of_lt_left hCa, fun A => ?_⟩
  obtain ⟨La, hLa⟩ := h1 A
  obtain ⟨Lb, hLb⟩ := h2 A
  refine ⟨max (max La Lb) 2, fun L hL δ hδ hδ1 n hn Cplus hCp lt _ xs ys hxs hys a b lam hlam W hWc
    hWs hW J Ψ₁ hΨ hD hH => ?_⟩
  have hL0 : 0 < L := by linarith [le_max_right (max La Lb) 2]
  have hδ0 : 0 < δ := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hδ
  have hX : 0 ≤ Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹ :=
    mul_nonneg (mul_nonneg hCp (Real.rpow_nonneg hL0.le _)) (inv_nonneg.2 hδ0.le)
  have hprod0 : 0 ≤ ∏ j, lam j := prod_nonneg fun j _ => by linarith [hlam j]
  have he : 0 ≤ L ^ (-gamma1 d γ + η) := Real.rpow_nonneg hL0.le _
  have hmono : ∀ C : ℝ, 0 ≤ C → C ≤ max Ca Cb →
      (∏ j, lam j) ^ (2 * d) * (C * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n ≤
        (∏ j, lam j) ^ (2 * d) * (max Ca Cb * Cplus * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n :=
    fun C hC0 hC => by
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ n) (by positivity)
      · have := mul_nonneg hC0 hX
        simpa only [mul_assoc] using this
      · have := mul_le_mul_of_nonneg_right hC hX
        simpa only [mul_assoc] using this
  have hLa' : La ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLb' : Lb ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have c1 := hLa L hLa' δ ⟨hδ0, hδ1⟩ n hn Cplus hCp lt xs ys hxs hys a b lam hlam W hWc hWs hW J Ψ₁
    hΨ hD
  obtain ⟨c2, c3⟩ := hLb L hLb' δ hδ hδ1 n hn Cplus hCp lt xs ys hxs hys a b lam hlam W hWc hWs hW
    J Ψ₁ hΨ hD hH
  refine ⟨c1.trans ?_, c2.trans (hmono Cb hCb.le (le_max_right _ _)), c3.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (hmono Ca hCa.le (le_max_left _ _)) he
  · exact mul_le_mul_of_nonneg_right (hmono Cb hCb.le (le_max_right _ _)) he

end WaveTurbulence.ApproxNT
