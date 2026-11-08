/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Links

/-! # D6a PROT-PTW: the per-link accounting

Each link contributes `c² ×` (its mass or its trivial supremum). Normal links give `K C₀ δ/4` (times the incoherent
gain); a pinned link gives `K 5^{2d} δ² L^{2γ}/4 ≤ K C₀ δ L²`; a selected link gives `K 5^{2d} δ / (2π M₂)`. The
products are assembled link by link. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh

theorem coupling_sq_kinetic {d : ℕ} {L γ δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    coupling d L γ δ ^ 2 * kineticLinkScale d γ δ L = δ / 4 := by
  unfold coupling kineticLinkScale
  have h1 : (L ^ ((d : ℝ) - γ)) ^ 2 = L ^ (2 * ((d : ℝ) - γ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; ring_nf
  have hp : 0 < L ^ ((d : ℝ) - γ) := Real.rpow_pos_of_pos hL _
  rw [div_pow, mul_pow, h1]
  field_simp
  ring

theorem coupling_sq_trivial {d : ℕ} {L γ δ : ℝ} (hL : 0 < L) :
    coupling d L γ δ ^ 2 * (5 * L) ^ (2 * d) = (5 : ℝ) ^ (2 * d) * δ ^ 2 * L ^ (2 * γ) / 4 := by
  unfold coupling
  have h1 : (L ^ ((d : ℝ) - γ)) ^ 2 = L ^ (2 * d) * L ^ (-(2 * γ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_natCast, ← Real.rpow_add hL]
    congr 1; push_cast; ring
  have hp : 0 < L ^ ((d : ℝ) - γ) := Real.rpow_pos_of_pos hL _
  have hq : L ^ (-(2 * γ)) = (L ^ (2 * γ))⁻¹ := Real.rpow_neg hL.le _
  have hr : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL _
  have hs : 0 < L ^ (2 * d) := pow_pos hL _
  rw [div_pow, mul_pow, h1, hq, mul_pow]
  field_simp
  norm_num

/-- Link-by-link assembly. -/
theorem link_product_le {n : ℕ} (c2 b : ℝ) (hc2 : 0 ≤ c2) (hb : 0 ≤ b) (T : Fin n → ℝ≥0∞) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (h : ∀ i, ENNReal.ofReal c2 * T i ≤ ENNReal.ofReal (b * w i)) :
    ENNReal.ofReal (c2 ^ n) * ∏ i, T i ≤ ENNReal.ofReal (b ^ n * ∏ i, w i) := by
  have hpow : ENNReal.ofReal (c2 ^ n) = ∏ _i : Fin n, ENNReal.ofReal c2 := by
    rw [ENNReal.ofReal_pow hc2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, ← Finset.prod_mul_distrib]
  refine (Finset.prod_le_prod fun i _ => h i).trans_eq ?_
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg hb (hw i)), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_fin]

/-- The incoherent weights multiply to the incoherency exponent. -/
theorem prod_incoh_weight {n : ℕ} {L : ℝ} (hL : 0 < L) (y : ℝ) (P : Fin n → Prop) [DecidablePred P] (ρ : Fin n → ℝ) :
    ∏ i, (ρ i * (if P i then L ^ (-y) else 1)) =
      (∏ i, ρ i) * L ^ (-y * ((Finset.univ.filter P).card : ℝ)) := by
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, ← Real.rpow_natCast,
    ← Real.rpow_mul hL.le]

/-! ### The three kinds of links -/

section PerLink
variable {d : ℕ} {L γ δ η K C₀ C₀' C₂ y : ℝ}

/-- A normal link: its D5a pair mass. -/
theorem per_normal (hL : 1 ≤ L) (hδ : 0 < δ) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hC₀' : C₀ ≤ C₀') (hC₂ : 0 ≤ C₂)
    (hC₂L : C₂ ≤ L ^ η) (x : ℝ) (hy : y = x - η) (P : Prop) [Decidable P] :
    ENNReal.ofReal (coupling d L γ δ ^ 2) *
        ENNReal.ofReal (K * (C₀ * kineticLinkScale d γ δ L) * (if P then C₂ * L ^ (-x) else 1)) ≤
      ENNReal.ofReal (K * C₀' * δ * (1 * (if P then L ^ (-y) else 1))) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hck := coupling_sq_kinetic (d := d) (γ := γ) hLp hδ
  have he : coupling d L γ δ ^ 2 * (K * (C₀ * kineticLinkScale d γ δ L) * (if P then C₂ * L ^ (-x) else 1)) =
      K * C₀ * (δ / 4) * (if P then C₂ * L ^ (-x) else 1) := by rw [← hck]; ring
  rw [he, one_mul]
  have hb : K * C₀ * (δ / 4) ≤ K * C₀' * δ := by
    have := mul_le_mul_of_nonneg_left hC₀' hK
    nlinarith [mul_nonneg hK hC₀]
  split_ifs
  · have hL1 : C₂ * L ^ (-x) ≤ L ^ (-y) := by
      rw [hy, show -(x - η) = η + -x by ring, Real.rpow_add hLp]
      exact mul_le_mul_of_nonneg_right hC₂L (Real.rpow_nonneg hLp.le _)
    exact mul_le_mul hb hL1 (mul_nonneg hC₂ (Real.rpow_nonneg hLp.le _))
      (mul_nonneg (mul_nonneg hK (hC₀.trans hC₀')) hδ.le)
  · rw [mul_one, mul_one]; exact hb

/-- The incoherent factor of an exceptional link costs at most `L`. -/
theorem one_le_L_mul_incoh (hL : 1 ≤ L) (hy : y ≤ 1) (P : Prop) [Decidable P] :
    1 ≤ L * (if P then L ^ (-y) else 1) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  split_ifs
  · rw [show L * L ^ (-y) = L ^ (1 + -y) by rw [Real.rpow_add hLp, Real.rpow_one]]
    exact Real.one_le_rpow hL (by linarith)
  · rw [mul_one]; exact hL

/-- A pinned link: its trivial supremum `K (5L)^{2d}`. -/
theorem per_pin (hL : 1 ≤ L) (hγ : γ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (h5 : (5 : ℝ) ^ (2 * d) ≤ C₀') (hy : y ≤ 1) (P : Prop) [Decidable P] :
    ENNReal.ofReal (coupling d L γ δ ^ 2) * ENNReal.ofReal (K * (5 * L) ^ (2 * d)) ≤
      ENNReal.ofReal (K * C₀' * δ * (L ^ 3 * (if P then L ^ (-y) else 1))) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have he : coupling d L γ δ ^ 2 * (K * (5 * L) ^ (2 * d)) = K * ((5 : ℝ) ^ (2 * d) * δ ^ 2 * L ^ (2 * γ) / 4) := by
    rw [← coupling_sq_trivial hLp]; ring
  rw [he]
  have hLγ : L ^ (2 * γ) ≤ L ^ 2 := by
    rw [show (L ^ 2 : ℝ) = L ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le hL (by push_cast; linarith)
  have hI := one_le_L_mul_incoh hL hy P
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have h5p : (0 : ℝ) ≤ 5 ^ (2 * d) := by positivity
  calc K * ((5 : ℝ) ^ (2 * d) * δ ^ 2 * L ^ (2 * γ) / 4) ≤ K * (C₀' * δ * L ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hK
        have h1 : (5 : ℝ) ^ (2 * d) * δ ^ 2 * L ^ (2 * γ) ≤ C₀' * δ * L ^ 2 := by
          apply mul_le_mul (mul_le_mul h5 hδ2 (sq_nonneg _) (h5p.trans h5)) hLγ (Real.rpow_nonneg hLp.le _)
            (mul_nonneg (h5p.trans h5) hδ.le)
        have h2 : 0 ≤ (5 : ℝ) ^ (2 * d) * δ ^ 2 * L ^ (2 * γ) := by positivity
        linarith
    _ ≤ K * (C₀' * δ * (L ^ 2 * (L * (if P then L ^ (-y) else 1)))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (h5p.trans h5) hδ.le)
        nlinarith [sq_nonneg L]
    _ = _ := by ring

/-- A selected link: the reciprocal weight `2K/(π δ L^{2γ} M₂)` times `(5L)^{2d}`. -/
theorem per_sel (hL : 1 ≤ L) (hδ : 0 < δ) (hK : 0 ≤ K) (h5 : (5 : ℝ) ^ (2 * d) ≤ C₀') {M₂ : ℝ} (hM₂ : 0 < M₂)
    (hy : y ≤ 1) (P : Prop) [Decidable P] :
    ENNReal.ofReal (coupling d L γ δ ^ 2) *
        ENNReal.ofReal (2 * K / (Real.pi * δ * L ^ (2 * γ) * M₂) * (5 * L) ^ (2 * d)) ≤
      ENNReal.ofReal (K * C₀' * δ * (L ^ 3 * M₂⁻¹ * (if P then L ^ (-y) else 1))) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hr : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hLp _
  have he : coupling d L γ δ ^ 2 * (2 * K / (Real.pi * δ * L ^ (2 * γ) * M₂) * (5 * L) ^ (2 * d)) =
      K * (5 : ℝ) ^ (2 * d) * δ / (2 * Real.pi * M₂) := by
    rw [mul_comm (2 * K / _), ← mul_assoc, coupling_sq_trivial hLp]
    field_simp
    ring
  rw [he]
  have hI := one_le_L_mul_incoh hL hy P
  have hL3 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h5p : (0 : ℝ) ≤ 5 ^ (2 * d) := by positivity
  have hpos : 0 ≤ K * C₀' * δ * M₂⁻¹ := by
    have : 0 ≤ C₀' := h5p.trans h5
    positivity
  calc K * (5 : ℝ) ^ (2 * d) * δ / (2 * Real.pi * M₂) ≤ K * C₀' * δ * M₂⁻¹ := by
        rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
        have h1 : K * 5 ^ (2 * d) * δ * (2 * Real.pi)⁻¹ ≤ K * C₀' * δ := by
          have h2 : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hπ
          have h3 : K * 5 ^ (2 * d) * δ ≤ K * C₀' * δ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hK) hδ.le
          have h4 : 0 ≤ K * 5 ^ (2 * d) * δ := by positivity
          nlinarith [inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ 2 * Real.pi)]
        exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hM₂.le)
    _ ≤ K * C₀' * δ * M₂⁻¹ * (L ^ 2 * (L * (if P then L ^ (-y) else 1))) := by
        have : 1 ≤ L ^ 2 * (L * (if P then L ^ (-y) else 1)) := one_le_mul_of_one_le_of_one_le hL3 hI
        nlinarith
    _ = _ := by ring

end PerLink

end WaveTurbulence.Flower.ProtPtw
