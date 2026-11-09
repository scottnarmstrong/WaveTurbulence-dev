/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Counts2
/-! **L6E GHOST, part 4: the real inequalities without `8η ≤ 2γ - 1`** (M1-R2 NOTES §10.1, Theorem 6.1 (c), (d);
REF-M1R2 R2).

Every lemma assumes the `TriReal` inequalities only (`3 ≤ d`, `0 < γ < 1`, `0 < η`, `200η ≤ γ`, `200η ≤ 1 - γ`,
`e ≤ L`, `0 < δ ≤ 1`, `1 ≤ C₁`), for every `0 < γ < 1`.
* `arith_B2_beta_low`: one new `α`-atom and one `β`-ghost, main's count (`min γ (1-γ) ≤ γ` in place of `≤ 1 - γ`).
* `arith_B2_alpha_low`: one new `α`-atom and one `α`-ghost, with the **ghost-label slab** (REF-M1R2 R2: needed wherever
  `8η > 2γ - 1`; here for all `γ`). Margin `(d-1)(γ-η) - γ₀ - 2η² - η³`.
* `arith_P5_alpha2_core`: three singleton blocks, two `α`-ghosts, one slab (the ghost `Q₂`), with a transfer `L^τ`, under
  an exponent condition on the other ghost; its three uses: `arith_P5_alpha2_kappa` (a `κ = 50` ghost),
  `arith_P5_alpha2_label` (the other label `≤ L^{-γ₀-4η}`), and `arith_P5_alpha2_NC` (`τ = 5η`, no condition). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

/-- One new `α`-atom, one `β`-ghost: `ΔF = 0`, `ΔV_β = 0` (main's `arith_B2_beta` without `8η ≤ 2γ - 1`). -/
theorem arith_B2_beta_low (d : ℕ) {L γ η δ C₁ na R ρ : ℝ} (c κ : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ)
    (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R)) :
    (((min ((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) *
        Real.log L ^ 12 ≤
      (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) * excessRHS L γ η [(R, κ)] 0 0 := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have h1 := lhs_ba d c κ hd hγ0 hγ1 hη hη1 hη2 hL hδ0 hδ hC hna0 hna hRl hRu hρ
  refine h1.trans ?_
  rw [excessRHS_one L γ η R κ hL0]
  have hlog := log_pow_le_eta (c + 12) (by omega) hL1 hη
  have hT : 0 ≤ L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R := by positivity
  have hexp : L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) ≤
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((0 : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((0 : ℤ)) : ℝ))) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have h1 : min γ (1 - γ) ≤ γ := min_le_left _ _
    push_cast
    have : η ^ 2 ≤ η := by nlinarith
    have : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 3]
    nlinarith
  calc 3 * 5 ^ d * 5 ^ d * Real.log L ^ (c + 12) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) *
        (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R)
      ≤ 3 * 5 ^ d * 5 ^ d * ((((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2)) *
          (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2))) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
        gcongr
    _ = (3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
          ((L ^ (η ^ 2) * (L ^ (min γ (1 - γ)) * L ^ (-(3 * γ / 2 - η / 2)))) *
          (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hT) (by positivity)

/-- The constant of the ghost-label two-block bound. -/
noncomputable def constB2 (d c : ℕ) (η : ℝ) : ℝ := 9 * d * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)

theorem constB2_nonneg (d c : ℕ) (η : ℝ) : 0 ≤ constB2 d c η := by unfold constB2; positivity

/-- The count `slab_ν · ball` of the ghost-label two-block bound, with the logarithms kept (cf. main's `lhs_ba`). -/
theorem lhs_B2_nu (d : ℕ) {L γ η δ C₁ na R ρ Qg : ℝ} (c κ : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ)
    (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (hQl : L⁻¹ ≤ Qg) (hQu : Qg ≤ L ^ (-γ + η)) :
    (((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2) / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) *
        (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      9 * d * 5 ^ d * 5 ^ d * Real.log L ^ (c + 12) * (L ^ (-γ) / Qg) * L ^ (-(3 * γ / 2 - η / 2)) *
        (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hQ0 : 0 < Qg := lt_of_lt_of_le (inv_pos.2 hL0) hQl
  have hdR : (0 : ℝ) < d := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hq0 := qq_nonneg hδ0.le (zero_le_one.trans hC)
  have hdq2 := delta_inv_qq_sq hδ0 hC
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hT : 0 ≤ L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R := by positivity
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hmono : ⌊2 * X / (Qg / 2 * L / d)⌋₊ ≤ ⌊2 * (2 * X) / (Qg / 2 * L / d)⌋₊ := by
    apply Nat.floor_le_floor
    have h1 : 0 < Qg / 2 * L / d := by positivity
    exact div_le_div_of_nonneg_right (by linarith) h1.le
  have hF := Fnu_bound d c hd hγ0 hγ1 hη hη2 hL hδ0 hδ hC hna0 hna hQl hQu rfl
  rw [← hX] at hF ⊢
  have hA := atom_factor d κ hd hγ0 hγ1 hη hη1 hη2 hL hRl hRu hρ
  rw [rankFactor_nat d L γ δ C₁ hL0 2]
  obtain ⟨S1, hS1⟩ : ∃ S1 : ℝ, S1 = (((⌊2 * (2 * X) / (Qg / 2 * L / d)⌋₊ + 1) *
    (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d := ⟨_, rfl⟩
  rw [← hS1] at hF
  rw [← hB] at hA
  have hN : (((⌊2 * X / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) *
        (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℝ) ≤ S1 * B := by
    rw [hS1, hB]
    have : ((⌊2 * X / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) ≤
        ((⌊2 * (2 * X) / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) * (⌊2 * ρ * L⌋₊ + 1) ^ d := by
      gcongr
    calc _ ≤ ((((⌊2 * (2 * X) / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) *
          (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast this
      _ = _ := by push_cast; ring
  have hS10 : 0 ≤ S1 := by rw [hS1]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hLn : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hL0.le _
  have hP0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  calc _ ≤ (S1 * B) * ((L ^ (-((d : ℝ) - γ))) ^ 2 * qq δ C₁ ^ 2) * Real.log L ^ 12 := by gcongr
    _ = (S1 * L ^ (-((d : ℝ) - γ)) * qq δ C₁) * (B * L ^ (-((d : ℝ) - γ))) * qq δ C₁ * Real.log L ^ 12 := by ring
    _ ≤ (9 * d * 5 ^ d * (δ⁻¹ * qq δ C₁) * Real.log L ^ c * (L ^ (-γ) / Qg)) *
          (5 ^ d * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) * L ^ (-(3 * γ / 2 - η / 2))) * qq δ C₁ *
            Real.log L ^ 12 := by gcongr
    _ = (9 * d * 5 ^ d * 5 ^ d) * (δ⁻¹ * qq δ C₁ ^ 2) * Real.log L ^ (c + 12) * (L ^ (-γ) / Qg) *
          L ^ (-(3 * γ / 2 - η / 2)) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by ring
    _ ≤ (9 * d * 5 ^ d * 5 ^ d) * 1 * Real.log L ^ (c + 12) * (L ^ (-γ) / Qg) *
          L ^ (-(3 * γ / 2 - η / 2)) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by gcongr
    _ = _ := by ring

/-- **One new `α`-atom, one `α`-ghost, with the ghost-label slab** (REF-M1R2 R2; all `0 < γ < 1`): `ΔF = 0`,
`ΔV_β = 1`, refund `T(Q_g, κ_g)⁻¹`. The slab width is read off the ghost's gap `‖gap‖ ≥ Q_g/2`. -/
theorem arith_B2_alpha_low (d : ℕ) {L γ η δ C₁ na R ρ Qg : ℝ} (c κ κg : ℕ) (hd : 3 ≤ d) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ)
    (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η))
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (hQl : L⁻¹ ≤ Qg) (hQu : Qg ≤ L ^ (-γ + η)) :
    (((⌊2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2) / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) *
        (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      constB2 d c η * (excessRHS L γ η [(R, κ)] 0 1 / (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hQ0 : 0 < Qg := lt_of_lt_of_le (inv_pos.2 hL0) hQl
  refine (lhs_B2_nu d c κ hd hγ0 hγ1 hη hη1 hη2 hL hδ0 hδ hC hna0 hna hRl hRu hρ hQl hQu).trans ?_
  rw [excessRHS_one L γ η R κ hL0]
  have hT : 0 ≤ L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R := by positivity
  have hTg : 0 < L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg := by positivity
  have hlog := log_pow_le_eta (c + 12) (by omega) hL1 hη
  have hexp : L ^ (η ^ 2) * (L ^ (-γ) / Qg) * L ^ (-(3 * γ / 2 - η / 2)) * (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg) ≤
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((0 : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((1 : ℤ)) : ℝ))) := by
    have e : L ^ (η ^ 2) * (L ^ (-γ) / Qg) * L ^ (-(3 * γ / 2 - η / 2)) * (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg) =
        L ^ (η ^ 2 + -γ + -(3 * γ / 2 - η / 2) + ((γ + 3 * η) / 2 - (κg : ℝ) * η)) := by
      rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0]; field_simp
    rw [e]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have h1 : min γ (1 - γ) ≤ γ := min_le_left _ _
    have hkg : (0 : ℝ) ≤ (κg : ℝ) * η := by positivity
    push_cast
    have : η ^ 2 ≤ η := by nlinarith
    have : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 3]
    nlinarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = L ^ (η ^ 2) * (L ^ (-γ) / Qg) * L ^ (-(3 * γ / 2 - η / 2)) *
      (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg) := ⟨_, rfl⟩
  rw [← hY] at hexp
  calc 9 * d * 5 ^ d * 5 ^ d * Real.log L ^ (c + 12) * (L ^ (-γ) / Qg) * L ^ (-(3 * γ / 2 - η / 2)) *
        (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R)
      ≤ 9 * d * 5 ^ d * 5 ^ d * ((((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) * L ^ (η ^ 2)) * (L ^ (-γ) / Qg) *
          L ^ (-(3 * γ / 2 - η / 2)) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) := by gcongr
    _ = constB2 d c η * (Y * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) /
            (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg)) := by
        rw [hY]; unfold constB2; field_simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (constB2_nonneg d c η)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hT) hTg.le

/-- **Two `α`-ghosts, one slab (that of `Q₂`), with a transfer `L^τ`**: the bound holds whenever the other ghost
satisfies `L^{3η - (κ₁+κ₂)η} Q₁ ≤ L^{-γ₀ - 4η² - η³ + τ}`. -/
theorem arith_P5_alpha2_core (d : ℕ) {L γ η δ C₁ na Q₁ Q₂ ρ τ : ℝ} (c κ₁ κ₂ gb : ℕ) (hgb : gb ≤ 1) (hd : 3 ≤ d)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQ₁l : L⁻¹ ≤ Q₁)
    (hQ₂l : L⁻¹ ≤ Q₂) (hQ₂u : Q₂ ≤ L ^ (-γ + η)) (hρ : ρ = Q₂ / 2)
    (hexp : L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) * Q₁ ≤ L ^ (-min γ (1 - γ) - 4 * η ^ 2 - η ^ 3 + τ)) :
    (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) * L ^ τ /
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hQ₁0 : 0 < Q₁ := lt_of_lt_of_le (inv_pos.2 hL0) hQ₁l
  have hQ₂0 : 0 < Q₂ := lt_of_lt_of_le (inv_pos.2 hL0) hQ₂l
  have h1 := lhs_nu d c hd hγ0 hγ1 hη hη2 hL hδ0 hδ hC hna0 hna hQ₂l hQ₂u hρ
  rw [excessRHS_nil L γ η hL0]
  refine h1.trans ?_
  have hT : 0 < (L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂) := by
    positivity
  have hK0 : 0 ≤ 9 * (d : ℝ) * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hK0
  rw [le_div_iff₀ hT]
  have hE : -η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((-(gb : ℤ) : ℤ)) : ℝ) -
      (min γ (1 - γ) + 2 * η ^ 2) * (((1 - 2 * (gb : ℤ) : ℤ)) : ℝ)) =
        -η ^ 3 - min γ (1 - γ) - 2 * η ^ 2 - (gb : ℝ) * η ^ 2 := by
    push_cast; ring
  rw [hE]
  have hg : (gb : ℝ) ≤ 1 := by exact_mod_cast hgb
  calc L ^ (η ^ 2) * (L ^ (-γ) / Q₂) * ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) *
        (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))
      = L ^ (η ^ 2) * (L ^ (-γ) * L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η)) *
          Q₁ := by field_simp
    _ = L ^ (η ^ 2) * (L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) * Q₁) := by
        have e : L ^ (-γ) * L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) =
            L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
        rw [e]; ring
    _ ≤ L ^ (η ^ 2) * L ^ (-min γ (1 - γ) - 4 * η ^ 2 - η ^ 3 + τ) := by gcongr
    _ = L ^ (η ^ 2 + (-min γ (1 - γ) - 4 * η ^ 2 - η ^ 3)) * L ^ τ := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
    _ ≤ L ^ (-η ^ 3 - min γ (1 - γ) - 2 * η ^ 2 - (gb : ℝ) * η ^ 2) * L ^ τ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith [sq_nonneg η]))
          (by positivity)

/-- Two `α`-ghosts, one of them with `κ = 50` (Theorem 6.1 (d), crit-free): no transfer. -/
theorem arith_P5_alpha2_kappa (d : ℕ) {L γ η δ C₁ na Q₁ Q₂ ρ : ℝ} (c κ₁ κ₂ gb : ℕ) (hgb : gb ≤ 1) (hd : 3 ≤ d)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQ₁l : L⁻¹ ≤ Q₁)
    (hQ₁u : Q₁ ≤ L ^ (-γ + η)) (hQ₂l : L⁻¹ ≤ Q₂) (hQ₂u : Q₂ ≤ L ^ (-γ + η)) (hρ : ρ = Q₂ / 2)
    (hκ : κ₁ = 50 ∨ κ₂ = 50) :
    (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) /
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have h := arith_P5_alpha2_core d (τ := 0) c κ₁ κ₂ gb hgb hd hγ0 hγ1 hη hη2 hL hδ0 hδ hC hna0 hna hQ₁l hQ₂l hQ₂u hρ
    (by
      have hk : (50 : ℝ) ≤ (κ₁ : ℝ) + κ₂ := by
        rcases hκ with h | h <;> rw [h] <;> push_cast <;> linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ κ₁),
          (Nat.cast_nonneg _ : (0 : ℝ) ≤ κ₂)]
      calc L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) * Q₁ ≤ L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) * L ^ (-γ + η) := by gcongr
        _ = L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η + (-γ + η)) := by rw [← Real.rpow_add hL0]
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le hL1
          have : min γ (1 - γ) ≤ γ := min_le_left _ _
          have : η ^ 2 ≤ η := by nlinarith
          have : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 3]
          nlinarith)
  rwa [Real.rpow_zero, mul_one] at h

/-- Two `α`-ghosts, the label of the non-slab ghost `≤ L^{-γ₀-4η}` (Theorem 6.1 (d), crit-free): no transfer. -/
theorem arith_P5_alpha2_label (d : ℕ) {L γ η δ C₁ na Q₁ Q₂ ρ : ℝ} (c κ₁ κ₂ gb : ℕ) (hgb : gb ≤ 1) (hd : 3 ≤ d)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQ₁l : L⁻¹ ≤ Q₁)
    (hQ₁c : Q₁ ≤ L ^ (-min γ (1 - γ) - 4 * η)) (hQ₂l : L⁻¹ ≤ Q₂) (hQ₂u : Q₂ ≤ L ^ (-γ + η)) (hρ : ρ = Q₂ / 2) :
    (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) /
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have h := arith_P5_alpha2_core d (τ := 0) c κ₁ κ₂ gb hgb hd hγ0 hγ1 hη hη2 hL hδ0 hδ hC hna0 hna hQ₁l hQ₂l hQ₂u hρ
    (by
      have hk : (0 : ℝ) ≤ ((κ₁ : ℝ) + κ₂) * η := by positivity
      calc L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) * Q₁ ≤ L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) *
            L ^ (-min γ (1 - γ) - 4 * η) := by gcongr
        _ = L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η + (-min γ (1 - γ) - 4 * η)) := by rw [← Real.rpow_add hL0]
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le hL1
          have h200 : η ≤ 1 / 200 := by linarith
          have : η ^ 2 ≤ η / 200 := by nlinarith
          have : η ^ 3 ≤ η ^ 2 := by nlinarith [sq_nonneg η]
          nlinarith)
  rwa [Real.rpow_zero, mul_one] at h

/-- Two `α`-ghosts, **near-collinear** (Theorem 6.1 (c)): the bound with the transfer `L^{5η}`, no condition. -/
theorem arith_P5_alpha2_NC (d : ℕ) {L γ η δ C₁ na Q₁ Q₂ ρ : ℝ} (c κ₁ κ₂ gb : ℕ) (hgb : gb ≤ 1) (hd : 3 ≤ d)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQ₁l : L⁻¹ ≤ Q₁)
    (hQ₁u : Q₁ ≤ L ^ (-γ + η)) (hQ₂l : L⁻¹ ≤ Q₂) (hQ₂u : Q₂ ≤ L ^ (-γ + η)) (hρ : ρ = Q₂ / 2) :
    (((⌊2 * (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      (9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        (excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) * L ^ (5 * η) /
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  refine arith_P5_alpha2_core d c κ₁ κ₂ gb hgb hd hγ0 hγ1 hη hη2 hL hδ0 hδ hC hna0 hna hQ₁l hQ₂l hQ₂u hρ ?_
  have hk : (0 : ℝ) ≤ ((κ₁ : ℝ) + κ₂) * η := by positivity
  calc L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) * Q₁ ≤ L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η) * L ^ (-γ + η) := by gcongr
    _ = L ^ (3 * η - ((κ₁ : ℝ) + κ₂) * η + (-γ + η)) := by rw [← Real.rpow_add hL0]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hL1
      have : min γ (1 - γ) ≤ γ := min_le_left _ _
      have h200 : η ≤ 1 / 200 := by linarith
      have : η ^ 2 ≤ η / 200 := by nlinarith
      have : η ^ 3 ≤ η ^ 2 := by nlinarith [sq_nonneg η]
      nlinarith

end WaveTurbulence.GammaLow.FinalCount.Ghost
