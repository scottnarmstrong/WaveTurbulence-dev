/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Arith1
/-! **L6E GHOST, part 5: the transverse pair** (M1-R2 Theorem 6.1 (b), Remark 6.3; all `0 < γ < 1`).

Two `α`-ghosts whose gaps make an angle `≥ θ₀ = L^{-6η}`: the two energy slabs (`card_P5_two`) give the charged bound with
no transfer. Margin `2γ - γ₀ - 9η - 4η² - η³ > 0` under `200η ≤ γ`.
* `twoSlab_terms`: the field inequality behind it (abstract positive reals);
* `arith_P5_alpha2_TR`: the real inequality in the form consumed by the triangle leaf. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

/-- The constant of the transverse-pair bound. -/
noncomputable def constTR (d c : ℕ) (η δ : ℝ) : ℝ :=
  256 * 5 ^ d * (d : ℝ) ^ 2 * (1 + d) * (δ⁻¹) ^ 2 * (((2 * c + 12 : ℕ) : ℝ) / η ^ 2) ^ (2 * c + 12)

theorem constTR_nonneg (d c : ℕ) (η δ : ℝ) (hδ : 0 < δ) : 0 ≤ constTR d c η δ := by unfold constTR; positivity

/-- **The three terms of `twoSlabX`**, abstractly: `r = 2 n D a L²` (slab radius), `θ = e⁻¹`, `ℓⱼ = Qⱼ L / 2`,
`Φ = a² g e / (Q₁ Q₂)`, under `Qⱼ ≤ a L` and `Q₁ Q₂ ≤ a² e L²`. -/
theorem twoSlab_terms {n D a g e L Q₁ Q₂ dd : ℝ} (hn : 0 ≤ n) (hD : 1 ≤ D) (ha : 0 < a) (hg : 0 < g) (he : 0 < e)
    (hL : 0 < L) (hQ₁ : 0 < Q₁) (hQ₂ : 0 < Q₂) (hd : 1 ≤ dd) (hQ₁a : Q₁ ≤ a * L) (hQ₂a : Q₂ ≤ a * L)
    (hQQ : Q₁ * Q₂ ≤ a ^ 2 * e * L ^ 2) :
    (4 * (2 * (n * (D * a) * L ^ 2)) ^ 2 * dd ^ 2 * (1 + dd) / (e⁻¹ * (Q₁ / 2 * L) * (Q₂ / 2 * L)) +
        2 * (2 * (n * (D * a) * L ^ 2)) * dd * (1 + dd) / e⁻¹ * (1 / (Q₁ / 2 * L) + 1 / (Q₂ / 2 * L)) + 1) *
      (g / L ^ 2) ≤ 64 * dd ^ 2 * (1 + dd) * D ^ 2 * (n + 1) ^ 2 * (a ^ 2 * g * e / (Q₁ * Q₂)) := by
  have hD0 : 0 < D := by linarith
  have hΦ : 0 < a ^ 2 * g * e / (Q₁ * Q₂) := by positivity
  have e1 : 4 * (2 * (n * (D * a) * L ^ 2)) ^ 2 * dd ^ 2 * (1 + dd) / (e⁻¹ * (Q₁ / 2 * L) * (Q₂ / 2 * L)) * (g / L ^ 2) =
      64 * n ^ 2 * D ^ 2 * dd ^ 2 * (1 + dd) * (a ^ 2 * g * e / (Q₁ * Q₂)) := by
    field_simp; ring
  have e2 : 2 * (2 * (n * (D * a) * L ^ 2)) * dd * (1 + dd) / e⁻¹ * (1 / (Q₁ / 2 * L) + 1 / (Q₂ / 2 * L)) * (g / L ^ 2) =
      8 * n * D * dd * (1 + dd) * (a * g * e / L) * (1 / Q₁ + 1 / Q₂) := by
    field_simp; ring
  have h1 : a * g * e / L * (1 / Q₁) ≤ a ^ 2 * g * e / (Q₁ * Q₂) := by
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    have : a * g * e * (Q₁ * Q₂) ≤ a * g * e * (Q₁ * (a * L)) := by gcongr
    nlinarith [mul_pos (mul_pos (mul_pos ha hg) he) hQ₁]
  have h2 : a * g * e / L * (1 / Q₂) ≤ a ^ 2 * g * e / (Q₁ * Q₂) := by
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    have : a * g * e * (Q₁ * Q₂) ≤ a * g * e * ((a * L) * Q₂) := by gcongr
    nlinarith [mul_pos (mul_pos (mul_pos ha hg) he) hQ₂]
  have h3 : g / L ^ 2 ≤ a ^ 2 * g * e / (Q₁ * Q₂) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : g * (Q₁ * Q₂) ≤ g * (a ^ 2 * e * L ^ 2) := by gcongr
    nlinarith
  have hT2 : 8 * n * D * dd * (1 + dd) * (a * g * e / L) * (1 / Q₁ + 1 / Q₂) ≤
      16 * n * D * dd * (1 + dd) * (a ^ 2 * g * e / (Q₁ * Q₂)) := by
    have hc : 0 ≤ 8 * n * D * dd * (1 + dd) := by positivity
    have : a * g * e / L * (1 / Q₁ + 1 / Q₂) ≤ 2 * (a ^ 2 * g * e / (Q₁ * Q₂)) := by
      rw [mul_add]; linarith
    calc 8 * n * D * dd * (1 + dd) * (a * g * e / L) * (1 / Q₁ + 1 / Q₂)
        = 8 * n * D * dd * (1 + dd) * (a * g * e / L * (1 / Q₁ + 1 / Q₂)) := by ring
      _ ≤ 8 * n * D * dd * (1 + dd) * (2 * (a ^ 2 * g * e / (Q₁ * Q₂))) := by gcongr
      _ = _ := by ring
  have hDd : D * dd ≤ D ^ 2 * dd ^ 2 := by
    have h1 : D ≤ D ^ 2 := le_self_pow₀ hD (by norm_num)
    have h2 : dd ≤ dd ^ 2 := le_self_pow₀ hd (by norm_num)
    exact mul_le_mul h1 h2 (by linarith) (by positivity)
  have hk2 : 16 * n * D * dd * (1 + dd) ≤ 2 * (64 * dd ^ 2 * (1 + dd) * D ^ 2) * n := by
    have h0 : 0 ≤ 16 * n * (1 + dd) := by positivity
    calc 16 * n * D * dd * (1 + dd) = 16 * n * (1 + dd) * (D * dd) := by ring
      _ ≤ 16 * n * (1 + dd) * (D ^ 2 * dd ^ 2) := mul_le_mul_of_nonneg_left hDd h0
      _ ≤ 2 * (64 * dd ^ 2 * (1 + dd) * D ^ 2) * n := by
          have hX : 0 ≤ 16 * n * (1 + dd) * (D ^ 2 * dd ^ 2) := by positivity
          have e : 2 * (64 * dd ^ 2 * (1 + dd) * D ^ 2) * n = 8 * (16 * n * (1 + dd) * (D ^ 2 * dd ^ 2)) := by ring
          rw [e]; linarith
  have hk3 : (1 : ℝ) ≤ 64 * dd ^ 2 * (1 + dd) * D ^ 2 := by
    have h1 : (1 : ℝ) ≤ dd ^ 2 := one_le_pow₀ hd
    have h2 : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ 64 * dd ^ 2 * (1 + dd) * D ^ 2 := by gcongr <;> linarith
  have hsum : 64 * n ^ 2 * D ^ 2 * dd ^ 2 * (1 + dd) + 16 * n * D * dd * (1 + dd) + 1 ≤
      64 * dd ^ 2 * (1 + dd) * D ^ 2 * (n + 1) ^ 2 := by
    have e : 64 * dd ^ 2 * (1 + dd) * D ^ 2 * (n + 1) ^ 2 = 64 * n ^ 2 * D ^ 2 * dd ^ 2 * (1 + dd) +
        2 * (64 * dd ^ 2 * (1 + dd) * D ^ 2) * n + 64 * dd ^ 2 * (1 + dd) * D ^ 2 := by ring
    rw [e]; linarith
  have hfin := mul_le_mul_of_nonneg_right hsum hΦ.le
  rw [add_mul, add_mul, one_mul, e1, e2]
  calc 64 * n ^ 2 * D ^ 2 * dd ^ 2 * (1 + dd) * (a ^ 2 * g * e / (Q₁ * Q₂)) +
        8 * n * D * dd * (1 + dd) * (a * g * e / L) * (1 / Q₁ + 1 / Q₂) + g / L ^ 2
      ≤ 64 * n ^ 2 * D ^ 2 * dd ^ 2 * (1 + dd) * (a ^ 2 * g * e / (Q₁ * Q₂)) +
        16 * n * D * dd * (1 + dd) * (a ^ 2 * g * e / (Q₁ * Q₂)) + a ^ 2 * g * e / (Q₁ * Q₂) := by
        linarith
    _ = (64 * n ^ 2 * D ^ 2 * dd ^ 2 * (1 + dd) + 16 * n * D * dd * (1 + dd) + 1) *
        (a ^ 2 * g * e / (Q₁ * Q₂)) := by ring
    _ ≤ _ := hfin

/-- **Two transverse `α`-ghosts** (Theorem 6.1 (b)): the two-slab count gives the charged bound, no transfer, for every
`0 < γ < 1`. Here `θ₀ = L^{-6η}` and the gaps have size `≥ Qⱼ/2`. -/
theorem arith_P5_alpha2_TR (d : ℕ) {L γ η δ C₁ na Q₁ Q₂ : ℝ} (c κ₁ κ₂ gb : ℕ) (hgb : gb ≤ 1) (hd : 3 ≤ d)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) (hna0 : 0 ≤ na) (hna : na ≤ Real.log L ^ c) (hQ₁l : L⁻¹ ≤ Q₁)
    (hQ₁u : Q₁ ≤ L ^ (-γ + η)) (hQ₂l : L⁻¹ ≤ Q₂) (hQ₂u : Q₂ ≤ L ^ (-γ + η)) :
    ((⌊twoSlabX d ⌊2 * L⌋₊ (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) (Q₁ / 2 * L) (Q₂ / 2 * L)
        (L ^ (-6 * η))⌋₊ : ℕ) : ℝ) * rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 ≤
      constTR d c η δ * (excessRHS L γ η [] (-(gb : ℤ)) (1 - 2 * (gb : ℤ)) /
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hQ₁0 : 0 < Q₁ := lt_of_lt_of_le (inv_pos.2 hL0) hQ₁l
  have hQ₂0 : 0 < Q₂ := lt_of_lt_of_le (inv_pos.2 hL0) hQ₂l
  have hd1 : (1 : ℝ) ≤ d := by have : (3 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  have hP1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL; rwa [Real.log_exp] at this
  have hPc : 1 ≤ Real.log L ^ c := one_le_pow₀ hP1
  have hP0 : 0 ≤ Real.log L := by linarith
  have hq0 := qq_nonneg hδ0.le (zero_le_one.trans hC)
  have hq1 := qq_le_one hδ0 hδ hC
  have hδ1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).2 hδ
  -- the abstract reals
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = L ^ (-2 * γ) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = L ^ γ := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = L ^ (6 * η) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hg0 : 0 < g := by rw [hg]; positivity
  have he0 : 0 < e := by rw [he]; positivity
  have hθ : L ^ (-6 * η) = e⁻¹ := by rw [he, ← Real.rpow_neg hL0.le]; congr 1; ring
  have hΦe : L ^ (-3 * γ + 6 * η) = a ^ 2 * g * e := by
    rw [ha, hg, he, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1; push_cast; ring
  have hQa : ∀ Q : ℝ, Q ≤ L ^ (-γ + η) → Q ≤ a * L := by
    intro Q hQ
    refine hQ.trans ?_
    calc L ^ (-γ + η) ≤ L ^ (-2 * γ + 1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = a * L := by rw [ha, Real.rpow_add hL0, Real.rpow_one]
  have hQQ : Q₁ * Q₂ ≤ a ^ 2 * e * L ^ 2 := by
    calc Q₁ * Q₂ ≤ L ^ (-γ + η) * L ^ (-γ + η) := by gcongr
      _ = L ^ (-2 * γ + 2 * η) := by rw [← Real.rpow_add hL0]; congr 1; ring
      _ ≤ L ^ (-4 * γ + 6 * η + 2) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = a ^ 2 * e * L ^ 2 := by
          rw [ha, he, ← Real.rpow_natCast L 2, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0,
            ← Real.rpow_add hL0]
          congr 1; push_cast; ring
  -- the box factor
  have hbox : ((2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ (d - 2)) * L ^ (-((d : ℝ) - γ)) ≤ 5 ^ d * (g / L ^ 2) := by
    have h5 : (2 * (⌊2 * L⌋₊ : ℝ) + 1) ≤ 5 * L := by exact_mod_cast two_m_succ_le hL1
    have hLd : (L ^ (d - 2) : ℝ) * L ^ (-((d : ℝ) - γ)) = g / L ^ 2 := by
      rw [hg, ← Real.rpow_natCast, ← Real.rpow_add hL0, ← Real.rpow_natCast L 2, ← Real.rpow_sub hL0]
      congr 1
      have : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; push_cast; ring
    have hLn : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hL0.le _
    calc ((2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ (d - 2)) * L ^ (-((d : ℝ) - γ)) ≤ (5 * L) ^ (d - 2) * L ^ (-((d : ℝ) - γ)) := by
          gcongr
      _ = 5 ^ (d - 2) * (L ^ (d - 2) * L ^ (-((d : ℝ) - γ))) := by rw [mul_pow]; ring
      _ ≤ 5 ^ d * (g / L ^ 2) := by
          rw [hLd]; gcongr
          · norm_num
          · omega
  -- the count, in the abstract form
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = twoSlabX d ⌊2 * L⌋₊ (2 * (na * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)) (Q₁ / 2 * L)
      (Q₂ / 2 * L) (L ^ (-6 * η)) := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by
    rw [hX]; unfold twoSlabX; rw [hθ, ← ha]; positivity
  have hXb : X * L ^ (-((d : ℝ) - γ)) ≤
      5 ^ d * (64 * (d : ℝ) ^ 2 * (1 + d) * (δ⁻¹) ^ 2 * (na + 1) ^ 2 * (a ^ 2 * g * e / (Q₁ * Q₂))) := by
    rw [hX]; unfold twoSlabX; rw [hθ, ← ha]
    have ht := twoSlab_terms (n := na) (D := δ⁻¹) (dd := (d : ℝ)) hna0 hδ1 ha0 hg0 he0 hL0 hQ₁0 hQ₂0 hd1
      (hQa Q₁ hQ₁u) (hQa Q₂ hQ₂u) hQQ
    have hT0 : 0 ≤ 4 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) ^ 2 * (d : ℝ) ^ 2 * (1 + d) / (e⁻¹ * (Q₁ / 2 * L) * (Q₂ / 2 * L)) +
        2 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) * d * (1 + d) / e⁻¹ * (1 / (Q₁ / 2 * L) + 1 / (Q₂ / 2 * L)) + 1 := by
      positivity
    calc (4 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) ^ 2 * (d : ℝ) ^ 2 * (1 + d) / (e⁻¹ * (Q₁ / 2 * L) * (Q₂ / 2 * L)) +
          2 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) * d * (1 + d) / e⁻¹ * (1 / (Q₁ / 2 * L) + 1 / (Q₂ / 2 * L)) + 1) *
          (2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ (d - 2) * L ^ (-((d : ℝ) - γ))
        = (4 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) ^ 2 * (d : ℝ) ^ 2 * (1 + d) / (e⁻¹ * (Q₁ / 2 * L) * (Q₂ / 2 * L)) +
          2 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) * d * (1 + d) / e⁻¹ * (1 / (Q₁ / 2 * L) + 1 / (Q₂ / 2 * L)) + 1) *
          ((2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ (d - 2) * L ^ (-((d : ℝ) - γ))) := by ring
      _ ≤ (4 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) ^ 2 * (d : ℝ) ^ 2 * (1 + d) / (e⁻¹ * (Q₁ / 2 * L) * (Q₂ / 2 * L)) +
          2 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) * d * (1 + d) / e⁻¹ * (1 / (Q₁ / 2 * L) + 1 / (Q₂ / 2 * L)) + 1) *
          (5 ^ d * (g / L ^ 2)) := mul_le_mul_of_nonneg_left hbox hT0
      _ = 5 ^ d * ((4 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) ^ 2 * (d : ℝ) ^ 2 * (1 + d) / (e⁻¹ * (Q₁ / 2 * L) * (Q₂ / 2 * L)) +
          2 * (2 * (na * (δ⁻¹ * a) * L ^ 2)) * d * (1 + d) / e⁻¹ * (1 / (Q₁ / 2 * L) + 1 / (Q₂ / 2 * L)) + 1) *
          (g / L ^ 2)) := by ring
      _ ≤ _ := by gcongr
  -- the logarithms
  have hna1 : (na + 1) ^ 2 ≤ 4 * Real.log L ^ (2 * c) := by
    have : na + 1 ≤ 2 * Real.log L ^ c := by linarith
    calc (na + 1) ^ 2 ≤ (2 * Real.log L ^ c) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
      _ = 4 * Real.log L ^ (2 * c) := by ring
  have hlog := log_pow_le_eta (2 * c + 12) (by omega) hL1 hη
  rw [rankFactor_nat d L γ δ C₁ hL0 1, excessRHS_nil L γ η hL0]
  simp only [pow_one]
  have hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0
  have hΦ0 : 0 ≤ a ^ 2 * g * e / (Q₁ * Q₂) := by positivity
  have hLn : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hL0.le _
  have hT : 0 < (L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂) := by
    positivity
  -- the final exponent
  have hexp : L ^ (η ^ 2) * (a ^ 2 * g * e / (Q₁ * Q₂)) *
      ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂)) ≤
      L ^ (-η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((-(gb : ℤ) : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((1 - 2 * (gb : ℤ) : ℤ)) : ℝ))) := by
    rw [← hΦe]
    have e : L ^ (η ^ 2) * (L ^ (-3 * γ + 6 * η) / (Q₁ * Q₂)) *
        ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂)) =
        L ^ (η ^ 2) * L ^ (-3 * γ + 6 * η) * L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) *
          L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) := by
      field_simp
    rw [e, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have hm : min γ (1 - γ) ≤ γ := min_le_left _ _
    have hg' : (gb : ℝ) ≤ 1 := by exact_mod_cast hgb
    have hgη : (gb : ℝ) * η ^ 2 ≤ η ^ 2 := mul_le_of_le_one_left (sq_nonneg η) hg'
    have hk1 : (0 : ℝ) ≤ (κ₁ : ℝ) * η := by positivity
    have hk2 : (0 : ℝ) ≤ (κ₂ : ℝ) * η := by positivity
    have h200 : η ≤ 1 / 200 := by linarith
    have h2 : η ^ 2 ≤ η / 200 := by
      calc η ^ 2 = η * η := by ring
        _ ≤ η * (1 / 200) := mul_le_mul_of_nonneg_left h200 hη.le
        _ = η / 200 := by ring
    have h3 : η ^ 3 ≤ η ^ 2 := pow_le_pow_of_le_one hη.le (by linarith) (by norm_num)
    have e2 : -η ^ 3 + ((2 * min γ (1 - γ) + 5 * η ^ 2) * (((-(gb : ℤ) : ℤ)) : ℝ) -
        (min γ (1 - γ) + 2 * η ^ 2) * (((1 - 2 * (gb : ℤ) : ℤ)) : ℝ)) =
        -η ^ 3 - min γ (1 - γ) - 2 * η ^ 2 - (gb : ℝ) * η ^ 2 := by push_cast; ring
    rw [e2]
    linarith
  calc ((⌊X⌋₊ : ℕ) : ℝ) * (L ^ (-((d : ℝ) - γ)) * qq δ C₁) * Real.log L ^ 12
      ≤ X * L ^ (-((d : ℝ) - γ)) * 1 * Real.log L ^ 12 := by
        rw [← mul_assoc]; gcongr
    _ ≤ 5 ^ d * (64 * (d : ℝ) ^ 2 * (1 + d) * (δ⁻¹) ^ 2 * (4 * Real.log L ^ (2 * c)) *
          (a ^ 2 * g * e / (Q₁ * Q₂))) * 1 * Real.log L ^ 12 := by
        rw [mul_one, mul_one]
        refine mul_le_mul_of_nonneg_right (hXb.trans ?_) (by positivity)
        gcongr
    _ = 256 * 5 ^ d * (d : ℝ) ^ 2 * (1 + d) * (δ⁻¹) ^ 2 * Real.log L ^ (2 * c + 12) *
          (a ^ 2 * g * e / (Q₁ * Q₂)) := by ring
    _ ≤ 256 * 5 ^ d * (d : ℝ) ^ 2 * (1 + d) * (δ⁻¹) ^ 2 *
          ((((2 * c + 12 : ℕ) : ℝ) / η ^ 2) ^ (2 * c + 12) * L ^ (η ^ 2)) * (a ^ 2 * g * e / (Q₁ * Q₂)) := by
        gcongr
    _ = constTR d c η δ * (L ^ (η ^ 2) * (a ^ 2 * g * e / (Q₁ * Q₂)) *
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂)) /
          ((L ^ ((γ + 3 * η) / 2 - (κ₁ : ℝ) * η) * Q₁) * (L ^ ((γ + 3 * η) / 2 - (κ₂ : ℝ) * η) * Q₂))) := by
        unfold constTR; field_simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (constTR_nonneg d c η δ hδ0)
        exact div_le_div_of_nonneg_right hexp hT.le

end WaveTurbulence.GammaLow.FinalCount.Ghost
