/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.CoreBound

/-!
# The core estimate, integrated (packet NT6)

`exists_core_bound`: with `μ = δL^{2γ}`, `Λ = L^{2d}`, `ε = L^{-2(d-1)(1-γ)+η}` and `A_F` bounding
`|Φ̂(s)| ∏_{i∈F} ⟨sᵢ⟩^{2d}`,

`|multiSum - Λ^m multiInt| ≤ (KΛ/μ)^m [A_∅ ∑ᵢ (L^{-1+2η}(1+|ξᵢ|+|ζᵢ|) + L^{-1}) + ∑_{F≠∅} A_F ε^{|F|}]`.

The constant `K` depends only on `d, γ, η`; it is uniform in the index type (the order `m`), the
cells, the frequencies, `L` and `δ`. This is the source's (conclusion1) mechanism, with all
`n`-dependence explicit: the minor arcs contribute `∑_{F≠∅} A_F ε^{|F|}`, the nonzero modes and
the tail one term per index.
-/

public section

noncomputable section

open MeasureTheory Metric WithLp Finset Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

theorem prod_le_pow_mul_prod {ι : Type*} [Fintype ι] {B u : ι → ℝ} {x : ℝ} (hB0 : ∀ i, 0 ≤ B i)
    (hB : ∀ i, B i ≤ x * u i) : ∏ i, B i ≤ x ^ Fintype.card ι * ∏ i, u i := by
  calc ∏ i, B i ≤ ∏ i, (x * u i) := Finset.prod_le_prod₀ (fun i _ => hB0 i) fun i _ => hB i
    _ = _ := by rw [prod_mul_distrib, prod_const, card_univ]

theorem enorm_le_of_hA {ι : Type*} [Fintype ι] {Φh : (ι → ℝ) → ℂ} {A : Finset ι → ℝ}
    (hA : ∀ F s, ‖Φh s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F) (F : Finset ι) (s : ι → ℝ) :
    ‖Φh s‖ₑ ≤ ENNReal.ofReal (A F) * ∏ i ∈ F, ENNReal.ofReal ((1 + s i ^ 2) ^ d)⁻¹ := by
  have hpos : 0 < ∏ i ∈ F, (1 + s i ^ 2) ^ d := prod_pos fun i _ => by positivity
  have h := hA F s
  have h' : ‖Φh s‖ ≤ A F * ∏ i ∈ F, ((1 + s i ^ 2) ^ d)⁻¹ := by
    rw [prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]; exact h
  rw [← ofReal_norm, ← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity,
    ← ENNReal.ofReal_mul (le_trans (by positivity) h)]
  exact ENNReal.ofReal_le_ofReal h'

/-- The integrated core estimate. -/
theorem exists_core_bound (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 20) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L δ : ℝ), 2 ≤ L → 2 ≤ L ^ η →
      δ ∈ Ioc (0 : ℝ) 1 → ∀ (Φ Φh : (ι → ℝ) → ℂ), IsFourierRep Φ Φh →
      ∀ A : Finset ι → ℝ, (∀ F s, ‖Φh s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F) →
      ∀ c : CellData d ι,
      ‖multiSum L (δ * L ^ (2 * γ)) Φ c.p c.q c.ξ c.ζ -
          ((L ^ (2 * d) : ℝ) : ℂ) ^ Fintype.card ι * multiInt (δ * L ^ (2 * γ)) Φ c.p c.q c.ξ c.ζ‖ ≤
        (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ Fintype.card ι *
          (A ∅ * ∑ i, (L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) + L⁻¹) +
            ∑ F ∈ (univ : Finset ι).powerset.erase ∅,
              A F * (L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)) ^ F.card) := by
  obtain ⟨C2, hC2, hmaj⟩ := exists_lintegral_scMaj_scS_le hd hη
  obtain ⟨C3, hC3, hmod⟩ := exists_lintegral_scMaj_scN_le hd hη0.le hη
  obtain ⟨C4, hC4, hmin⟩ := exists_lintegral_scMin_scS_le hd hγ hη0
  set C1 := cellK0 d * NTSP.sInt d
  set C5 := cellK0 d * NTSP.sInt (d - 1)
  have hC1 : 0 ≤ C1 := mul_nonneg (cellK0_nonneg d) (NTSP.sInt_nonneg d)
  have hC5 : 0 ≤ C5 := mul_nonneg (cellK0_nonneg d) (NTSP.sInt_nonneg _)
  set K := 2 * (C1 + C2 + C3 + C4 + C5)
  refine ⟨K, by positivity, ?_⟩
  intro ι _ _ L δ hL hLη hδ Φ Φh hrep A hA c
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hμ : 0 < δ * L ^ (2 * γ) := mul_pos hδ.1 (Real.rpow_pos_of_pos hL0 _)
  set μ := δ * L ^ (2 * γ) with hμdef
  set Λ : ℝ := L ^ (2 * d)
  have hΛ : 0 ≤ Λ := by positivity
  set ε : ℝ := L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)
  have hε : 0 ≤ ε := Real.rpow_nonneg hL0.le _
  have hA0 : ∀ F, 0 ≤ A F := fun F => le_trans (by positivity) (hA F 0)
  set x : ℝ := K * Λ / μ
  have hx : 0 ≤ x := by positivity
  have hμΛ : ∀ C, μ⁻¹ * Λ * C = x * (C / K) ∨ K = 0 := by
    intro C
    by_cases hK : K = 0
    · exact Or.inr hK
    · left; simp only [x]; field_simp
  -- abbreviations
  set S : ι → ℝ → ℂ := fun i => scS L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i)
  set T : ι → ℝ → ℂ := fun i => scT L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i)
  set N : ι → ℝ → ℂ := fun i => scN L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i)
  -- Step A: the difference as one integral
  have hSb : ∀ i t, ‖S i t‖ ≤ (cellIndex hL0 (c.p i) (c.q i)).card := fun i t =>
    norm_cellSum_le hL0 _ _ _ _ _
  have hTb : ∀ i t, ‖T i t‖ ≤ Λ * cellK0 d := by
    intro i t
    simp only [T, scT, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ L ^ (2 * d))]
    calc Λ * ‖cellInt (c.p i) (c.q i) (c.ξ i) (c.ζ i) (μ * t)‖
        ≤ Λ * (cellK0 d * ((1 + |μ * t|) ^ d)⁻¹) :=
          mul_le_mul_of_nonneg_left (norm_cellInt_le _ _ _ _ _) hΛ
      _ ≤ Λ * (cellK0 d * 1) := by
          gcongr
          · exact cellK0_nonneg d
          · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [abs_nonneg (μ * t)]))
      _ = Λ * cellK0 d := by ring
  have hint1 : Integrable (fun s : ι → ℝ => Φh s * ∏ i, S i (s i)) := by
    refine hrep.1.mul_bdd (c := ∏ i, ((cellIndex hL0 (c.p i) (c.q i)).card : ℝ)) ?_ ?_
    · exact (continuous_finsetProd _ fun i _ =>
        (continuous_scS hL0 μ _ _ _ _).comp (continuous_apply i)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun s => ?_
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hSb i (s i)
  have hint2 : Integrable (fun s : ι → ℝ => Φh s * ∏ i, T i (s i)) := by
    refine hrep.1.mul_bdd (c := ∏ _i : ι, Λ * cellK0 d) ?_ ?_
    · exact (continuous_finsetProd _ fun i _ =>
        (continuous_scT L μ _ _ _ _).comp (continuous_apply i)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun s => ?_
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hTb i (s i)
  have hA_eq : multiSum L μ Φ c.p c.q c.ξ c.ζ -
      ((L ^ (2 * d) : ℝ) : ℂ) ^ Fintype.card ι * multiInt μ Φ c.p c.q c.ξ c.ζ =
      ∫ s, Φh s * (∏ i, S i (s i) - ∏ i, T i (s i)) := by
    have e2 : ((L ^ (2 * d) : ℝ) : ℂ) ^ Fintype.card ι *
        (∫ s, Φh s * ∏ i, cellInt (c.p i) (c.q i) (c.ξ i) (c.ζ i) (μ * s i)) =
        ∫ s, Φh s * ∏ i, T i (s i) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [T, scT, prod_mul_distrib, prod_const, card_univ]
      ring
    rw [multiSum_eq hL0 μ hrep, multiInt_eq μ hrep, e2]
    rw [show (∫ s, Φh s * ∏ i, cellSum L (c.p i) (c.q i) (c.ξ i) (c.ζ i) (μ * s i)) =
      ∫ s, Φh s * ∏ i, S i (s i) from rfl, ← integral_sub hint1 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only
    ring
  -- Step B, C: pointwise
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((1 + t ^ 2) ^ d)⁻¹
  set g1 : Finset ι → ι → ℝ → ℝ≥0∞ := fun F i t =>
    if i ∈ F then w t * ‖scMin L μ t * S i t‖ₑ else ‖scMaj L μ t * S i t‖ₑ
  set g2 : ι → ι → ℝ → ℝ≥0∞ := fun l i t =>
    if i = l then ‖scMaj L μ t * N i t‖ₑ
    else ‖scMaj L μ t * (T i t + N i t)‖ₑ + ‖scMaj L μ t * T i t‖ₑ
  set g3 : ι → ι → ℝ → ℝ≥0∞ := fun l i t =>
    if i = l then ‖scMin L μ t * T i t‖ₑ else ‖scMaj L μ t * T i t‖ₑ + ‖T i t‖ₑ
  have hpt : ∀ s : ι → ℝ, ‖Φh s‖ₑ * ‖∏ i, S i (s i) - ∏ i, T i (s i)‖ₑ ≤
      (∑ F ∈ (univ : Finset ι).powerset.erase ∅, ENNReal.ofReal (A F) * ∏ i, g1 F i (s i)) +
      (∑ l, ENNReal.ofReal (A ∅) * ∏ i, g2 l i (s i)) +
      (∑ l, ENNReal.ofReal (A ∅) * ∏ i, g3 l i (s i)) := by
    intro s
    have hdec := enorm_prod_scS_sub_prod_scT_le hL0 μ c s
    have h0 : ‖Φh s‖ₑ ≤ ENNReal.ofReal (A ∅) := by
      simpa using enorm_le_of_hA hA ∅ s
    refine (mul_le_mul_of_nonneg_left hdec zero_le).trans ?_
    rw [mul_add, mul_add, mul_sum, mul_sum, mul_sum]
    refine add_le_add (add_le_add (sum_le_sum fun F _ => ?_) (sum_le_sum fun l _ => ?_))
      (sum_le_sum fun l _ => ?_)
    · have hF := enorm_le_of_hA hA F s
      have hprod : ∏ i, g1 F i (s i) = (∏ i ∈ F, w (s i)) *
          ((∏ i ∈ F, ‖scMin L μ (s i) * S i (s i)‖ₑ) *
            ∏ i ∈ univ \ F, ‖scMaj L μ (s i) * S i (s i)‖ₑ) := by
        simp only [g1]
        rw [prod_ite, filter_mem_eq_inter, Finset.univ_inter, prod_mul_distrib, mul_assoc]
        congr 3
        ext i; simp
      rw [hprod, ← mul_assoc (ENNReal.ofReal (A F))]
      exact mul_le_mul_of_nonneg_right hF zero_le
    · have hprod : ∏ i, g2 l i (s i) = ‖scMaj L μ (s l) * N l (s l)‖ₑ *
          ∏ i ∈ univ.erase l, (‖scMaj L μ (s i) * (T i (s i) + N i (s i))‖ₑ +
            ‖scMaj L μ (s i) * T i (s i)‖ₑ) := by
        rw [← mul_prod_erase univ _ (mem_univ l)]
        simp only [g2, ite_true]
        congr 1
        exact prod_congr rfl fun i hi => by simp [ne_of_mem_erase hi]
      rw [hprod]
      exact mul_le_mul_of_nonneg_right h0 zero_le
    · have hprod : ∏ i, g3 l i (s i) = ‖scMin L μ (s l) * T l (s l)‖ₑ *
          ∏ i ∈ univ.erase l, (‖scMaj L μ (s i) * T i (s i)‖ₑ + ‖T i (s i)‖ₑ) := by
        rw [← mul_prod_erase univ _ (mem_univ l)]
        simp only [g3, ite_true]
        congr 1
        exact prod_congr rfl fun i hi => by simp [ne_of_mem_erase hi]
      rw [hprod]
      exact mul_le_mul_of_nonneg_right h0 zero_le
  -- measurability
  have hmS : ∀ i, Continuous (S i) := fun i => continuous_scS hL0 μ _ _ _ _
  have hmT : ∀ i, Continuous (T i) := fun i => continuous_scT L μ _ _ _ _
  have hmN : ∀ i, Continuous (N i) := fun i => continuous_scN hL0 μ _ _ _ _
  have hmaj' := continuous_scMaj L μ
  have hmin' := continuous_scMin L μ
  have hw : Measurable w := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hg1 : ∀ F i, Measurable (g1 F i) := by
    intro F i
    simp only [g1]
    split_ifs
    · exact hw.mul (hmin'.mul (hmS i)).enorm.measurable
    · exact (hmaj'.mul (hmS i)).enorm.measurable
  have hg2 : ∀ l i, Measurable (g2 l i) := by
    intro l i
    simp only [g2]
    split_ifs
    · exact (hmaj'.mul (hmN i)).enorm.measurable
    · exact (hmaj'.mul ((hmT i).add (hmN i))).enorm.measurable.add
        (hmaj'.mul (hmT i)).enorm.measurable
  have hg3 : ∀ l i, Measurable (g3 l i) := by
    intro l i
    simp only [g3]
    split_ifs
    · exact (hmin'.mul (hmT i)).enorm.measurable
    · exact (hmaj'.mul (hmT i)).enorm.measurable.add (hmT i).enorm.measurable
  -- Step D: one-variable integrals
  have hI1 : ∀ F i, ∫⁻ t, g1 F i t ≤ ENNReal.ofReal
      (if i ∈ F then μ⁻¹ * Λ * (C4 * ε) else μ⁻¹ * Λ * C2) := by
    intro F i
    simp only [g1]
    split_ifs
    · exact hmin L δ hL hδ _ _ _ _
    · exact hmaj L μ hL1 hLη hμ _ _ _ _
  have hI2 : ∀ l i, ∫⁻ t, g2 l i t ≤ ENNReal.ofReal
      (if i = l then μ⁻¹ * Λ * (C3 * L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖))
        else μ⁻¹ * Λ * (C2 + C1)) := by
    intro l i
    simp only [g2]
    split_ifs
    · exact hmod L μ hL1 hLη hμ _ _ _ _
    · rw [lintegral_add_left (f := fun t => ‖scMaj L μ t * (T i t + N i t)‖ₑ)
        (hmaj'.mul ((hmT i).add (hmN i))).enorm.measurable]
      have h1 := hmaj L μ hL1 hLη hμ (c.p i) (c.q i) (c.ξ i) (c.ζ i)
      rw [← lintegral_scMaj_scTN_eq hL0] at h1
      have h2 := lintegral_scMaj_scT_le (by omega) hL0.le hμ (c.p i) (c.q i) (c.ξ i) (c.ζ i)
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
  have hI3 : ∀ l i, ∫⁻ t, g3 l i t ≤ ENNReal.ofReal
      (if i = l then μ⁻¹ * Λ * (C5 * L⁻¹) else μ⁻¹ * Λ * (2 * C1)) := by
    intro l i
    simp only [g3]
    split_ifs
    · refine (lintegral_scMin_scT_le hd hL0 hμ _ _ _ _).trans (le_of_eq ?_)
      congr 1
    · rw [lintegral_add_left (f := fun t => ‖scMaj L μ t * T i t‖ₑ)
        (hmaj'.mul (hmT i)).enorm.measurable]
      have h1 := lintegral_scMaj_scT_le (by omega) hL0.le hμ (c.p i) (c.q i) (c.ξ i) (c.ζ i)
      have h2 := lintegral_scT_le (by omega) hL0.le hμ (c.p i) (c.q i) (c.ξ i) (c.ζ i)
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
  -- real bounds of the products
  have hKC : ∀ C, 0 ≤ C → C ≤ K → ∀ u, 0 ≤ u → μ⁻¹ * Λ * (C * u) ≤ x * u := by
    intro C hC hCK u hu
    have : μ⁻¹ * Λ * (C * u) = (Λ / μ) * C * u := by ring
    rw [this, show x * u = (Λ / μ) * K * u by simp only [x]; ring]
    gcongr
  have hKC' : ∀ C, 0 ≤ C → C ≤ K → μ⁻¹ * Λ * C ≤ x * 1 := by
    intro C hC hCK
    simpa using hKC C hC hCK 1 zero_le_one
  have hP1 : ∀ F, A F * ∏ i, (if i ∈ F then μ⁻¹ * Λ * (C4 * ε) else μ⁻¹ * Λ * C2) ≤
      A F * (x ^ Fintype.card ι * ε ^ F.card) := by
    intro F
    refine mul_le_mul_of_nonneg_left ?_ (hA0 F)
    have h := prod_le_pow_mul_prod (B := fun i => if i ∈ F then μ⁻¹ * Λ * (C4 * ε) else μ⁻¹ * Λ * C2)
      (u := fun i => if i ∈ F then ε else 1) (x := x) (fun i => by split_ifs <;> positivity)
      (fun i => by
        split_ifs
        · exact hKC C4 hC4 (by simp only [K]; linarith) ε hε
        · exact hKC' C2 hC2 (by simp only [K]; linarith))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [Finset.prod_ite_mem, Finset.univ_inter, prod_const]
  have hP2 : ∀ l, A ∅ * ∏ i, (if i = l then μ⁻¹ * Λ * (C3 * L ^ (-1 + 2 * η) *
      (1 + ‖c.ξ i‖ + ‖c.ζ i‖)) else μ⁻¹ * Λ * (C2 + C1)) ≤
      A ∅ * (x ^ Fintype.card ι * (L ^ (-1 + 2 * η) * (1 + ‖c.ξ l‖ + ‖c.ζ l‖))) := by
    intro l
    refine mul_le_mul_of_nonneg_left ?_ (hA0 ∅)
    have hLp : 0 ≤ L ^ (-1 + 2 * η) := Real.rpow_nonneg hL0.le _
    have h := prod_le_pow_mul_prod (B := fun i => if i = l then μ⁻¹ * Λ * (C3 * L ^ (-1 + 2 * η) *
        (1 + ‖c.ξ i‖ + ‖c.ζ i‖)) else μ⁻¹ * Λ * (C2 + C1))
      (u := fun i => if i = l then L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) else 1) (x := x)
      (fun i => by split_ifs <;> positivity)
      (fun i => by
        split_ifs
        · rw [mul_assoc C3]
          exact hKC C3 hC3 (by simp only [K]; linarith) _ (by positivity)
        · exact hKC' (C2 + C1) (by positivity) (by simp only [K]; linarith))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [Finset.prod_ite_eq']
    simp
  have hP3 : ∀ l : ι, A ∅ * ∏ i, (if i = l then μ⁻¹ * Λ * (C5 * L⁻¹) else μ⁻¹ * Λ * (2 * C1)) ≤
      A ∅ * (x ^ Fintype.card ι * L⁻¹) := by
    intro l
    refine mul_le_mul_of_nonneg_left ?_ (hA0 ∅)
    have h := prod_le_pow_mul_prod (B := fun i => if i = l then μ⁻¹ * Λ * (C5 * L⁻¹)
        else μ⁻¹ * Λ * (2 * C1))
      (u := fun i => if i = l then L⁻¹ else 1) (x := x)
      (fun i => by split_ifs <;> positivity)
      (fun i => by
        split_ifs
        · exact hKC C5 hC5 (by simp only [K]; linarith) _ (by positivity)
        · exact hKC' (2 * C1) (by positivity) (by simp only [K]; linarith))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [Finset.prod_ite_eq']
    simp
  -- Step E: assemble
  have hfinal : ‖multiSum L μ Φ c.p c.q c.ξ c.ζ -
      ((L ^ (2 * d) : ℝ) : ℂ) ^ Fintype.card ι * multiInt μ Φ c.p c.q c.ξ c.ζ‖ₑ ≤
      ENNReal.ofReal (∑ F ∈ (univ : Finset ι).powerset.erase ∅,
          A F * (x ^ Fintype.card ι * ε ^ F.card)) +
        ENNReal.ofReal (∑ l, A ∅ * (x ^ Fintype.card ι *
          (L ^ (-1 + 2 * η) * (1 + ‖c.ξ l‖ + ‖c.ζ l‖)))) +
        ENNReal.ofReal (∑ _l : ι, A ∅ * (x ^ Fintype.card ι * L⁻¹)) := by
    rw [hA_eq]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp_rw [enorm_mul]
    refine (lintegral_mono hpt).trans ?_
    have hm1 : ∀ F, Measurable fun s : ι → ℝ => ENNReal.ofReal (A F) * ∏ i, g1 F i (s i) :=
      fun F => measurable_const.mul (Finset.measurable_prod _ fun i _ =>
        (hg1 F i).comp (measurable_pi_apply i))
    have hm2 : ∀ l, Measurable fun s : ι → ℝ => ENNReal.ofReal (A ∅) * ∏ i, g2 l i (s i) :=
      fun l => measurable_const.mul (Finset.measurable_prod _ fun i _ =>
        (hg2 l i).comp (measurable_pi_apply i))
    have hm3 : ∀ l, Measurable fun s : ι → ℝ => ENNReal.ofReal (A ∅) * ∏ i, g3 l i (s i) :=
      fun l => measurable_const.mul (Finset.measurable_prod _ fun i _ =>
        (hg3 l i).comp (measurable_pi_apply i))
    rw [lintegral_add_left (f := fun s : ι → ℝ =>
        (∑ F ∈ (univ : Finset ι).powerset.erase ∅, ENNReal.ofReal (A F) * ∏ i, g1 F i (s i)) +
          ∑ l, ENNReal.ofReal (A ∅) * ∏ i, g2 l i (s i))
        ((Finset.measurable_sum _ fun F _ => hm1 F).add (Finset.measurable_sum _ fun l _ => hm2 l)),
      lintegral_add_left (f := fun s : ι → ℝ =>
        ∑ F ∈ (univ : Finset ι).powerset.erase ∅, ENNReal.ofReal (A F) * ∏ i, g1 F i (s i))
        (Finset.measurable_sum _ fun F _ => hm1 F),
      lintegral_finsetSum _ fun F _ => hm1 F, lintegral_finsetSum _ fun l _ => hm2 l,
      lintegral_finsetSum _ fun l _ => hm3 l]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · rw [ENNReal.ofReal_sum_of_nonneg fun F _ => mul_nonneg (hA0 F) (by positivity)]
      refine sum_le_sum fun F _ => ?_
      refine (lintegral_const_mul_prod_le _ (g1 F) (hg1 F) _ (fun i => by
        split_ifs <;> positivity) (hI1 F)).trans (ENNReal.ofReal_le_ofReal (hP1 F))
    · rw [ENNReal.ofReal_sum_of_nonneg fun l _ => mul_nonneg (hA0 ∅) (by positivity)]
      refine sum_le_sum fun l _ => ?_
      refine (lintegral_const_mul_prod_le _ (g2 l) (hg2 l) _ (fun i => by
        split_ifs <;> positivity) (hI2 l)).trans (ENNReal.ofReal_le_ofReal (hP2 l))
    · rw [ENNReal.ofReal_sum_of_nonneg fun l _ => mul_nonneg (hA0 ∅) (by positivity)]
      refine sum_le_sum fun l _ => ?_
      refine (lintegral_const_mul_prod_le _ (g3 l) (hg3 l) _ (fun i => by
        split_ifs <;> positivity) (hI3 l)).trans (ENNReal.ofReal_le_ofReal (hP3 l))
  have hR0 : 0 ≤ x ^ Fintype.card ι *
      (A ∅ * ∑ i, (L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) + L⁻¹) +
        ∑ F ∈ (univ : Finset ι).powerset.erase ∅, A F * ε ^ F.card) := by
    have := hA0 ∅
    refine mul_nonneg (by positivity) (add_nonneg (mul_nonneg this (sum_nonneg fun i _ => ?_))
      (sum_nonneg fun F _ => mul_nonneg (hA0 F) (by positivity)))
    have := Real.rpow_nonneg hL0.le (-1 + 2 * η); positivity
  have hLp : 0 ≤ L ^ (-1 + 2 * η) := Real.rpow_nonneg hL0.le _
  have hxm : 0 ≤ x ^ Fintype.card ι := pow_nonneg hx _
  have hs1 : 0 ≤ ∑ F ∈ (univ : Finset ι).powerset.erase ∅,
      A F * (x ^ Fintype.card ι * ε ^ F.card) :=
    sum_nonneg fun F _ => mul_nonneg (hA0 F) (mul_nonneg hxm (pow_nonneg hε _))
  have hs2 : 0 ≤ ∑ l, A ∅ * (x ^ Fintype.card ι * (L ^ (-1 + 2 * η) * (1 + ‖c.ξ l‖ + ‖c.ζ l‖))) :=
    sum_nonneg fun l _ => mul_nonneg (hA0 ∅) (mul_nonneg hxm (by positivity))
  have hs3 : 0 ≤ ∑ _l : ι, A ∅ * (x ^ Fintype.card ι * L⁻¹) :=
    sum_nonneg fun l _ => mul_nonneg (hA0 ∅) (mul_nonneg hxm (by positivity))
  rw [← ofReal_norm] at hfinal
  rw [← ENNReal.ofReal_add hs1 hs2, ← ENNReal.ofReal_add (add_nonneg hs1 hs2) hs3] at hfinal
  have h1 := (ENNReal.ofReal_le_ofReal_iff (add_nonneg (add_nonneg hs1 hs2) hs3)).1 hfinal
  refine h1.trans (le_of_eq ?_)
  have e1 : ∑ F ∈ (univ : Finset ι).powerset.erase ∅, A F * (x ^ Fintype.card ι * ε ^ F.card) =
      x ^ Fintype.card ι * ∑ F ∈ (univ : Finset ι).powerset.erase ∅, A F * ε ^ F.card := by
    rw [mul_sum]; exact sum_congr rfl fun F _ => by ring
  have e2 : ∑ l, A ∅ * (x ^ Fintype.card ι * (L ^ (-1 + 2 * η) * (1 + ‖c.ξ l‖ + ‖c.ζ l‖))) =
      x ^ Fintype.card ι * (A ∅ * ∑ l, L ^ (-1 + 2 * η) * (1 + ‖c.ξ l‖ + ‖c.ζ l‖)) := by
    rw [mul_sum, mul_sum]; exact sum_congr rfl fun l _ => by ring
  have e3 : ∑ _l : ι, A ∅ * (x ^ Fintype.card ι * L⁻¹) =
      x ^ Fintype.card ι * (A ∅ * ∑ _l : ι, L⁻¹) := by
    rw [mul_sum, mul_sum]; exact sum_congr rfl fun l _ => by ring
  rw [e1, e2, e3, sum_add_distrib]
  ring

end WaveTurbulence.ApproxNT
