/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltNT.Concl
public import WaveTurbulence.Foundations.ApproxNT.CoreTheorem

/-! # FILT-COH (b): the modulation-uniform crude core (o82 Thm 10.1 (10.5))

Main's `ApproxNT.exists_core_bound` bounds the DIFFERENCE `multiSum - Λ^m multiInt` and pays the first moment
`1 + ‖ξ‖ + ‖ζ‖` of the cell modulations (the nonzero modes). A crude bound of the lattice sum ALONE needs no such
moment: splitting every factor into its major and minor arcs,
`∏ᵢ S_i = ∑_F ∏_{i∈F} ψ S_i ∏_{i∉F} φ S_i`, and the one-variable integrals
`∫|φ(μt)S(μt)| ≲ μ⁻¹Λ`, `∫⟨t⟩^{-2d}|ψ(μt)S(μt)| ≲ μ⁻¹Λε` (main's `exists_lintegral_scMaj_scS_le`,
`exists_lintegral_scMin_scS_le`) are uniform in the centers AND the modulations. This is (10.8) of o82 §10.

* `exists_crude_core_bound`: `‖multiSum‖ ≤ (KΛ/μ)^m ∑_F A_F ε^{|F|}`, uniform in `c.ξ, c.ζ`;
* `exists_filt_crude_cell_bound`: the same for D5c's filtered profile, `≤ 2 (K M C₀ Λ/μ)^n`.

Proofs adapted from main's `ApproxNT.exists_core_bound` (CoreTheorem.lean) and D5c's `exists_filt_cell_bound`
(sha256 in COPIED-SHA256SUMS). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open MeasureTheory WaveTurbulence.ApproxNT Finset Set
open WaveTurbulence.Flower.FiltNT
open scoped ENNReal ContDiff

variable {d : ℕ}

/-- **The crude core estimate** (o82 (10.5)/(10.8)): the decoupled lattice sum alone, with no modulation moment. -/
theorem exists_crude_core_bound (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 20) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L δ : ℝ), 2 ≤ L → 2 ≤ L ^ η →
      δ ∈ Ioc (0 : ℝ) 1 → ∀ (Φ Φh : (ι → ℝ) → ℂ), IsFourierRep Φ Φh →
      ∀ A : Finset ι → ℝ, (∀ F s, ‖Φh s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F) →
      ∀ c : CellData d ι,
      ‖multiSum L (δ * L ^ (2 * γ)) Φ c.p c.q c.ξ c.ζ‖ ≤
        (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ Fintype.card ι *
          ∑ F ∈ (univ : Finset ι).powerset,
            A F * (L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)) ^ F.card := by
  obtain ⟨C2, hC2, hmaj⟩ := exists_lintegral_scMaj_scS_le hd hη
  obtain ⟨C4, hC4, hmin⟩ := exists_lintegral_scMin_scS_le hd hγ hη0
  refine ⟨C2 + C4, by positivity, ?_⟩
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
  set K := C2 + C4
  set x : ℝ := K * Λ / μ
  have hx : 0 ≤ x := by positivity
  set S : ι → ℝ → ℂ := fun i => scS L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i)
  have hmS : ∀ i, Continuous (S i) := fun i => continuous_scS hL0 μ _ _ _ _
  have hmaj' := continuous_scMaj L μ
  have hmin' := continuous_scMin L μ
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((1 + t ^ 2) ^ d)⁻¹
  have hw : Measurable w := ENNReal.measurable_ofReal.comp (by fun_prop)
  set g1 : Finset ι → ι → ℝ → ℝ≥0∞ := fun F i t =>
    if i ∈ F then w t * ‖scMin L μ t * S i t‖ₑ else ‖scMaj L μ t * S i t‖ₑ
  have hg1 : ∀ F i, Measurable (g1 F i) := by
    intro F i
    simp only [g1]
    split_ifs
    · exact hw.mul (hmin'.mul (hmS i)).enorm.measurable
    · exact (hmaj'.mul (hmS i)).enorm.measurable
  have hpt : ∀ s : ι → ℝ, ‖Φh s * ∏ i, S i (s i)‖ₑ ≤
      ∑ F ∈ (univ : Finset ι).powerset, ENNReal.ofReal (A F) * ∏ i, g1 F i (s i) := by
    intro s
    have hsplit : ∏ i, S i (s i) = ∑ F ∈ (univ : Finset ι).powerset,
        (∏ i ∈ F, scMin L μ (s i) * S i (s i)) * ∏ i ∈ univ \ F, scMaj L μ (s i) * S i (s i) := by
      rw [← Finset.prod_add]
      refine prod_congr rfl fun i _ => ?_
      rw [← add_mul, add_comm, scMaj_add_scMin, one_mul]
    rw [hsplit, enorm_mul]
    refine (mul_le_mul' le_rfl (enorm_sum_le _ _)).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun F _ => ?_
    have hF := enorm_le_of_hA hA F s
    have hprod : ∏ i, g1 F i (s i) = (∏ i ∈ F, w (s i)) *
        ((∏ i ∈ F, ‖scMin L μ (s i) * S i (s i)‖ₑ) *
          ∏ i ∈ univ \ F, ‖scMaj L μ (s i) * S i (s i)‖ₑ) := by
      simp only [g1]
      rw [prod_ite, filter_mem_eq_inter, Finset.univ_inter, prod_mul_distrib, mul_assoc]
      congr 3
      ext i; simp
    rw [hprod, enorm_mul, enorm_finset_prod, enorm_finset_prod, ← mul_assoc (ENNReal.ofReal (A F))]
    exact mul_le_mul_of_nonneg_right hF zero_le
  have hI1 : ∀ F i, ∫⁻ t, g1 F i t ≤ ENNReal.ofReal
      (if i ∈ F then μ⁻¹ * Λ * (C4 * ε) else μ⁻¹ * Λ * C2) := by
    intro F i
    simp only [g1]
    split_ifs
    · exact hmin L δ hL hδ _ _ _ _
    · exact hmaj L μ hL1 hLη hμ _ _ _ _
  have hKC : ∀ C, 0 ≤ C → C ≤ K → ∀ u, 0 ≤ u → μ⁻¹ * Λ * (C * u) ≤ x * u := by
    intro C hC hCK u hu
    have : μ⁻¹ * Λ * (C * u) = (Λ / μ) * C * u := by ring
    rw [this, show x * u = (Λ / μ) * K * u by simp only [x]; ring]
    gcongr
  have hP1 : ∀ F, A F * ∏ i, (if i ∈ F then μ⁻¹ * Λ * (C4 * ε) else μ⁻¹ * Λ * C2) ≤
      A F * (x ^ Fintype.card ι * ε ^ F.card) := by
    intro F
    refine mul_le_mul_of_nonneg_left ?_ (hA0 F)
    have h := prod_le_pow_mul_prod (B := fun i => if i ∈ F then μ⁻¹ * Λ * (C4 * ε) else μ⁻¹ * Λ * C2)
      (u := fun i => if i ∈ F then ε else 1) (x := x) (fun i => by split_ifs <;> positivity)
      (fun i => by
        split_ifs
        · exact hKC C4 hC4 (by simp only [K]; linarith) ε hε
        · simpa using hKC C2 hC2 (by simp only [K]; linarith) 1 zero_le_one)
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [Finset.prod_ite_mem, Finset.univ_inter, prod_const]
  have hm1 : ∀ F, Measurable fun s : ι → ℝ => ENNReal.ofReal (A F) * ∏ i, g1 F i (s i) :=
    fun F => measurable_const.mul (Finset.measurable_prod _ fun i _ =>
      (hg1 F i).comp (measurable_pi_apply i))
  have hfinal : ‖multiSum L μ Φ c.p c.q c.ξ c.ζ‖ₑ ≤
      ENNReal.ofReal (∑ F ∈ (univ : Finset ι).powerset, A F * (x ^ Fintype.card ι * ε ^ F.card)) := by
    rw [multiSum_eq hL0 μ hrep]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_finsetSum _ fun F _ => hm1 F,
      ENNReal.ofReal_sum_of_nonneg fun F _ => mul_nonneg (hA0 F) (by positivity)]
    refine sum_le_sum fun F _ => ?_
    exact (lintegral_const_mul_prod_le _ (g1 F) (hg1 F) _ (fun i => by
      split_ifs <;> positivity) (hI1 F)).trans (ENNReal.ofReal_le_ofReal (hP1 F))
  have hs0 : 0 ≤ ∑ F ∈ (univ : Finset ι).powerset, A F * (x ^ Fintype.card ι * ε ^ F.card) :=
    sum_nonneg fun F _ => mul_nonneg (hA0 F) (by positivity)
  rw [← ofReal_norm] at hfinal
  refine ((ENNReal.ofReal_le_ofReal_iff hs0).1 hfinal).trans (le_of_eq ?_)
  rw [mul_sum]
  exact sum_congr rfl fun F _ => by ring

/-- **The crude cell estimate for D5c's filtered profile**, uniform in the modulations and the scales `S_j ≥ 1`. -/
theorem exists_filt_crude_cell_bound (hd : 3 ≤ d) (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hb : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ * (1 + s ^ 2) ^ d ≤ Kp) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 20) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (L δ : ℝ), 2 ≤ L → 2 ≤ L ^ η → δ ∈ Ioc (0 : ℝ) 1 →
      (n : ℝ) * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
        L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)) ≤ 1 / 2 →
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ∀ (S : Fin n → ℝ), (∀ j, 1 ≤ S j) → ∀ (c : CellData d (Fin n)),
      ‖multiSum L (δ * L ^ (2 * γ)) (filtProf J S Ψ₁) c.p c.q c.ξ c.ζ‖ ≤
        2 * (K * max 1 Kp * C₀ * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n := by
  obtain ⟨K, hK0, hcore⟩ := exists_crude_core_bound hd hγ hη0 hη
  refine ⟨K, hK0, ?_⟩
  intro n L δ hL hLη hδ hnq J Ψ₁ hΨ hD S hS c
  have hd1 : 1 ≤ d := by omega
  have hC0 : 0 ≤ C₀ := by linarith
  have hD0 : ∀ k, 0 ≤ C₀ ^ n * ((4 * k).factorial : ℝ) := fun k => by positivity
  have hL0 : 0 < L := by linarith
  set M := max 1 Kp
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  set B : ℝ := ((8 * d * n + 1 : ℕ) : ℝ)
  set ε : ℝ := L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)
  have hε : 0 ≤ ε := Real.rpow_nonneg hL0.le _
  set q : ℝ := 2 ^ (d + 1) * B ^ (8 * d) * ε
  have hq : 0 ≤ q := by positivity
  set A : Finset (Fin n) → ℝ := fun F => M ^ n * C₀ ^ n * (2 ^ (d + 1) * B ^ (8 * d)) ^ F.card
  have hA : ∀ F s, ‖filtHat J S Ψ₁ s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F := fun F s =>
    (norm_filtHat_mul_le J S Kp hKp (fun j s' => hb (S j) (hS j) s') hΨ hD hD0 F s).trans
      (filt_weight_le J Kp hKp hC₀ F)
  have hrep := isFourierRep_filtProf hd1 J S hS hΨ hD hD0
  have h := hcore (Fin n) L δ hL hLη hδ _ _ hrep A hA c
  rw [Fintype.card_fin] at h
  refine h.trans ?_
  have hsum : ∑ F ∈ (univ : Finset (Fin n)).powerset, A F * ε ^ F.card ≤ M ^ n * C₀ ^ n * 2 := by
    have h1 : ∑ F ∈ (univ : Finset (Fin n)).powerset, A F * ε ^ F.card =
        M ^ n * C₀ ^ n * ∑ F ∈ (univ : Finset (Fin n)).powerset, q ^ F.card := by
      rw [mul_sum]
      refine sum_congr rfl fun F _ => ?_
      simp only [A, q, mul_pow]; ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := sum_powerset_erase_pow_le (ι := Fin n) hq (by simpa [q] using hnq)
    rw [← add_sum_erase _ _ (empty_mem_powerset _), Finset.card_empty, pow_zero]
    simp only [Fintype.card_fin] at h2
    have h3 : 2 * (n : ℝ) * q ≤ 1 := by
      have : (n : ℝ) * q ≤ 1 / 2 := hnq
      linarith
    linarith
  have hx : 0 ≤ (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n := by
    have := hδ.1; positivity
  calc (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n *
        ∑ F ∈ (univ : Finset (Fin n)).powerset, A F * ε ^ F.card
      ≤ (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n * (M ^ n * C₀ ^ n * 2) :=
        mul_le_mul_of_nonneg_left hsum hx
    _ = _ := by rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow]; ring

end WaveTurbulence.Flower.FiltCoh
