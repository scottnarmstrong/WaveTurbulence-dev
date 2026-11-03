/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.CoreTheorem
public import WaveTurbulence.Foundations.ApproxNT.Profile

/-!
# The estimate for one cell configuration (packet NT6)

The core estimate applied to the truncated profile `∏_{j∈J} m_{K_j} · Ψ₁`, with the weights
`A_F ≤ M^n C^n (2^{d+1} (8dn)^{8d})^{|F|}` coming from `‖∂^ρΨ₁‖_{L¹} ≤ C^n (4|ρ|)!`. The minor-arc
sum `∑_{F≠∅} A_F ε^{|F|}` is at most `2n q M^n C^n` with `q = 2^{d+1}(8dn)^{8d} ε`, provided
`n q ≤ 1/2`. This is where the source's restriction `n ≤ (log L)^3` entered (the factor `(8f)!`
of DH21 L1640); here it is replaced by the explicit condition `n q ≤ 1/2`, which holds for all
`n ≤ (log L)^A`, any fixed `A`, once `L` is large.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

theorem sum_powerset_erase_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℝ} (hq : 0 ≤ q)
    (hnq : (Fintype.card ι : ℝ) * q ≤ 1 / 2) :
    ∑ F ∈ (univ : Finset ι).powerset.erase ∅, q ^ F.card ≤ 2 * Fintype.card ι * q := by
  have hall : ∑ F ∈ (univ : Finset ι).powerset, q ^ F.card = (1 + q) ^ Fintype.card ι := by
    rw [← card_univ, ← prod_const, prod_one_add]
    exact sum_congr rfl fun F _ => (prod_const q).symm
  have herase : ∑ F ∈ (univ : Finset ι).powerset.erase ∅, q ^ F.card =
      (1 + q) ^ Fintype.card ι - 1 := by
    rw [← hall, ← sum_erase_add _ _ (empty_mem_powerset _), card_empty, pow_zero]; ring
  rw [herase]
  have key : ∀ k : ℕ, k ≤ Fintype.card ι → (1 + q) ^ k ≤ 1 + 2 * k * q := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have hkq : (k : ℝ) * q ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast (by omega : k ≤ Fintype.card ι)) hq) hnq
        calc (1 + q) ^ (k + 1) = (1 + q) ^ k * (1 + q) := pow_succ _ _
          _ ≤ (1 + 2 * k * q) * (1 + q) := mul_le_mul_of_nonneg_right h1 (by linarith)
          _ ≤ 1 + 2 * ((k + 1 : ℕ) : ℝ) * q := by
              push_cast
              nlinarith [mul_nonneg hq hq]
  linarith [key (Fintype.card ι) le_rfl]

theorem factorial_le_pow_of_le {f n k : ℕ} (hf : f ≤ n) :
    ((k * f).factorial : ℝ) ≤ ((k * n + 1 : ℕ) : ℝ) ^ (k * f) := by
  have h1 : (k * f).factorial ≤ (k * f) ^ (k * f) := Nat.factorial_le_pow _
  have h2 : (k * f) ^ (k * f) ≤ (k * n + 1) ^ (k * f) :=
    Nat.pow_le_pow_left (by have := Nat.mul_le_mul_left k hf; omega) _
  exact_mod_cast h1.trans h2

theorem kerConst_nonneg (d : ℕ) : 0 ≤ kerConst d := by
  have := psiConstA_nonneg
  have : 0 ≤ SchwartzMap.seminorm ℝ (2 * d) 0 psiHat := apply_nonneg _ _
  unfold kerConst; positivity

/-- The profile weights, in closed form. -/
theorem profile_weight_le {n : ℕ} (J : Finset (Fin n)) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (F : Finset (Fin n)) :
    kerConst d ^ J.card * (2 ^ (d * (F.subtype (· ∉ J)).card) *
      ∑ G ∈ (F.subtype (· ∉ J)).powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ)) ≤
      max 1 (kerConst d) ^ n * C₀ ^ n *
        (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) ^ F.card := by
  set F' := F.subtype (· ∉ J)
  have hF' : F'.card ≤ F.card := by rw [card_subtype]; exact card_filter_le _ _
  have hJ : J.card ≤ n := by simpa using card_le_univ J
  have hFn : F.card ≤ n := by simpa using card_le_univ F
  have hK := kerConst_nonneg d
  have hC0 : 0 ≤ C₀ := by linarith
  set B : ℝ := ((8 * d * n + 1 : ℕ) : ℝ)
  have hB : 1 ≤ B := by simp only [B]; exact_mod_cast Nat.le_add_left 1 _
  have hM : kerConst d ^ J.card ≤ max 1 (kerConst d) ^ n :=
    (pow_le_pow_left₀ hK (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) hJ)
  have hterm : ∀ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ) ≤
      C₀ ^ n * B ^ (8 * d * F.card) := by
    intro G hG
    have hGc : G.card ≤ F.card := (card_le_card (mem_powerset.1 hG)).trans hF'
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : 4 * (G.card * (2 * d)) = (8 * d) * G.card := by ring
    rw [h1]
    calc (((8 * d) * G.card).factorial : ℝ) ≤ B ^ ((8 * d) * G.card) :=
          factorial_le_pow_of_le (hGc.trans hFn)
      _ ≤ B ^ (8 * d * F.card) := pow_le_pow_right₀ hB (Nat.mul_le_mul_left _ hGc)
  have hsum : ∑ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ) ≤
      2 ^ F.card * (C₀ ^ n * B ^ (8 * d * F.card)) := by
    calc ∑ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ)
        ≤ ∑ _G ∈ F'.powerset, C₀ ^ n * B ^ (8 * d * F.card) := sum_le_sum hterm
      _ = 2 ^ F'.card * (C₀ ^ n * B ^ (8 * d * F.card)) := by
          rw [sum_const, card_powerset, nsmul_eq_mul]; push_cast; ring
      _ ≤ 2 ^ F.card * (C₀ ^ n * B ^ (8 * d * F.card)) := by
          gcongr
          · norm_num
  calc kerConst d ^ J.card * (2 ^ (d * F'.card) *
        ∑ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ))
      ≤ max 1 (kerConst d) ^ n * (2 ^ (d * F.card) * (2 ^ F.card * (C₀ ^ n * B ^ (8 * d * F.card)))) := by
        refine mul_le_mul hM ?_ (by positivity) (by positivity)
        refine mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hF')) hsum
          (sum_nonneg fun G _ => by positivity) (by positivity)
    _ = max 1 (kerConst d) ^ n * C₀ ^ n * (2 ^ (d + 1) * B ^ (8 * d)) ^ F.card := by
        rw [mul_pow, ← pow_mul, ← pow_mul, add_mul, one_mul, pow_add]
        ring

/-- The estimate for one cell configuration. -/
theorem exists_cell_bound (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 20) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (L δ : ℝ), 2 ≤ L → 2 ≤ L ^ η → δ ∈ Set.Ioc (0 : ℝ) 1 →
      (n : ℝ) * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
        L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)) ≤ 1 / 2 →
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ∀ (Kj : Fin n → ℕ) (c : CellData d (Fin n)),
      ‖multiSum L (δ * L ^ (2 * γ)) (truncProfile J Kj Ψ₁) c.p c.q c.ξ c.ζ -
          ((L ^ (2 * d) : ℝ) : ℂ) ^ n *
            multiInt (δ * L ^ (2 * γ)) (truncProfile J Kj Ψ₁) c.p c.q c.ξ c.ζ‖ ≤
        (K * max 1 (kerConst d) * C₀ * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n *
          (∑ i, (L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) + L⁻¹) +
            2 * n * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
              L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η))) := by
  obtain ⟨K, hK0, hcore⟩ := exists_core_bound hd hγ hη0 hη
  refine ⟨K, hK0, ?_⟩
  intro n L δ hL hLη hδ hnq J Ψ₁ hΨ hD Kj c
  have hd1 : 1 ≤ d := by omega
  have hD0 : ∀ k, 0 ≤ C₀ ^ n * ((4 * k).factorial : ℝ) := fun k => by
    have : 0 ≤ C₀ := by linarith
    positivity
  have hL0 : 0 < L := by linarith
  set M := max 1 (kerConst d)
  set B : ℝ := ((8 * d * n + 1 : ℕ) : ℝ)
  set ε : ℝ := L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)
  have hε : 0 ≤ ε := Real.rpow_nonneg hL0.le _
  set q : ℝ := 2 ^ (d + 1) * B ^ (8 * d) * ε
  have hq : 0 ≤ q := by positivity
  set A : Finset (Fin n) → ℝ := fun F => M ^ n * C₀ ^ n * (2 ^ (d + 1) * B ^ (8 * d)) ^ F.card
  have hA : ∀ F s, ‖truncProfileHat J Kj Ψ₁ s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F := fun F s =>
    (norm_truncProfileHat_mul_le hd1 J Kj hΨ hD hD0 F s).trans (profile_weight_le J hC₀ F)
  have hrep := isFourierRep_truncProfile hd1 J Kj hΨ hD hD0
  have h := hcore (Fin n) L δ hL hLη hδ _ _ hrep A hA c
  rw [Fintype.card_fin] at h
  refine h.trans ?_
  have hμ : 0 < δ * L ^ (2 * γ) := mul_pos hδ.1 (Real.rpow_pos_of_pos hL0 _)
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hC0 : 0 ≤ C₀ := by linarith
  have hsumF : ∑ F ∈ (univ : Finset (Fin n)).powerset.erase ∅, A F * ε ^ F.card ≤
      M ^ n * C₀ ^ n * (2 * n * q) := by
    have h1 : ∑ F ∈ (univ : Finset (Fin n)).powerset.erase ∅, A F * ε ^ F.card =
        M ^ n * C₀ ^ n * ∑ F ∈ (univ : Finset (Fin n)).powerset.erase ∅, q ^ F.card := by
      rw [mul_sum]
      refine sum_congr rfl fun F _ => ?_
      simp only [A, q, mul_pow]; ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := sum_powerset_erase_pow_le (ι := Fin n) hq (by simpa [q] using hnq)
    simpa using h2
  have hA0 : A ∅ = M ^ n * C₀ ^ n := by simp [A]
  rw [hA0]
  have hx : 0 ≤ (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n := by positivity
  calc (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n *
        (M ^ n * C₀ ^ n * ∑ i, (L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) + L⁻¹) +
          ∑ F ∈ (univ : Finset (Fin n)).powerset.erase ∅, A F * ε ^ F.card)
      ≤ (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n *
        (M ^ n * C₀ ^ n * ∑ i, (L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) + L⁻¹) +
          M ^ n * C₀ ^ n * (2 * n * q)) := by gcongr
    _ = _ := by
        simp only [q, B, ε, M]
        rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, mul_pow]
        ring

end WaveTurbulence.ApproxNT
