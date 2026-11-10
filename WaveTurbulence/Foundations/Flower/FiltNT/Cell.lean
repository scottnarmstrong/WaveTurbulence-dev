/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltNT.Profile
public import WaveTurbulence.Foundations.ApproxNT.CellEstimate
public import WaveTurbulence.Foundations.ApproxNT.AppCell
public import WaveTurbulence.Foundations.RegAsymp.ContinuousCellSize

/-! # FILT-NT: the cell estimates for the filtered profile

* `exists_filt_cell_bound`: main's `ApproxNT.exists_cell_bound` for `filtProf J S Ψ₁` (the core bound
  `ApproxNT.exists_core_bound` is generic in the Fourier representation and the weights);
* `filt_continuous_cell_size`: main's `RegAsymp.exists_continuous_cell_size_bound`, the `J`-factors bounded through
  `‖ĝ_S‖_∞` and the `L¹` bound of `cellInt` (no principal-value estimate is needed).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset WithLp WaveTurbulence.ApproxNT
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.Flower.FiltNT

variable {ι : Type} [Fintype ι] [DecidableEq ι]


variable {d : ℕ}

/-- The profile weights, in closed form. -/
theorem filt_weight_le {d n : ℕ} (J : Finset (Fin n)) (Kp : ℝ) (hKp : 0 ≤ Kp) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (F : Finset (Fin n)) :
    Kp ^ J.card * (2 ^ (d * (F.subtype (· ∉ J)).card) *
      ∑ G ∈ (F.subtype (· ∉ J)).powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ)) ≤
      max 1 (Kp) ^ n * C₀ ^ n *
        (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) ^ F.card := by
  set F' := F.subtype (· ∉ J)
  have hF' : F'.card ≤ F.card := by rw [card_subtype]; exact card_filter_le _ _
  have hJ : J.card ≤ n := by simpa using card_le_univ J
  have hFn : F.card ≤ n := by simpa using card_le_univ F
  have hK := hKp
  have hC0 : 0 ≤ C₀ := by linarith
  set B : ℝ := ((8 * d * n + 1 : ℕ) : ℝ)
  have hB : 1 ≤ B := by simp only [B]; exact_mod_cast Nat.le_add_left 1 _
  have hM : Kp ^ J.card ≤ max 1 (Kp) ^ n :=
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
  calc Kp ^ J.card * (2 ^ (d * F'.card) *
        ∑ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ))
      ≤ max 1 (Kp) ^ n * (2 ^ (d * F.card) * (2 ^ F.card * (C₀ ^ n * B ^ (8 * d * F.card)))) := by
        refine mul_le_mul hM ?_ (by positivity) (by positivity)
        refine mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hF')) hsum
          (sum_nonneg fun G _ => by positivity) (by positivity)
    _ = max 1 (Kp) ^ n * C₀ ^ n * (2 ^ (d + 1) * B ^ (8 * d)) ^ F.card := by
        rw [mul_pow, ← pow_mul, ← pow_mul, add_mul, one_mul, pow_add]
        ring



end WaveTurbulence.Flower.FiltNT
