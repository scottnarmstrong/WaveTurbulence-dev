/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RungBall
public import WaveTurbulence.Foundations.Spine.Outer
/-! # Time integral of the one-variable-sharp rung (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory Set WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint

variable {d : ℕ}

lemma continuous_rungSum_fst (L c : ℝ) (w : Pt d → ℂ) (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ)
    (τ : ℝ) : Continuous (fun s : ℝ => rungSum L c w S lam ν (s, τ)) := by
  unfold rungSum
  refine continuous_finset_sum _ (fun p _ => continuous_const.mul ?_)
  unfold e
  exact Complex.continuous_exp.comp (by fun_prop)

/-- Inner time integral with distance `m` from the other box. -/
theorem ball_inner {C0 : ℝ} (hd : 3 ≤ d)
    (hmaj : ∀ {L : ℝ}, 1 ≤ L → ∀ (a b : Fin d → ℝ)
    (ι : (Fin d → ℤ) → ℂ), (∀ x, ‖ι x‖ ≤ 1) → ∀ (I : Fin d → Finset ℤ),
    (∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset I) → ∀ (lam ν : Pt d →+ ℝ) (τ Ls Kc : ℝ), 0 ≤ Kc →
    (∀ i, ((I i).card : ℝ) ≤ Kc ∧ ∀ n ∈ I i, ∀ n' ∈ I i, |(n : ℝ) - n'| ≤ Kc) → Kc ≤ 4 * L →
    2 * Ls * Kc ≤ (4 * L) ^ 2 → ∀ σ : ℝ, |σ| ≤ Ls →
      ‖rungSum L 1 (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν (τ + σ / 16, τ)‖ ≤
        (C0 * (4 * L)) ^ d * 1 + (C0 * (4 * L) ^ 2) ^ d * ((1 + |σ|) ^ d)⁻¹)
    (hC0 : 0 ≤ C0) {L : ℝ} (hL : 1 ≤ L) (a b : Fin d → ℝ) (ι : (Fin d → ℤ) → ℂ)
    (hι : ∀ x, ‖ι x‖ ≤ 1) (I : Fin d → Finset ℤ) (hQ : ∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset I)
    (lam ν : Pt d →+ ℝ) (c l u t Wd Kc m : ℝ) (hc : 0 < c) (hlu : l ≤ u)
    (hwlo : -Wd ≤ 16 * c * (l - t)) (hwhi : 16 * c * (u - t) ≤ Wd) (hm : 0 ≤ m)
    (hdist : ∀ s ∈ Icc l u, m ≤ |16 * c * (s - t)|) (hKc : 0 ≤ Kc)
    (hI : ∀ i, ((I i).card : ℝ) ≤ Kc ∧ ∀ n ∈ I i, ∀ n' ∈ I i, |(n : ℝ) - n'| ≤ Kc)
    (hKL : Kc ≤ 4 * L) (hLs : 2 * (Wd + 1) * Kc ≤ (4 * L) ^ 2) :
    (∫ s in Icc l u, ‖rungSum L c (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν (s, t)‖) ≤
      (u - l) * (C0 * (4 * L)) ^ d * 1 + (16 * c)⁻¹ * ((C0 * (4 * L) ^ 2) ^ d *
        (2 / ((d : ℝ) - 1) * (1 + m) ^ (-((d : ℝ) - 1))) + 0) := by
  set S := Fintype.piFinset I ×ˢ byBox L b with hS
  set f : ℝ → ℝ := fun σ => ‖rungSum L 1 (ballW L a b ι) S lam ν (t + σ / 16, t)‖ with hf
  have hfc : Continuous f := by
    have := continuous_rungSum_fst L 1 (ballW L a b ι) S lam ν t
    exact (this.comp (by fun_prop : Continuous fun σ : ℝ => t + σ / 16)).norm
  have heq : ∀ s : ℝ, ‖rungSum L c (ballW L a b ι) S lam ν (s, t)‖ = f (16 * c * (s - t)) := by
    intro s
    simp only [hf]
    rw [rungSum_c_eq]
    congr 3
    ring
  have hmain := inner_window_bound hd hfc (fun σ => norm_nonneg _) (c := 16 * c) (l := l) (u := u)
    (t := t) (W := Wd) (Ls := Wd + 1) (A1 := (C0 * (4 * L)) ^ d * 1)
    (A2 := (C0 * (4 * L) ^ 2) ^ d) (Al := 0) (m := m) (by positivity) hlu hwlo hwhi hm hdist
    (by positivity) (by positivity)
    (fun σ hσ => hmaj hL a b ι hι I hQ lam ν t (Wd + 1) Kc hKc hI hKL hLs σ hσ)
    (by
      have : {σ : ℝ | Wd + 1 ≤ |σ| ∧ |σ| ≤ Wd} = ∅ := by
        ext σ; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
        intro h; linarith
      rw [this]; simp)
  calc (∫ s in Icc l u, ‖rungSum L c (ballW L a b ι) S lam ν (s, t)‖)
      = ∫ s in Icc l u, f (16 * c * (s - t)) := setIntegral_congr_fun measurableSet_Icc (fun s _ => heq s)
    _ ≤ _ := hmain.trans (le_of_eq (by ring))

/-- The one-variable-sharp rung: the pointwise majorant constant `C0`. -/
theorem rung_ball_time (hd : 3 ≤ d) : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ (a b : Fin d → ℝ)
    (ι : (Fin d → ℤ) → ℂ), (∀ x, ‖ι x‖ ≤ 1) → ∀ (I : Fin d → Finset ℤ),
    (∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset I) → ∀ (lam ν : Pt d →+ ℝ) (c l u v w Wd Kc : ℝ),
    0 < c → l ≤ u → v ≤ w → (∀ t ∈ Icc v w, -Wd ≤ 16 * c * (l - t) ∧ 16 * c * (u - t) ≤ Wd) →
    0 ≤ Kc → (∀ i, ((I i).card : ℝ) ≤ Kc ∧ ∀ n ∈ I i, ∀ n' ∈ I i, |(n : ℝ) - n'| ≤ Kc) →
    Kc ≤ 4 * L → 2 * (Wd + 1) * Kc ≤ (4 * L) ^ 2 →
    (∫ t in Icc v w, ∫ s in Icc l u,
        ‖rungSum L c (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν (s, t)‖) ≤
      (w - v) * ((u - l) * (C0 * (4 * L)) ^ d * 1 +
        (16 * c)⁻¹ * ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1)))) ∧
    (u ≤ v ∨ w ≤ l →
      (∫ t in Icc v w, ∫ s in Icc l u,
        ‖rungSum L c (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν (s, t)‖) ≤
      (w - v) * ((u - l) * (C0 * (4 * L)) ^ d * 1) +
        (16 * c)⁻¹ * ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1))) * (16 * c)⁻¹) := by
  obtain ⟨C0, hC0, hmaj⟩ := ball_majorant
  refine ⟨C0, hC0, ?_⟩
  intro L hL a b ι hι I hQ lam ν c l u v w Wd Kc hc hlu hvw hwin hKc hI hKL hLs
  have hc' : 0 < 16 * c := by positivity
  have hmaj' := fun {L : ℝ} (hL : 1 ≤ L) a b ι hι I hQ lam ν τ Ls Kc hKc hI hKL hLs σ hσ =>
    hmaj hL d a b ι hι I hQ lam ν τ Ls Kc hKc hI hKL hLs σ hσ
  have hG0 : ∀ t : ℝ, 0 ≤ ∫ s in Icc l u,
      ‖rungSum L c (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν (s, t)‖ :=
    fun t => integral_nonneg (fun s => norm_nonneg _)
  have hA2 : 0 ≤ (C0 * (4 * L) ^ 2) ^ d := by positivity
  have hK : 0 ≤ 2 / ((d : ℝ) - 1) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    apply div_nonneg (by norm_num); linarith
  constructor
  · refine (outer_same hvw hG0 (B := (u - l) * (C0 * (4 * L)) ^ d * 1 +
      (16 * c)⁻¹ * ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1)))) (fun t ht => ?_))
    have := ball_inner hd hmaj' hC0 hL a b ι hι I hQ lam ν c l u t Wd Kc 0 hc hlu (hwin t ht).1
      (hwin t ht).2 le_rfl (fun s _ => abs_nonneg _) hKc hI hKL hLs
    refine this.trans (le_of_eq ?_)
    simp
  · intro hsep
    have hb : ∀ t ∈ Icc v w, (∫ s in Icc l u,
        ‖rungSum L c (ballW L a b ι) (Fintype.piFinset I ×ˢ byBox L b) lam ν (s, t)‖) ≤
        (u - l) * (C0 * (4 * L)) ^ d + ((16 * c)⁻¹ * ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1)))) *
          (1 + (if u ≤ v then 16 * c * (t - v) else 16 * c * (w - t))) ^ (-((d : ℝ) - 1)) := by
      intro t ht
      set m : ℝ := (if u ≤ v then 16 * c * (t - v) else 16 * c * (w - t)) with hm
      have hm0 : 0 ≤ m := by
        rw [hm]
        split_ifs
        · exact mul_nonneg hc'.le (by linarith [ht.1])
        · exact mul_nonneg hc'.le (by linarith [ht.2])
      have hdist : ∀ s ∈ Icc l u, m ≤ |16 * c * (s - t)| := by
        intro s hs
        rw [hm]
        split_ifs with huv
        · rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc'.le (by linarith [hs.2, ht.1]))]
          nlinarith [hs.2, ht.1]
        · have hwl : w ≤ l := by rcases hsep with h | h; exact absurd h huv; exact h
          rw [abs_of_nonneg (mul_nonneg hc'.le (by linarith [hs.1, ht.2]))]
          nlinarith [hs.1, ht.2]
      have := ball_inner hd hmaj' hC0 hL a b ι hι I hQ lam ν c l u t Wd Kc m hc hlu (hwin t ht).1
        (hwin t ht).2 hm0 hdist hKc hI hKL hLs
      refine this.trans (le_of_eq ?_)
      simp only [mul_one, add_zero]
      ring
    have := outer_diff hd hc' hvw (P := (u - l) * (C0 * (4 * L)) ^ d)
      (Q := (16 * c)⁻¹ * ((C0 * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1))))
      (by positivity) (by positivity) (u ≤ v) hG0 hb
    refine this.trans (le_of_eq ?_)
    simp only [mul_one]

end WaveTurbulence.LadderDecay
