/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplOn
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFix
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildB
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ASum

/-! # RT-GATE (ii), fork C: tools for the one-pinned couples on a general partner window

* `rt1t_piece_trace`: a couple piece at the pinned clock `s` (window `[P, P+1]`) and the partner clock `x 1` (window
  `[q, q+1]`), in either orientation, on the triangle `triS q q`, by its norm on its own mixed box;
* `rt1t_rb_lost`: one lost link costs `L`;
* `rt1t_rhs`: the right side of `RtOneOn` from `C · L^{3c'} · L · c² C₁² rb` (or `C₁³`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **A couple piece at the pinned clock and the partner clock**, mixed windows, either orientation. -/
theorem rt1t_piece_trace {θ : ℝ} (hθ : 0 ≤ θ) {P q s : ℝ} (hPs : P ≤ s) (hsP : s ≤ P + 1) (f : ℝ → ℝ → ℂ)
    (o : ℝ → ℝ → Fin 2 → ℝ) (ho : (∀ u v, o u v 0 = u ∧ o u v 1 = v) ∨ (∀ u v, o u v 0 = v ∧ o u v 1 = u))
    (hf : Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1))) :
    rn θ (triS q q) (fun x => f (o s (x 1) 0) (o s (x 1) 1)) ≤
      Regref.traceConst (r := 2) θ VineEstS3.chiUnit *
        rn θ (timeBox (o P q 0) (o P q 1)) (fun x => f (x 0) (x 1)) := by
  have hcells : ∀ x ∈ triS q q, ∀ i, x i ∈ Icc ((fun _ : Fin 2 => q) i) ((fun _ : Fin 2 => q) i + 1) := by
    intro x hx i
    fin_cases i
    · exact hx.1.1
    · exact hx.1.2
  rcases ho with ho | ho
  · have e1 : (fun x : Fin 2 → ℝ => f (o s (x 1) 0) (o s (x 1) 1)) =
        fun x => (fun y : Fin 2 → ℝ => f (y 0) (y 1)) (Function.update x 0 s) := by
      funext x; rw [(ho _ _).1, (ho _ _).2]; simp
    rw [e1, (ho P q).1, (ho P q).2]
    refine rn_trace hθ (fun _ => q) (B := timeBox P q) hcells _ hf 0 s fun x hx => ?_
    refine VineEstS3.timeBox_subset_closure_interior P q ⟨?_, ?_⟩
    · simp only [Function.update_self]; exact ⟨hPs, hsP⟩
    · rw [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]; exact hx.1.2
  · have e1 : (fun x : Fin 2 → ℝ => f (o s (x 1) 0) (o s (x 1) 1)) =
        fun x => (fun y : Fin 2 → ℝ => f (y 1) (y 0)) (Function.update x 0 s) := by
      funext x; rw [(ho _ _).1, (ho _ _).2]; simp
    rw [e1, (ho P q).1, (ho P q).2]
    have hsw : rn θ (timeBox P q) (fun y : Fin 2 → ℝ => f (y 1) (y 0)) =
        rn θ (timeBox q P) (fun x => f (x 0) (x 1)) := by
      rw [← tc2a_swap_box θ q P (fun x => f (x 0) (x 1))]
      congr 1
    rw [← hsw]
    refine rn_trace hθ (fun _ => q) (B := timeBox P q) hcells _
      (hf.comp (show Continuous fun y : Fin 2 → ℝ => ![y 1, y 0] by fun_prop)) 0 s fun x hx => ?_
    refine VineEstS3.timeBox_subset_closure_interior P q ⟨?_, ?_⟩
    · simp only [Function.update_self]; exact ⟨hPs, hsP⟩
    · rw [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]; exact hx.1.2

/-- **One lost link costs `L`.** -/
theorem rt1t_rb_lost {P : WTParams} (hL : 1 ≤ P.L) (hC1 : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hη : 0 ≤ P.η) (n : ℕ)
    {g g' : ℕ} (h1 : g' ≤ g) (h2 : g ≤ g' + 1) : rb P n g' ≤ P.L * rb P n g := by
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · rw [h]; exact le_mul_of_one_le_left (rb_nonneg hC1 hδ hL0 n g) hL
  · have hg : g' = g - 1 := by omega
    rw [hg]
    have := rb_pred_le hL hC1 hδ hη n (show 1 ≤ g by omega)
    rwa [Real.rpow_one] at this

/-- **The right side of `RtOneOn`** from a two- or three-piece budget with `L^{3c'}` and a lost link. -/
theorem rt1t_rhs {P : WTParams} (hL : 1 ≤ P.L) (hC11 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) {c' : ℝ} (hc' : 0 ≤ c')
    {a : ℕ} (ha : a ≤ 3) (n g : ℕ) {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS) :
    P.L ^ (3 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ a * rb P n g) * leaf * CS)) ≤
      P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P n g) * leaf * CS)) := by
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have h34 : P.L ^ (3 * c') ≤ P.L ^ (4 * c') := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hCa : P.C₁ ^ a ≤ P.C₁ ^ 3 := pow_le_pow_right₀ hC11 ha
  have hr := rb_nonneg (by linarith) hδ hL0 n g
  have hc2 : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  have hX : 0 ≤ P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ a * rb P n g) * leaf * CS) := by
    have : 0 ≤ P.C₁ ^ a := pow_nonneg (by linarith) _
    positivity
  calc P.L ^ (3 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ a * rb P n g) * leaf * CS))
      ≤ P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ a * rb P n g) * leaf * CS)) :=
        mul_le_mul_of_nonneg_right h34 hX
    _ ≤ _ := by
        have : 0 ≤ P.L ^ (4 * c') := Real.rpow_nonneg hL0 _
        gcongr

theorem rt1t_rpow3 {L : ℝ} (hL : 0 < L) (c' : ℝ) : L ^ c' * L ^ c' * L ^ c' = L ^ (3 * c') := by
  rw [show 3 * c' = c' + c' + c' by ring, Real.rpow_add hL, Real.rpow_add hL]

end WaveTurbulence.Flower.ProtRT
