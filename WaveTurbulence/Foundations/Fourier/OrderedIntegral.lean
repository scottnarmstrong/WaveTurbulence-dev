/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.SmoothIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Smooth ordered time integrals

The recursive oriented simplex integral uses the ordering
`t ≥ u₀ ≥ ⋯ ≥ uₙ₋₁ ≥ s`, and also applies when `t < s`.
The twofold and fourfold integrals in TARGET A.2–A.3 are instances.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The literal recursively ordered integral, including its oriented signs. -/
@[expose] noncomputable def orderedIntegral : (n : ℕ) → ((Fin n → ℝ) → ℂ) → ℝ → ℝ → ℂ
  | 0, F, _, _ => F Fin.elim0
  | n + 1, F, t, s => ∫ u in s..t, orderedIntegral n (fun v => F (Fin.cons u v)) u s

/-- Integration over an ordered simplex preserves smooth parameter dependence. -/
theorem contDiff_orderedIntegral (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
      {F : E × (Fin n → ℝ) → ℂ} {a b : E → ℝ},
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      ContDiff ℝ ∞ (fun w => orderedIntegral n (fun v => F (w, v)) (b w) (a w)) := by
  induction n with
  | zero =>
    intro E _ _ _ F a b hF _ _
    exact hF.comp (contDiff_id.prodMk contDiff_const)
  | succ n ih =>
    intro E _ _ _ F a b hF ha hb
    change ContDiff ℝ ∞ (fun w => ∫ u in a w..b w,
      orderedIntegral n (fun v => F (w, Fin.cons u v)) u (a w))
    apply contDiff_intervalIntegral
      (G := fun p : E × ℝ => orderedIntegral n (fun v => F (p.1, Fin.cons p.2 v)) p.2 (a p.1))
      (a := a) (b := b) ?_ ha hb
    apply ih (F := fun p : (E × ℝ) × (Fin n → ℝ) => F (p.1.1, Fin.cons p.1.2 p.2))
      (a := fun p : E × ℝ => a p.1) (b := fun p : E × ℝ => p.2)
    · apply hF.comp
      apply (contDiff_fst.comp contDiff_fst).prodMk
      apply contDiff_pi.mpr
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact contDiff_snd.comp contDiff_fst
      · simp only [Fin.cons_succ]; fun_prop
    · exact ha.comp contDiff_fst
    · exact contDiff_snd

/-- The upper-endpoint derivative of an ordered integral is its first boundary face. -/
theorem hasDerivAt_orderedIntegral_upper (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (t s : ℝ) :
    HasDerivAt (fun t => orderedIntegral (n + 1) F t s)
      (orderedIntegral n (fun v => F (Fin.cons t v)) t s) t := by
  have hi : ContDiff ℝ ∞ (fun u : ℝ =>
      orderedIntegral n (fun v => F (Fin.cons u v)) u s) := by
    apply contDiff_orderedIntegral n
      (F := fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
      (a := fun _ => s) (b := id)
    · apply hF.comp
      apply contDiff_pi.mpr
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact contDiff_fst
      · simp only [Fin.cons_succ]; fun_prop
    · exact contDiff_const
    · exact contDiff_id
  exact intervalIntegral.integral_hasDerivAt_right (hi.continuous.intervalIntegrable s t)
    hi.continuous.stronglyMeasurable.stronglyMeasurableAtFilter hi.continuous.continuousAt

/-- Simultaneous time translation acts by translating every integration variable.
Phases depending only on differences are therefore unchanged. -/
theorem orderedIntegral_translate (n : ℕ) (F : (Fin n → ℝ) → ℂ) (t s c : ℝ) :
    orderedIntegral n F (t + c) (s + c) =
      orderedIntegral n (fun v => F (fun i => v i + c)) t s := by
  induction n generalizing t s with
  | zero =>
    unfold orderedIntegral
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [orderedIntegral]
    rw [← intervalIntegral.integral_comp_add_right]
    apply intervalIntegral.integral_congr
    intro u _
    change orderedIntegral n (fun v => F (Fin.cons (u + c) v)) (u + c) (s + c) =
      orderedIntegral n (fun v : Fin n → ℝ => F (fun i => (Fin.cons u v : Fin (n + 1) → ℝ) i + c)) u s
    rw [ih]
    congr 1
    funext v
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> rfl

end WaveTurbulence.Fourier
