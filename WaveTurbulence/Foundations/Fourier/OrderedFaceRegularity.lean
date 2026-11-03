/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.WeightedOrderedIntegral
import Mathlib.Tactic

/-!
# Smooth boundary-face amplitudes

The endpoint insertion maps are smooth. Every ordered face therefore
retains the time regularity needed when splitting its `L¹` moment bounds.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Appending a final scalar coordinate is smooth. -/
@[fun_prop] theorem contDiff_fin_snoc (n : ℕ) :
    ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) := by
  apply contDiff_pi.mpr
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]; exact contDiff_snd
  · simp only [Fin.snoc_castSucc]; fun_prop

/-- Smoothness of the first boundary face. -/
theorem ordered_upper_face_contDiff {n : ℕ} {A : (Fin (n + 1) → ℝ) → ℂ}
    (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun t : Fin 2 → ℝ =>
      orderedIntegral n (fun v => A (Fin.cons (t 0) v)) (t 0) (t 1)) := by
  apply contDiff_orderedIntegral n
    (F := fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => A (Fin.cons (p.1 0) p.2))
    (a := fun t : Fin 2 → ℝ => t 1) (b := fun t : Fin 2 → ℝ => t 0)
  · have hp : ContDiff ℝ ∞ (fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => (p.1 0, p.2)) := by fun_prop
    exact hA.comp (by simpa only [Function.comp_def] using (contDiff_fin_cons n).comp hp)
  · fun_prop
  · fun_prop

/-- Smoothness of the last boundary face. -/
theorem ordered_lower_face_contDiff {n : ℕ} {A : (Fin (n + 1) → ℝ) → ℂ}
    (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun t : Fin 2 → ℝ =>
      orderedIntegral n (fun v => A (Fin.snoc v (t 1))) (t 0) (t 1)) := by
  apply contDiff_orderedIntegral n
    (F := fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => A (Fin.snoc p.2 (p.1 1)))
    (a := fun t : Fin 2 → ℝ => t 1) (b := fun t : Fin 2 → ℝ => t 0)
  · have hp : ContDiff ℝ ∞ (fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => (p.2, p.1 1)) := by fun_prop
    exact hA.comp (by simpa only [Function.comp_def] using (contDiff_fin_snoc n).comp hp)
  · fun_prop
  · fun_prop

/-- Smoothness of the mixed boundary face in the source's insertion order. -/
theorem ordered_mixed_face_contDiff {n : ℕ} {A : (Fin (n + 2) → ℝ) → ℂ}
    (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun t : Fin 2 → ℝ =>
      orderedIntegral n (fun v => A (Fin.snoc (Fin.cons (t 0) v) (t 1))) (t 0) (t 1)) := by
  apply contDiff_orderedIntegral n
    (F := fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => A (Fin.snoc (Fin.cons (p.1 0) p.2) (p.1 1)))
    (a := fun t : Fin 2 → ℝ => t 1) (b := fun t : Fin 2 → ℝ => t 0)
  · have hp : ContDiff ℝ ∞ (fun p : (Fin 2 → ℝ) × (Fin n → ℝ) => (p.1 0, p.2)) := by fun_prop
    have hcons : ContDiff ℝ ∞ (fun p : (Fin 2 → ℝ) × (Fin n → ℝ) =>
        (Fin.cons (p.1 0) p.2 : Fin (n + 1) → ℝ)) := by
      simpa only [Function.comp_def] using (contDiff_fin_cons n).comp hp
    have hs : ContDiff ℝ ∞ (fun p : (Fin 2 → ℝ) × (Fin n → ℝ) =>
        ((Fin.cons (p.1 0) p.2 : Fin (n + 1) → ℝ), p.1 1)) :=
      hcons.prodMk (by fun_prop)
    exact hA.comp (by simpa only [Function.comp_def] using (contDiff_fin_snoc (n + 1)).comp hs)
  · fun_prop
  · fun_prop

/-- Multiplication by the two smooth endpoint factors preserves smoothness. -/
theorem endpoint_product_contDiff {a b : ℝ → ℝ} {G : (Fin 2 → ℝ) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun t => (a (t 0) : ℂ) * (b (t 1) : ℂ) * G t) :=
  ((Complex.ofRealCLM.contDiff.comp (ha.comp (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp (hb.comp (by fun_prop)))).mul hG

end WaveTurbulence.Fourier
