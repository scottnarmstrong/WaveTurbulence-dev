/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded convergence in ordered time integrals

The amplitudes may converge to discontinuous time-order indicators.
Only the approximating amplitudes need smoothness.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace WaveTurbulence.Incoh

/-- A crude bound on a bounded clock interval, valid without integrability assumptions. -/
theorem norm_orderedIntegral_le (n : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (F : (Fin n → ℝ) → ℂ) (hF : ∀ v, ‖F v‖ ≤ C)
    {t s : ℝ} (ht : t ∈ Icc (-R) R) (hs : s ∈ Icc (-R) R) :
    ‖Fourier.orderedIntegral n F t s‖ ≤ C * (2 * R) ^ n := by
  induction n generalizing t s with
  | zero => simpa only [Fourier.orderedIntegral, pow_zero, mul_one] using hF Fin.elim0
  | succ n ih =>
    change ‖∫ u in s..t, Fourier.orderedIntegral n (fun v => F (Fin.cons u v)) u s‖ ≤ _
    have hsub : uIoc s t ⊆ Icc (-R) R :=
      uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)
    calc
      _ ≤ (C * (2 * R) ^ n) * |t - s| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu =>
          ih _ (fun v => hF _) (hsub hu) hs)
      _ ≤ (C * (2 * R) ^ n) * (2 * R) :=
        mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [ht.1, hs.2],
          by linarith [ht.2, hs.1]⟩) (mul_nonneg hC (pow_nonneg (by linarith) _))
      _ = _ := by rw [pow_succ]; ring

/-- Dominated convergence on a fixed oriented interval. -/
theorem tendsto_intervalIntegral_of_bounded {Fₙ : ℕ → ℝ → ℂ} {F : ℝ → ℂ}
    (a b C : ℝ) (hm : ∀ n, AEStronglyMeasurable (Fₙ n) (volume.restrict (uIoc a b)))
    (hb : ∀ n x, x ∈ uIoc a b → ‖Fₙ n x‖ ≤ C)
    (hl : ∀ x, x ∈ uIoc a b → Tendsto (fun n => Fₙ n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫ x in a..b, Fₙ n x) atTop (𝓝 (∫ x in a..b, F x)) := by
  let : IsFiniteMeasure (volume.restrict (uIoc a b)) := Real.isFiniteMeasure_restrict_Ioc _ _
  have ht : Tendsto (fun n => ∫ x in uIoc a b, Fₙ n x) atTop
      (𝓝 (∫ x in uIoc a b, F x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C) hm (integrable_const C)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      exact hb n x hx
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      exact hl x hx
  rcases le_total a b with hab | hba
  · simpa only [intervalIntegral.integral_of_le hab, uIoc_of_le hab] using ht
  · simpa only [intervalIntegral.integral_of_ge hba, uIoc_of_ge hba] using ht.neg

/-- Pointwise bounded smooth approximations converge inside every ordered integral. -/
theorem tendsto_orderedIntegral_of_bounded (n : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    {Fₙ : ℕ → (Fin n → ℝ) → ℂ} {F : (Fin n → ℝ) → ℂ}
    (hd : ∀ j, ContDiff ℝ ∞ (Fₙ j)) (hb : ∀ j v, ‖Fₙ j v‖ ≤ C)
    (hl : ∀ v, Tendsto (fun j => Fₙ j v) atTop (𝓝 (F v)))
    {t s : ℝ} (ht : t ∈ Icc (-R) R) (hs : s ∈ Icc (-R) R) :
    Tendsto (fun j => Fourier.orderedIntegral n (Fₙ j) t s) atTop
      (𝓝 (Fourier.orderedIntegral n F t s)) := by
  induction n generalizing t s with
  | zero => exact hl Fin.elim0
  | succ n ih =>
    change Tendsto (fun j => ∫ u in s..t,
      Fourier.orderedIntegral n (fun v => Fₙ j (Fin.cons u v)) u s) atTop
      (𝓝 (∫ u in s..t, Fourier.orderedIntegral n (fun v => F (Fin.cons u v)) u s))
    have hsub : uIoc s t ⊆ Icc (-R) R :=
      uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)
    apply tendsto_intervalIntegral_of_bounded s t (C * (2 * R) ^ n)
    · intro j
      have hd' : ContDiff ℝ ∞ (fun u : ℝ =>
          Fourier.orderedIntegral n (fun v => Fₙ j (Fin.cons u v)) u s) := by
        apply Fourier.contDiff_orderedIntegral n
          ((hd j).comp (Fourier.contDiff_fin_cons n)) contDiff_const contDiff_id
      exact hd'.continuous.aestronglyMeasurable
    · intro j u hu
      exact norm_orderedIntegral_le n hC hR _ (fun v => hb j _) (hsub hu) hs
    · intro u hu
      exact ih (Fₙ := fun j v => Fₙ j (Fin.cons u v)) (F := fun v => F (Fin.cons u v))
        (fun j => (hd j).comp ((Fourier.contDiff_fin_cons n).comp
          (contDiff_const.prodMk contDiff_id)))
        (fun j v => hb j _) (fun v => hl _) (hsub hu) hs

end WaveTurbulence.Incoh
