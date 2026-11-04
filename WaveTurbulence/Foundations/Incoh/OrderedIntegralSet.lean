/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.OrderedClockDomain
public import WaveTurbulence.Foundations.Incoh.FiniteClockFubini

/-!
# Ordered integrals are literal ordered-domain integrals

Bounded measurable amplitudes suffice. This identifies the integer-endpoint
inclusion/exclusion formulas with the actual source time domains.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- A non-reversed ordered integral equals integration over its literal clock simplex. -/
theorem orderedIntegral_eq_setIntegral (n : ℕ) {F : (Fin n → ℝ) → ℂ}
    (hF : StronglyMeasurable F) {C : ℝ} (hb : ∀ v, ‖F v‖ ≤ C)
    {t s : ℝ} (hst : s ≤ t) :
    Fourier.orderedIntegral n F t s = ∫ v in orderedClockDomain n t s, F v := by
  induction n generalizing t s with
  | zero =>
    simp only [Fourier.orderedIntegral, orderedClockDomain, Antitone, Fin.forall_fin_zero,
      and_self, Set.ofPred_true, setIntegral_univ]
    calc
      F Fin.elim0 = ∫ _v : Fin 0 → ℝ, F Fin.elim0 := by
        rw [Measure.volume_pi_eq_dirac (x := (Fin.elim0 : Fin 0 → ℝ)), integral_dirac]
      _ = ∫ v, F v := integral_congr_ae (Filter.Eventually.of_forall
        (fun v => congrArg F (Subsingleton.elim _ _)))
  | succ n ih =>
    have hD := measurableSet_orderedClockDomain (n + 1) t s
    have hi := (integrableOn_orderedClockDomain hF hb t s).integrable_indicator hD
    have hp := integral_eq_integral_finCons hi
    rw [integral_indicator hD] at hp
    have he (x : ℝ) : (∫ v, (orderedClockDomain (n + 1) t s).indicator F (Fin.cons x v)) =
        (Icc s t).indicator (fun x => ∫ v in orderedClockDomain n x s, F (Fin.cons x v)) x := by
      by_cases hx : x ∈ Icc s t
      · rw [indicator_of_mem hx, ← integral_indicator (measurableSet_orderedClockDomain n x s)]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun v => by
          dsimp only
          by_cases hv : v ∈ orderedClockDomain n x s
          · have hcons := (cons_mem_orderedClockDomain_iff x v t s).mpr ⟨hx, hv⟩
            rw [indicator_of_mem hcons, indicator_of_mem hv]
          · have hcons : Fin.cons x v ∉ orderedClockDomain (n + 1) t s :=
              fun h => hv ((cons_mem_orderedClockDomain_iff x v t s).mp h).2
            rw [indicator_of_notMem hcons, indicator_of_notMem hv])
      · rw [indicator_of_notMem hx]
        apply integral_eq_zero_of_ae
        exact Filter.Eventually.of_forall (fun v => by
          dsimp only [Pi.zero_apply]
          have hcons : Fin.cons x v ∉ orderedClockDomain (n + 1) t s :=
            fun h => hx ((cons_mem_orderedClockDomain_iff x v t s).mp h).1
          rw [indicator_of_notMem hcons])
    simp_rw [he] at hp
    rw [integral_indicator measurableSet_Icc] at hp
    rw [Fourier.orderedIntegral, intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc, hp]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    have hm : Measurable (fun v : Fin n → ℝ => (Fin.cons x v : Fin (n + 1) → ℝ)) :=
      (Fourier.contDiff_fin_cons n).continuous.measurable.comp (measurable_const.prodMk measurable_id)
    exact ih (F := fun v : Fin n → ℝ => F (Fin.cons x v)) (hF.comp_measurable hm) (fun v => hb _) hx.1

end WaveTurbulence.Incoh
