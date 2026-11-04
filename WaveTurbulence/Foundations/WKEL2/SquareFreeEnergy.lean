/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SobolevL2ENN
public import WaveTurbulence.Foundations.WKEL2.FiniteProductIntegration
public import WaveTurbulence.Foundations.Analysis.WeightedSobolev

/-!
# Bounding the recursive Sobolev energy by full-space mixed derivative energies
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Enumerate mixed derivatives by whether the head coordinate is differentiated. -/
theorem sum_mixedEnergy_cons {n : ℕ} (f : (Fin (n + 1) → ℝ) → E)
    (t : ℝ) (y : Fin n → ℝ) :
    (∑ b : Fin n → Bool, ENNReal.ofReal
      (‖Analysis.mixedPartial n b (fun z => f (Fin.cons t z)) y‖ ^ 2)) +
    (∑ b : Fin n → Bool, ENNReal.ofReal
      (‖Analysis.mixedPartial n b (fun z => deriv (fun s => f (Fin.cons s z)) t) y‖ ^ 2)) =
    ∑ b : Fin (n + 1) → Bool,
      ENNReal.ofReal (‖Analysis.mixedPartial (n + 1) b f (Fin.cons t y)‖ ^ 2) := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp only [Analysis.mixedPartial, Fin.cons_zero, Fin.tail_cons]
  exact add_comm _ _

/-- The recursive energy is controlled by the sum of the full-space square-free L² energies.
The only analytic side condition here is measurability of the actual derivative energies. -/
theorem wholeSobolevL2Sq_le_mixedEnergy : ∀ (n : ℕ) (f : (Fin n → ℝ) → E),
    (∀ b : Fin n → Bool, Measurable (fun x =>
      ENNReal.ofReal (‖Analysis.mixedPartial n b f x‖ ^ 2))) →
    wholeSobolevL2Sq n f ≤ ∫⁻ x, ∑ b : Fin n → Bool,
      ENNReal.ofReal (‖Analysis.mixedPartial n b f x‖ ^ 2) := by
  intro n
  induction n with
  | zero =>
      intro f _
      rw [Measure.volume_pi_eq_dirac (fun i : Fin 0 => Fin.elim0 i), lintegral_dirac]
      simp only [wholeSobolevL2Sq, Analysis.mixedPartial, Finset.sum_const,
        Finset.card_univ, Fintype.card_unique, one_nsmul, le_refl]
  | succ n ih =>
      intro f hM
      have hmcons (t : ℝ) : Measurable (fun y : Fin n → ℝ => (Fin.cons t y : Fin (n + 1) → ℝ)) := by fun_prop
      have h₀ (t : ℝ) : ∀ b : Fin n → Bool, Measurable (fun y => ENNReal.ofReal
          (‖Analysis.mixedPartial n b (fun z => f (Fin.cons t z)) y‖ ^ 2)) := by
        intro b
        simpa only [Function.comp_def, Analysis.mixedPartial, Fin.cons_zero, Fin.tail_cons,
          Bool.false_eq_true, ↓reduceIte] using (hM (Fin.cons false b)).comp (hmcons t)
      have h₁ (t : ℝ) : ∀ b : Fin n → Bool, Measurable (fun y => ENNReal.ofReal
          (‖Analysis.mixedPartial n b (fun z => deriv (fun s => f (Fin.cons s z)) t) y‖ ^ 2)) := by
        intro b
        simpa only [Function.comp_def, Analysis.mixedPartial, Fin.cons_zero, Fin.tail_cons, ↓reduceIte] using
          (hM (Fin.cons true b)).comp (hmcons t)
      let A := fun (t : ℝ) (y : Fin n → ℝ) => ∑ b : Fin n → Bool, ENNReal.ofReal
        (‖Analysis.mixedPartial n b (fun z => f (Fin.cons t z)) y‖ ^ 2)
      let B := fun (t : ℝ) (y : Fin n → ℝ) => ∑ b : Fin n → Bool, ENNReal.ofReal
        (‖Analysis.mixedPartial n b (fun z => deriv (fun s => f (Fin.cons s z)) t) y‖ ^ 2)
      calc
        wholeSobolevL2Sq (n + 1) f ≤ (∫⁻ t, ∫⁻ y, A t y) + ∫⁻ t, ∫⁻ y, B t y :=
          add_le_add (lintegral_mono fun t => ih _ (h₀ t))
            (lintegral_mono fun t => ih _ (h₁ t))
        _ ≤ ∫⁻ t, (∫⁻ y, A t y) + ∫⁻ y, B t y := le_lintegral_add _ _
        _ ≤ ∫⁻ t, ∫⁻ y, A t y + B t y := lintegral_mono fun t => le_lintegral_add _ _
        _ = ∫⁻ t : ℝ, ∫⁻ y : Fin n → ℝ, ∑ b : Fin (n + 1) → Bool,
            ENNReal.ofReal (‖Analysis.mixedPartial (n + 1) b f (Fin.cons t y)‖ ^ 2) := by
          apply lintegral_congr
          intro t
          apply lintegral_congr
          intro y
          exact sum_mixedEnergy_cons f t y
        _ = _ := (lintegral_fin_cons (Finset.measurable_sum _ fun b _ => hM b)).symm

end WaveTurbulence.WKEL2
