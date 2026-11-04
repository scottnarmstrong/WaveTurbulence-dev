/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ProductLinkMixture
public import WaveTurbulence.Foundations.Incoh.RootBoxes

/-!
# Removing dummy selected clocks from the literal mixture amplitude

The selected coefficients have no temporal dependence. Untouched link
factors depend only on remaining clocks, by the coordinate permutation.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Literal selected coefficients and untouched link factors at the remaining clocks. -/
@[expose] def RootCoordinates.remainingMixtureFactor {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) (u : Fin R.restCount → ℝ) : ℂ :=
  ∏ i, if i ∈ R.rootLinks then linkPhaseCoefficient L (Q i) (p i)
    else linkTimeFactor L γ δ (Q i) (R.equiv.symm (0, u) i)

/-- Every clock cutoff remains present after factoring the selected coefficients. -/
theorem RootCoordinates.prod_linkMixtureFactor_eq_indicator {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (v : Fin r → ℝ) (u : Fin R.restCount → ℝ) :
    (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks))
      (p i, R.equiv.symm (v, u) i)) =
      (univ.pi (fun i => linkBox (Q i))).indicator
        (fun _ => R.remainingMixtureFactor L γ δ Q p u) (R.equiv.symm (v, u)) := by
  classical
  by_cases hbox : R.equiv.symm (v, u) ∈ univ.pi (fun i => linkBox (Q i))
  · rw [indicator_of_mem hbox]
    unfold remainingMixtureFactor
    apply Finset.prod_congr rfl
    intro i _
    rw [linkMixtureFactor, indicator_of_mem (hbox i (mem_univ i))]
    by_cases hi : i ∈ R.rootLinks
    · simp only [hi, decide_true, ite_true]
    · simp only [hi, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [R.equiv_symm_eq_of_notMem_rootLinks v 0 u i hi]
  · rw [indicator_of_notMem hbox]
    have hi : ∃ i, R.equiv.symm (v, u) i ∉ linkBox (Q i) := by
      simpa only [mem_pi, mem_univ, forall_const, not_forall] using hbox
    obtain ⟨i, hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact indicator_of_notMem hi _

/-- The selected dummy clocks contribute precisely their unit layer-box indicator. -/
theorem RootCoordinates.prod_linkMixtureFactor_eq_split {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (v : Fin r → ℝ) (u : Fin R.restCount → ℝ) :
    (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks))
      (p i, R.equiv.symm (v, u) i)) =
      (R.rootBox Q).indicator (fun _ =>
        (R.restBox Q).indicator (fun _ => R.remainingMixtureFactor L γ δ Q p u) u) v := by
  rw [R.prod_linkMixtureFactor_eq_indicator]
  by_cases hv : v ∈ R.rootBox Q <;> by_cases hu : u ∈ R.restBox Q <;>
    simp [R.equiv_symm_mem_linkBoxes, hv, hu]

/-- Integrating the dummy selected clocks costs exactly their unit box volume. -/
theorem RootCoordinates.integral_dummyMixtureFactor {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) (u : Fin R.restCount → ℝ) :
    (∫ v : Fin r → ℝ, ∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks))
      (p i, R.equiv.symm (v, u) i)) =
      (R.restBox Q).indicator (fun _ => R.remainingMixtureFactor L γ δ Q p u) u := by
  simp_rw [R.prod_linkMixtureFactor_eq_split L γ δ Q p]
  rw [integral_indicator (show MeasurableSet (R.rootBox Q) from measurableSet_Icc), setIntegral_const, measureReal_def,
    R.volume_rootBox Q, ENNReal.toReal_one, one_smul]

end WaveTurbulence.Incoh
