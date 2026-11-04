/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.WideCoupleExtensionAgreement

/-!
# The literal degenerate couple kernel with one external root clock

TARGET L1049, audit P-1. Either selected clock is the genuine root; the
other is an auxiliary branching clock, not a root of the trivial tree.
Integrating its full source layer removes its external constraint.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The sole genuine external root constraint of the degenerate couple. -/
@[expose] def RootCoordinates.oneClockCut {n : ℕ} (R : RootCoordinates n) (a : Fin 2) (t : ℝ) :
    Set (Fin n → Fin 2 → ℝ) := {w | (R.equiv w).1 a ≤ t}

/-- Literal source kernel, independent of the other external clock. -/
@[expose] def RootCoordinates.oneClockKernel {d n : ℕ} (R : RootCoordinates n) (a : Fin 2)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) : ℂ := normalizedLinkIntegral L γ δ Q (I ∩ R.oneClockCut a (t a))

/-- Complete the auxiliary layer integration; no second source root is assumed. -/
theorem RootCoordinates.cumulativeKernel_eq_oneClockKernel {d n : ℕ} (R : RootCoordinates n)
    (a : Fin 2) (L γ δ : ℝ) (Q : Fin n → LayerLink d) {I : Set (Fin n → Fin 2 → ℝ)}
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {t : Fin 2 → ℝ}
    (ht : ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ t j) :
    R.cumulativeKernel L γ δ Q I t = R.oneClockKernel a L γ δ Q I t := by
  have hset : I ∩ R.rootCut t = I ∩ R.oneClockCut a (t a) := by
    ext w
    constructor
    · rintro ⟨hi, hc⟩
      exact ⟨hi, hc.1 a⟩
    · rintro ⟨hi, hc⟩
      refine ⟨hi, ?_⟩
      have hb : (R.equiv w).1 ∈ R.rootBox Q := by
        apply ((R.equiv_symm_mem_linkBoxes Q (R.equiv w).1 (R.equiv w).2).mp ?_).1
        simpa only [Prod.eta, MeasurableEquiv.symm_apply_apply] using hbox hi
      change (R.equiv w).1 ≤ t ∧ (R.equiv w).2 ∈ univ
      refine ⟨fun j => ?_, mem_univ _⟩
      by_cases hj : j = a
      · subst j
        exact hc
      · exact (hb.2 j).trans (ht j hj)
  rw [cumulativeKernel, oneClockKernel, hset]

/-- Unit external box; the passive base is independent of every actual source clock. -/
@[expose] def RootCoordinates.oneClockBox {d n : ℕ} (R : RootCoordinates n)
    (a : Fin 2) (Q : Fin n → LayerLink d) (b : ℝ) : Set (Fin 2 → ℝ) :=
  Icc (fun j => if j = a then R.baseRootTimes Q j else b)
    (fun j => (if j = a then R.baseRootTimes Q j else b) + 1)

/-- Place the passive upper limit above its complete actual source layer. -/
@[expose] def RootCoordinates.oneClockShift {d n : ℕ} (R : RootCoordinates n)
    (a : Fin 2) (Q : Fin n → LayerLink d) (b : ℝ) : Fin 2 → ℝ :=
  fun j => if j = a then 0 else R.baseRootTimes Q j - b + 1

/-- The actual wider canonical extension translated in the passive external clock. -/
@[expose] def RootCoordinates.oneClockExtension {d n : ℕ} (R : RootCoordinates n) (a : Fin 2)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (b : ℝ)
    (t : Fin 2 → ℝ) : ℂ :=
  R.coupleExtension wideRootCutoff L γ δ Q I (t + R.oneClockShift a Q b)

/-- The canonical extension agrees pointwise for either choice of the genuine root clock. -/
theorem RootCoordinates.oneClockExtension_agrees {d n : ℕ} (R : RootCoordinates n) (a : Fin 2)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (b : ℝ) {t : Fin 2 → ℝ}
    (ht : t ∈ R.oneClockBox a Q b) :
    R.oneClockExtension a L γ δ Q I b t = R.oneClockKernel a L γ δ Q I t := by
  have hl (j : Fin 2) := ht.1 j
  have hu (j : Fin 2) := ht.2 j
  have hτ : t + R.oneClockShift a Q b - R.baseRootTimes Q ∈ Icc (0 : Fin 2 → ℝ) 2 := by
    constructor <;> intro j
    all_goals
      have hl' := hl j
      have hu' := hu j
      by_cases hj : j = a <;>
        simp only [oneClockShift, hj, ite_true, ite_false, Pi.add_apply, Pi.sub_apply,
          Pi.ofNat_apply] at hl' hu' ⊢ <;> linarith
  have haux (j : Fin 2) (hj : j ≠ a) :
      R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j := by
    have hh := hl j
    simp only [hj, ite_false] at hh
    simp only [Pi.add_apply, oneClockShift, hj, ite_false]
    linarith only [hh]
  rw [oneClockExtension, R.coupleExtension_wide_agrees hL γ δ Q hI hbox hτ,
    R.cumulativeKernel_eq_oneClockKernel a L γ δ Q hbox haux]
  unfold oneClockKernel
  simp only [Pi.add_apply, oneClockShift, ite_true, add_zero]

end WaveTurbulence.Incoh
