/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootDensityLp
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Local clocks for the actual root density

TARGET (incohproof17)–(incohproof20): subtract the integer root layers so
all root clocks lie in `[0,1]`. This is an actual translation of the marginal;
it preserves physical Lᵖ norms and puts its support in the unit box.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The actual root density in clocks measured from their integer layers. -/
@[expose] def RootCoordinates.localLinkDensity {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin r → ℝ) : ℂ :=
  R.linkDensity L γ δ Q I (t + R.baseRootTimes Q)

/-- Translation preserves integrability of the actual root density. -/
theorem RootCoordinates.integrable_localLinkDensity {d n r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    Integrable (R.localLinkDensity L γ δ Q I) :=
  (R.integrable_linkDensity hL γ δ Q hI hbox).comp_add_right (R.baseRootTimes Q)

/-- Every physical Lᵖ norm is unchanged by the local-clock translation. -/
theorem RootCoordinates.eLpNorm_localLinkDensity {d n r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (p : ℝ≥0∞) :
    eLpNorm (R.localLinkDensity L γ δ Q I) p = eLpNorm (R.linkDensity L γ δ Q I) p := by
  have hmp : MeasurePreserving (fun t : Fin r → ℝ => t + R.baseRootTimes Q) :=
    measurePreserving_add_right volume (R.baseRootTimes Q)
  exact eLpNorm_comp_measurePreserving
    (R.integrable_linkDensity hL γ δ Q hI hbox).aestronglyMeasurable hmp

/-- An actual marginal vanishes whenever one selected time leaves its own source interval. -/
theorem RootCoordinates.linkDensity_eq_zero_of_notMem_rootBox {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) {I : Set (Fin n → Fin 2 → ℝ)}
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {t : Fin r → ℝ} (ht : t ∉ R.rootBox Q) :
    R.linkDensity L γ δ Q I t = 0 := by
  change (∫ u : Fin R.restCount → ℝ, normalizedLinkIntegrand L γ δ Q I (R.equiv.symm (t, u))) = 0
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro u
  dsimp only
  have hnot : R.equiv.symm (t, u) ∉ I := by
    intro h
    exact ht ((R.equiv_symm_mem_linkBoxes Q t u).mp (hbox h)).1
  rw [normalizedLinkIntegrand, Set.indicator_of_notMem (s := I) hnot, mul_zero]
  simp only [Pi.zero_apply]

end WaveTurbulence.Incoh
