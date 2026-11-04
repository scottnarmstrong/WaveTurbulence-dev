/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LocalRootDensity
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The literal couple kernel as the cumulative root marginal

TARGET (incohproof17). The external root clocks impose actual upper
constraints on the selected internal times. Measure preservation and
Fubini identify that source integral with the cumulative root density.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Integrating a root marginal over any root set recovers the full source integral over its preimage. -/
theorem RootCoordinates.setIntegral_density {n r : ℕ} (R : RootCoordinates n r)
    {F : (Fin n → Fin 2 → ℝ) → ℂ} (hF : Integrable F) (B : Set (Fin r → ℝ)) :
    (∫ t in B, R.density F t) = ∫ u in R.equiv ⁻¹' (B ×ˢ univ), F u := by
  have hG : Integrable (fun z => F (R.equiv.symm z)) :=
    (R.measurePreserving.symm.integrable_comp_emb R.equiv.symm.measurableEmbedding).mpr hF
  have hs := R.measurePreserving.setIntegral_preimage_emb R.equiv.measurableEmbedding
    (fun z => F (R.equiv.symm z)) (B ×ˢ univ)
  simp only [MeasurableEquiv.symm_apply_apply] at hs
  have hp := setIntegral_prod (fun z => F (R.equiv.symm z))
    (s := B) (t := univ) hG.integrableOn
  simp only [setIntegral_univ] at hp
  exact hp.symm.trans hs.symm

/-- The source root constraints at the two external clocks. -/
@[expose] def RootCoordinates.rootCut {n : ℕ} (R : RootCoordinates n) (t : Fin 2 → ℝ) :
    Set (Fin n → Fin 2 → ℝ) := R.equiv ⁻¹' (Iic t ×ˢ univ)

theorem RootCoordinates.measurableSet_rootCut {n : ℕ} (R : RootCoordinates n) (t : Fin 2 → ℝ) :
    MeasurableSet (R.rootCut t) := (measurableSet_Iic.prod MeasurableSet.univ).preimage R.equiv.measurable

/-- The localized source kernel with its literal external root-time constraints. -/
@[expose] def RootCoordinates.cumulativeKernel {d n : ℕ} (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) (t : Fin 2 → ℝ) : ℂ :=
  normalizedLinkIntegral L γ δ Q (I ∩ R.rootCut t)

/-- TARGET (incohproof17): the literal constrained kernel is the cumulative actual root density. -/
theorem RootCoordinates.cumulativeKernel_eq_setIntegral {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (t : Fin 2 → ℝ) :
    R.cumulativeKernel L γ δ Q I t = ∫ u in Iic t, R.linkDensity L γ δ Q I u := by
  have hcut := R.measurableSet_rootCut t
  have hF := integrable_normalizedLinkIntegrand hL γ δ Q hI hbox
  have heq : normalizedLinkIntegrand L γ δ Q (I ∩ R.rootCut t) =
      (R.rootCut t).indicator (normalizedLinkIntegrand L γ δ Q I) := by
    funext u
    by_cases hi : u ∈ I <;> by_cases hc : u ∈ R.rootCut t <;>
      simp [normalizedLinkIntegrand, hi, hc]
  rw [cumulativeKernel, ← integral_normalizedLinkIntegrand L γ δ Q (hI.inter hcut), heq,
    integral_indicator hcut]
  exact (R.setIntegral_density hF (Iic t)).symm

end WaveTurbulence.Incoh
