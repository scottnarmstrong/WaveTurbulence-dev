/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootCumulative

/-!
# The actual cumulative kernel in local clocks

TARGET (incohproof17)–(incohproof19): the density vanishes below its root
layers, and translating their lower endpoints gives the actual unit-box
cumulative integral. No extension is substituted for the source kernel.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The literal cumulative kernel is exactly the root-box integral in local clocks. -/
theorem RootCoordinates.cumulativeKernel_eq_localBoxIntegral {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) (t : Fin 2 → ℝ) :
    R.cumulativeKernel L γ δ Q I t =
      ∫ u in Icc (0 : Fin 2 → ℝ) (t - R.baseRootTimes Q), R.localLinkDensity L γ δ Q I u := by
  classical
  let q := R.baseRootTimes Q
  let F := R.linkDensity L γ δ Q I
  have hind : (Iic t).indicator F = (Icc q t).indicator F := by
    funext u
    by_cases hup : u ≤ t
    · by_cases hlo : q ≤ u
      · simp [hup, hlo]
      · have hz : F u = 0 := R.linkDensity_eq_zero_of_notMem_rootBox L γ δ Q hbox (fun h => hlo h.1)
        simp [hup, hlo, hz]
    · simp [hup]
  have hpre : (fun u : Fin 2 → ℝ => u + q) ⁻¹' Icc q t = Icc (0 : Fin 2 → ℝ) (t - q) := by
    ext u
    simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    constructor
    · intro h
      constructor
      · intro a; have ha := h.1 a; linarith
      · intro a; have ha := h.2 a; linarith
    · intro h
      constructor
      · intro a; have ha := h.1 a; linarith
      · intro a; have ha := h.2 a; linarith
  have hmp : MeasurePreserving (fun u : Fin 2 → ℝ => u + q) := measurePreserving_add_right volume q
  have htrans := hmp.setIntegral_preimage_emb (MeasurableEquiv.addRight q).measurableEmbedding F (Icc q t)
  rw [hpre] at htrans
  calc
    _ = ∫ u in Iic t, F u := R.cumulativeKernel_eq_setIntegral hL γ δ Q hI hbox t
    _ = ∫ u in Icc q t, F u := by
      rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Icc, hind]
    _ = _ := htrans.symm

end WaveTurbulence.Incoh
