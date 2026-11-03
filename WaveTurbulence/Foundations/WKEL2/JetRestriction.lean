/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetIntertwining
public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevForget

/-!
# Restriction identities for the completed collision equations
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance restrictionNormedJet (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance restrictionSpaceJet (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance restrictionNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance restrictionSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance restrictionNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance restrictionSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- Successive restrictions agree with direct restriction. -/
theorem weightedSobolevForgetCLM_comp (s : ℝ) {m r q : ℕ} (hrm : r ≤ m) (hqr : q ≤ r)
    (u : WeightedSobolevSpace d s m) :
    weightedSobolevForgetCLM s r q hqr (weightedSobolevForgetCLM s m r hrm u) =
      weightedSobolevForgetCLM s m q (hqr.trans hrm) u := by
  have H := (denseRange_schwartzToWeightedSobolevCLM (d := d) s m).equalizer
    ((weightedSobolevForgetCLM s r q hqr).continuous.comp
      (weightedSobolevForgetCLM s m r hrm).continuous)
    (weightedSobolevForgetCLM s m q (hqr.trans hrm)).continuous
    (funext fun f => by simp only [Function.comp_def, weightedSobolevForgetCLM_schwartz])
  exact congrFun H u

/-- Restriction to the same order is the identity. -/
theorem weightedSobolevForgetCLM_self (s : ℝ) (m : ℕ) (u : WeightedSobolevSpace d s m) :
    weightedSobolevForgetCLM s m m le_rfl u = u := by
  have H := (denseRange_schwartzToWeightedSobolevCLM (d := d) s m).equalizer
    (weightedSobolevForgetCLM s m m le_rfl).continuous continuous_id
    (funext fun f => weightedSobolevForgetCLM_schwartz s le_rfl f)
  exact congrFun H u

/-- Collision fields at every order commute with the canonical restrictions. -/
theorem weightedSobolevForgetCLM_collision (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {m r : ℕ} (hrm : r ≤ m)
    (u v w : WeightedSobolevSpace d s m) :
    weightedSobolevForgetCLM s m r hrm (jetCollisionBanach hd s hs m u v w) =
      jetCollisionBanach hd s hs r (weightedSobolevForgetCLM s m r hrm u)
        (weightedSobolevForgetCLM s m r hrm v) (weightedSobolevForgetCLM s m r hrm w) := by
  apply dense_triple_ext (denseRange_schwartzToWeightedSobolevCLM (d := d) s m)
      (x := u) (y := v) (z := w)
  · fun_prop
  · fun_prop
  · intro f g h
    have H₁ := congrArg (weightedSobolevForgetCLM s m r hrm)
      (jetCollisionBanach_schwartz hd s hs m f g h)
    have H₂ := weightedSobolevForgetCLM_schwartz s hrm
      (WKE.collisionOpSchwartz (by omega) f g h)
    have H₃ := jetCollisionBanach_schwartz hd s hs r f g h
    simpa only [weightedSobolevForgetCLM_schwartz] using (H₁.trans H₂).trans H₃.symm

/-- Differentiable solutions restrict to the collision ODE at every lower order. -/
theorem hasDerivWithinAt_weightedSobolevForget (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {m r : ℕ} (hrm : r ≤ m)
    {u : ℝ → WeightedSobolevSpace d s m} {S : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u (cubicField (jetCollisionBanach hd s hs m) (u t)) S t) :
    HasDerivWithinAt (fun z => weightedSobolevForgetCLM s m r hrm (u z))
      (cubicField (jetCollisionBanach hd s hs r) (weightedSobolevForgetCLM s m r hrm (u t))) S t := by
  have H := (weightedSobolevForgetCLM s m r hrm).hasFDerivAt.comp_hasDerivWithinAt t hu
  simpa only [Function.comp_def, cubicField, weightedSobolevForgetCLM_collision] using H

end WaveTurbulence.WKEL2
