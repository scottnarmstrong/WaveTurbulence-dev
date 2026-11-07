/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepCount2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: measurability, volume and norm facts for the time integral
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  MeasureTheory Set

variable {w d : ℕ}

theorem measurableSet_splicedTimeDomain (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ) :
    MeasurableSet (splicedTimeDomain G layer rt) := by
  unfold splicedTimeDomain
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun v => ?_)
    (MeasurableSet.inter (MeasurableSet.iInter fun v => MeasurableSet.iInter fun u =>
      MeasurableSet.iInter fun _ => ?_) (MeasurableSet.iInter fun v => ?_))
  · exact measurableSet_Icc.preimage (measurable_pi_apply v)
  · exact measurableSet_lt (measurable_pi_apply v) (measurable_pi_apply u)
  · exact measurableSet_lt (measurable_pi_apply v) measurable_const

theorem volume_splicedTimeDomain_le (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ) :
    volume (splicedTimeDomain G layer rt) ≤ 1 := by
  have hsub : splicedTimeDomain G layer rt ⊆
      Set.pi Set.univ (fun v : GBranch G.tree => Set.Icc (layer v : ℝ) (layer v + 1)) := by
    intro t ht v _
    exact ht.1 v
  refine (measure_mono hsub).trans ?_
  rw [volume_pi, Measure.pi_pi]
  simp

theorem norm_phaseProd_le {G : Garden w} (L γ δ : ℝ) (k : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) :
    ‖phaseProd L γ δ G k τ‖ = 1 := by
  unfold phaseProd
  rw [norm_prod]
  exact Finset.prod_eq_one fun b _ => Complex.norm_exp_ofReal_mul_I _

theorem norm_epsDec_le {G : Garden w} (z : GNode G.tree → Fin d → ℤ) : |epsDec G z| ≤ 1 := by
  unfold epsDec
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun b _ => ?_
  unfold epsCoef
  split_ifs <;> simp

end WaveTurbulence.Represents
