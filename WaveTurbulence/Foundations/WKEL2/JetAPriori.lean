/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetTameCompleted
public import WaveTurbulence.Foundations.WKEL2.JetGronwallConstant

/-!
# Uniform weighted jet persistence by Gronwall induction

TARGET (schappend10), L2518–L2524. The constant is chosen before the solution
and depends only on d,s,m,T,A,B. Every input to the induction is the proved
completed collision estimate, not an assumed higher-order bound.
-/

public section

noncomputable section

open Set MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance prioriL2AddGroup : AddCommGroup (WeightedL2Space d) :=
  (inferInstance : NormedAddCommGroup (WeightedL2Space d)).toAddCommGroup
local instance prioriL2Module : Module ℝ (WeightedL2Space d) :=
  (inferInstance : NormedSpace ℝ (WeightedL2Space d)).toModule
local instance prioriNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance prioriSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance prioriNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance prioriSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance prioriNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance prioriSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- TARGET (schappend10): a bounded base norm controls every already-existing finite jet solution. -/
theorem exists_jet_solution_uniform_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) (T A B : ℝ)
    (_hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ u : ℝ → WeightedSobolevSpace d s m,
      (∀ t ∈ Icc 0 T, HasDerivWithinAt u (cubicField (jetCollisionBanach hd s hs m) (u t))
        (Icc 0 T) t) → ‖u 0‖ ≤ B →
      (∀ t ∈ Icc 0 T, ‖weightedSobolevToL2CLM s m (u t)‖ ≤ A) →
      ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Q := by
  let C := (exists_jetCollision_tame_completed hd s hs).choose
  have hC : 0 ≤ C := (exists_jetCollision_tame_completed hd s hs).choose_spec.1
  have hb := (exists_jetCollision_tame_completed hd s hs).choose_spec.2
  refine ⟨jetGronwallBound C T A B m, jetGronwallBound_nonneg C T A B hA m,
    fun u hu h₀ hbase => ?_⟩
  have H : ∀ r (hrm : r ≤ m), ∀ t ∈ Icc 0 T,
      ‖weightedSobolevLowerJetCLM s m r hrm (u t)‖ ≤ jetGronwallBound C T A B r := by
    intro r
    induction r with
    | zero =>
        intro hrm t ht
        rw [norm_weightedSobolevLowerJetCLM_zero, jetGronwallBound_zero]
        exact hbase t ht
    | succ r ih =>
        intro hrm t ht
        have hrm₀ : r ≤ m := (Nat.le_succ r).trans hrm
        have hQ := jetGronwallBound_nonneg C T A B hA r
        apply (pi_norm_le_iff_of_nonneg (jetGronwallBound_nonneg C T A B hA (r + 1))).2
        rintro ⟨⟨k, hk⟩, w⟩
        by_cases hkr : k ≤ r
        · have HL := norm_le_pi_norm (weightedSobolevLowerJetCLM s m r hrm₀ (u t))
            (wordJetIndex hkr w)
          exact HL.trans ((ih hrm₀ t ht).trans (jetGronwallBound_le_succ C T A B r))
        · have hkeq : k = r + 1 := by omega
          subst k
          let P := weightedSobolevCoordinateCLM s m (wordJetIndex hrm w)
          change ‖P (u t)‖ ≤ _
          have hPu : ∀ q ∈ Icc 0 T,
              HasDerivWithinAt (fun z => P (u z))
                (P (jetCollisionBanach hd s hs m (u q) (u q) (u q))) (Icc 0 T) q := by
            intro q hq
            simpa only [Function.comp_def, cubicField] using
              P.hasFDerivAt.comp_hasDerivWithinAt q (hu q hq)
          have hP₀ : ‖P (u 0)‖ ≤ B :=
            (norm_weightedSobolevCoordinateCLM_le s m (wordJetIndex hrm w) (u 0)).trans h₀
          have hbound : ∀ q ∈ Icc 0 T,
              ‖P (jetCollisionBanach hd s hs m (u q) (u q) (u q))‖ ≤
                (12 * C * A ^ 2) * ‖P (u q)‖ +
                  4 * 3 ^ (r + 1) * C * jetGronwallBound C T A B r ^ 3 := by
            intro q hq
            apply (hb m r hrm w (u q)).trans
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (norm_nonneg _) (hbase q hq) 2) (by positivity)) (norm_nonneg _)
            · exact mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (norm_nonneg _) (ih hrm₀ q hq) 3) (by positivity)
          have HG := norm_le_gronwallBound_uniform hB (by positivity) (by positivity) hPu hP₀ hbound
          exact (HG t ht).trans (gronwallBound_le_jetGronwallBound C T A B r)
  intro t ht
  simpa only [norm_weightedSobolevLowerJetCLM_self] using H m le_rfl t ht

end WaveTurbulence.WKEL2
