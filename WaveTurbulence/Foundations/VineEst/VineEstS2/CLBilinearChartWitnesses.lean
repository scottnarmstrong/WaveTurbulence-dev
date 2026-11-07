/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLocalWitnessFromChartPhase

/-! # Pure rung, joint and core phases recover their local coordinates -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem sum_single_chart_form {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    (j : α) (σ : ℤ) (x : α → Mom d) :
    (∑ k, (((Pi.single j σ : α → ℤ) k : ℤ) : ℝ) • x k) = (σ : ℝ) • x j := by
  classical
  simp [Pi.single_apply]

theorem clLocalWitness_of_bilinear_phase (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {X : VineType} (A : FullVineChart G.molecule X U a b)
    (phase i j : Fin A.indexing.shape.n) (hji : j ≠ i) (σ : ℤˣ)
    (hphase : ∀ (g r : Mom 1) (x : Fin A.indexing.shape.n → Mom 1),
      nodeResonance A.indexing ((A.chart g r).symm x).1 g r phase =
        2*((((σ : ℤ) : ℝ))*inner ℝ (x i) (x j))) : ChartLocalWitness A i := by
  apply clLocalWitness_of_chart_phase hU R A phase i (Pi.single (.inl j) (σ : ℤ)) (.inl j)
    (fun h => hji (Sum.inl.inj h))
  · simp only [Pi.single_eq_same]
    exact Int.isUnit_eq_one_or σ.isUnit
  · intro g r x
    rw [sum_single_chart_form]
    simpa only [Sum.elim_inl,real_inner_smul_right] using hphase g r x

theorem clLocalWitness_of_joint_phase (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {X : VineType} (A : FullVineChart G.molecule X U a b) : ChartLocalWitness A A.indexing.shape.x0 := by
  apply clLocalWitness_of_chart_phase hU R A A.indexing.shape.x0 A.indexing.shape.x0
    (Pi.single (.inr ()) 1) (.inr ()) (by intro h; cases h)
  · norm_num [Pi.single_apply]
  · intro g r x
    rw [sum_single_chart_form]
    simp only [Sum.elim_inr,Int.cast_one,one_smul]
    exact (A.joint_phase 1 g r x).trans (by rw [real_inner_comm])

end WaveTurbulence.VineEstS2
