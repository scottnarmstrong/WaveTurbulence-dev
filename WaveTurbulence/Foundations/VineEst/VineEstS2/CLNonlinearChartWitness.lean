/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBilinearChartWitnesses

/-! # The F79 nonlinear core also supplies its local coordinate witness -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Primitive factor recovery uses the independent unit coefficient of
x_j in x_j+x_k-x_i; it requires no positive-core or linear-core replacement. -/
theorem clLocalWitness_of_nonlinear_phase (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {X : VineType} (A : FullVineChart G.molecule X U a b)
    (phase i j k : Fin A.indexing.shape.n) (hji : j ≠ i) (hkj : k ≠ j) (σ : ℤˣ)
    (hphase : ∀ (g r : Mom 1) (x : Fin A.indexing.shape.n → Mom 1),
      nodeResonance A.indexing ((A.chart g r).symm x).1 g r phase =
        2*((((σ : ℤ) : ℝ))*inner ℝ (x i) (x j+x k-x i))) : ChartLocalWitness A i := by
  classical
  let c : ChartAffineIndex A → ℤ := Pi.single (.inl j) (σ : ℤ)+Pi.single (.inl k) (σ : ℤ)-Pi.single (.inl i) (σ : ℤ)
  apply clLocalWitness_of_chart_phase hU R A phase i c (.inl j) (fun h => hji (Sum.inl.inj h))
  · have hc : c (.inl j) = (σ : ℤ) := by simp [c,Pi.single_apply,hji,Ne.symm hji,hkj,Ne.symm hkj]
    rw [hc]
    exact Int.isUnit_eq_one_or σ.isUnit
  · intro g r x
    simp only [c,Pi.add_apply,Pi.sub_apply,Int.cast_add,Int.cast_sub,add_smul,sub_smul,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [sum_single_chart_form,sum_single_chart_form,sum_single_chart_form]
    simpa only [Sum.elim_inl,← smul_add,← smul_sub,real_inner_smul_right] using hphase g r x

end WaveTurbulence.VineEstS2
