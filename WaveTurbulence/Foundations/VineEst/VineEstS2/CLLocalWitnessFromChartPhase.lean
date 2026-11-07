/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLocalWitnessFromScalarPhase
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPhysicalChartResonances

/-! # Existing uniform M9 phase identities prove local coordinate geometry -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Conditional phase helper to be instantiated by the existing M9 joint,
rung and core phase fields. Only one independent unit coefficient in the
other factor is needed, including the F79 nonlinear core. -/
theorem clLocalWitness_of_chart_phase (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {X : VineType} (A : FullVineChart G.molecule X U a b)
    (phase i : Fin A.indexing.shape.n) (c : ChartAffineIndex A → ℤ)
    (j : ChartAffineIndex A) (hji : j ≠ .inl i) (hc : c j = 1 ∨ c j = -1)
    (hphase : ∀ (g r : Mom 1) (x : Fin A.indexing.shape.n → Mom 1),
      nodeResonance A.indexing ((A.chart g r).symm x).1 g r phase =
        2*inner ℝ (x i) (∑ k : ChartAffineIndex A, (c k : ℝ) • Sum.elim x (fun _ => r) k)) :
    ChartLocalWitness A i := by
  let v := (A.indexing.atom phase).1
  have hv := Finset.mem_erase.mp (A.indexing.atom phase).2
  have hscalar (z : ChartAffineIndex A → ℤ) :
      (((G.sign v.toNode : ℤ) : ℝ)*omegaNode G
        (clPhysicalChartLabels R A (0 : Mom 1) (scalarMomentum (z (.inr ())))
          (fun k => scalarMomentum (z (.inl k)))) v) =
        2*((z (.inl i)*integerLinearForm c z : ℤ) : ℝ) := by
    have he := (clPhysicalChart_signedResonance hU R A (0 : Mom 1) (scalarMomentum (z (.inr ())))
      (fun k => scalarMomentum (z (.inl k))) phase).symm.trans
        (hphase 0 (scalarMomentum (z (.inr ()))) (fun k => scalarMomentum (z (.inl k))))
    rw [scalarAffineForm,inner_scalarMomentum] at he
    exact he
  rcases Int.units_eq_one_or (G.sign v.toNode) with hs | hs
  · apply clLocalWitness_of_scalar_phase hU R A v hv.2 hv.1 i c j hji hc
    intro z
    simpa only [hs,Units.val_one,Int.cast_one,one_mul] using hscalar z
  · have hc' : (-c j) = 1 ∨ (-c j) = -1 := by
      rcases hc with hc | hc <;> simp only [hc] <;> norm_num
    apply clLocalWitness_of_scalar_phase hU R A v hv.2 hv.1 i (fun k => -c k) j hji hc'
    intro z
    have hn : integerLinearForm (fun k => -c k) z = -integerLinearForm c z := by
      simp only [integerLinearForm,neg_mul,Finset.sum_neg_distrib]
    rw [hn,mul_neg,Int.cast_neg]
    have he := hscalar z
    simp only [hs,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul] at he
    linarith only [he]

end WaveTurbulence.VineEstS2
