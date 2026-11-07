/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartLocalFactors
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ScalarOriginForms
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9LocalWitnessFromPhase

/-! # Recover local source coordinate witnesses from checked scalar phases -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Conditional phase helper. The phase premise is the exact scalar
specialization of a source resonance identity, not an inverse-matrix bound.
The resulting local geometry is proved from the original garden slots. -/
theorem clLocalWitness_of_scalar_phase (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {X : VineType} (A : FullVineChart G.molecule X U a b)
    (v : GBranch G.tree) (hv : v ∈ U) (ha : v ≠ a) (i : Fin A.indexing.shape.n)
    (c : ChartAffineIndex A → ℤ) (j : ChartAffineIndex A) (hji : j ≠ .inl i)
    (hc : c j = 1 ∨ c j = -1)
    (hphase : ∀ z : ChartAffineIndex A → ℤ,
      omegaNode G (clPhysicalChartLabels R A (0 : Mom 1) (scalarMomentum (z (.inr ())))
        (fun k => scalarMomentum (z (.inl k)))) v =
        2*((z (.inl i)*integerLinearForm c z : ℤ) : ℝ)) : ChartLocalWitness A i := by
  obtain ⟨p,q,t,op,oq,hp,hq,hq',ht,hfactor⟩ := clChart_local_factors hU R A v hv ha
  apply chart_local_witness_of_primitive_phase A p q q t i v hv op oq hp hq hq' ht c j hji hc
  intro z
  have he := hfactor (0 : Mom 1) (scalarMomentum (z (.inr ()))) (fun k => scalarMomentum (z (.inl k)))
  rw [chartOrigin_difference_scalar,chartOrigin_difference_scalar,inner_scalarMomentum] at he
  have hh := (hphase z).symm.trans he
  apply Int.cast_injective (α := ℝ)
  linarith only [hh]

end WaveTurbulence.VineEstS2
