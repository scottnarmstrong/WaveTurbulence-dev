/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPhysicalChartLabels

/-! # Uniform real chart phases are original signed garden resonances -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clPhysicalChart_signedResonance (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {X : VineType} (A : FullVineChart G.molecule X U a b) (g r : Mom d)
    (x : Fin A.indexing.shape.n → Mom d) (i : Fin A.indexing.shape.n) :
    nodeResonance A.indexing ((A.chart g r).symm x).1 g r i =
      (((G.sign (A.indexing.atom i).1.toNode : ℤ) : ℝ)*
        omegaNode G (clPhysicalChartLabels R A g r x) (A.indexing.atom i).1) := by
  let κ := clPhysicalChartLabels R A g r x
  have he := clNodeResonance_eq_signedOmega hU R A.indexing κ (clPhysicalChartLabels_matching R A g r x) i
  have hlabels : (fun e : Bond G.molecule U => Mole.restrictLabels G κ e.1) = ((A.chart g r).symm x).1 :=
    funext (clPhysicalChartLabels_bond R A g r x)
  have h2 : κ (b.child R.positive) = g := clPhysicalChartLabels_boundary hU R A g r x 2
  have h3 : κ (b.child R.negative) = g-r := clPhysicalChartLabels_boundary hU R A g r x 3
  rw [hlabels,h2,h3,sub_sub_cancel] at he
  exact he

end WaveTurbulence.VineEstS2
