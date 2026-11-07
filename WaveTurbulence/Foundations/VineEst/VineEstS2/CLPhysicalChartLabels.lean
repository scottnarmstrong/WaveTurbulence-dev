/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFlowConservation
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLResonanceCorrespondence

/-! # Physical chart labels at arbitrary real free coordinates and gap -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- A convenient actual source boundary assignment for testing uniform
chart identities. It satisfies the signed four-boundary momentum relation. -/
noncomputable def chartBoundary (g r : Mom d) (ζ : ℤˣ) : Fin 4 → Mom d :=
  ![(((ζ : ℤ) : ℝ) • r),0,g,g-r]

theorem chartBoundary_gap (g r : Mom d) (ζ : ℤˣ) :
    chartBoundary g r ζ 2-chartBoundary g r ζ 3 = r := by
  change g-(g-r) = r
  abel

theorem chartBoundary_conservation (g r : Mom d) (ζ : ℤˣ) :
    (((ζ : ℤ) : ℝ) • (chartBoundary g r ζ 0-chartBoundary g r ζ 1)) =
      chartBoundary g r ζ 2-chartBoundary g r ζ 3 := by
  rw [chartBoundary_gap]
  change (((ζ : ℤ) : ℝ) • ((((ζ : ℤ) : ℝ) • r)-0)) = r
  rw [sub_zero,smul_smul]
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> simp

noncomputable def clPhysicalChartLabels (R : CLRegionData G U a b) {X : VineType}
    (A : FullVineChart G.molecule X U a b) (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) :
    GNode G.tree → Mom d :=
  clRebuildLabels R ((A.chart g r).symm x).1 (chartBoundary g r (G.sign a.toNode))

theorem clPhysicalChartLabels_matching (R : CLRegionData G U a b) {X : VineType}
    (A : FullVineChart G.molecule X U a b) (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) :
    ∀ ℓ, Mole.IsInternalLeaf G U ℓ → clPhysicalChartLabels R A g r x ℓ.toNode =
      clPhysicalChartLabels R A g r x (G.pair ℓ).toNode :=
  clRebuildLabels_matching R _ _

theorem clPhysicalChartLabels_bond (R : CLRegionData G U a b) {X : VineType}
    (A : FullVineChart G.molecule X U a b) (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d)
    (e : Bond G.molecule U) :
    Mole.restrictLabels G (clPhysicalChartLabels R A g r x) e.1 = ((A.chart g r).symm x).1 e :=
  clRebuildLabels_bond R _ _ e

theorem clPhysicalChartLabels_boundary (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) {X : VineType}
    (A : FullVineChart G.molecule X U a b) (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) (j : Fin 4) :
    clPhysicalChartLabels R A g r x (clBoundaryNodes R j) = chartBoundary g r (G.sign a.toNode) j :=
  clRebuildLabels_boundary hU R _ _ j

theorem clPhysicalChartLabels_conservation (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) {X : VineType}
    (A : FullVineChart G.molecule X U a b) (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) :
    ∀ v ∈ U, clPhysicalChartLabels R A g r x v.toNode =
      clPhysicalChartLabels R A g r x (v.child 0)-clPhysicalChartLabels R A g r x (v.child 1)+
        clPhysicalChartLabels R A g r x (v.child 2) := by
  let k := (A.chart g r).symm x
  let β := chartBoundary g r (G.sign a.toNode)
  let k' : FlowFiber G.molecule U a b (Mom d) (β 2-β 3) :=
    ⟨k.1,by simpa only [β,chartBoundary_gap] using k.2⟩
  have hk' : k'.1 = k.1 := rfl
  clear_value k'
  have hc := clRebuildLabels_conservation hU R β (chartBoundary_conservation g r _) k'
  have he (z : GNode G.tree) : clPhysicalChartLabels R A g r x z = clRebuildLabels R k'.1 β z := by
    rw [hk']
    rfl
  intro v hv
  calc
    _ = clRebuildLabels R k'.1 β v.toNode := he _
    _ = _ := hc v hv
    _ = _ := by rw [← he,← he,← he]

end WaveTurbulence.VineEstS2
