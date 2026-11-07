/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLocalReconstruction

/-! # Exact regional lattice-decoration equivalence with the M9 flow fiber -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clLocalIntegerFlowFiber_val {L : ℝ} (hL : L ≠ 0)
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (base : Mom d) (boundary : Fin 4 → Mom d) (κ : CLLocalDecoration R L base boundary) :
    (clLocalIntegerFlowFiber hL hU R base boundary κ).1 = clLocalBondLabels R L base boundary κ := by
  dsimp only [clLocalIntegerFlowFiber,clIntegerFlowFiber]
  rfl

noncomputable def clLocalToFlow {L : ℝ} (hL : L ≠ 0)
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (κ : CLLocalDecoration R L base (fun j => base+latticePoint L (β j))) :
    FlowFiber G.molecule U a b (Fin d → ℤ) (β 2-β 3) := by
  let Q := clLocalIntegerFlowFiber hL hU R base (fun j => base+latticePoint L (β j)) κ
  have hval : Q.1 = clLocalBondLabels R L base (fun j => base+latticePoint L (β j)) κ :=
    clLocalIntegerFlowFiber_val hL hU R base _ κ
  clear_value Q
  have h2 : clExtendIndices R κ.1 (b.child R.positive) = β 2 := clLocal_boundaryIndex hL R base β κ 2
  have h3 : clExtendIndices R κ.1 (b.child R.negative) = β 3 := clLocal_boundaryIndex hL R base β κ 3
  refine ⟨clLocalBondLabels R L base (fun j => base+latticePoint L (β j)) κ,?_,?_,?_⟩
  · rw [← hval,Q.2.1,h2,h3]
  · rw [← hval,Q.2.2.1,h2,h3]
  · intro v hv ha hb
    rw [← hval]
    exact Q.2.2.2 v hv ha hb

theorem clLocalToFlow_val {L : ℝ} (hL : L ≠ 0)
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (κ : CLLocalDecoration R L base (fun j => base+latticePoint L (β j))) :
    (clLocalToFlow hL hU R base β κ).1 =
      clLocalBondLabels R L base (fun j => base+latticePoint L (β j)) κ := by
  dsimp only [clLocalToFlow]

/-- Actual source labels, all four boundary constraints and both inverse
identities. No hypothetical decoration bijection or independent labels are
assumed. The signed boundary premise is exactly the source momentum condition. -/
noncomputable def clLocalFlowEquiv {L : ℝ} (hL : L ≠ 0)
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) :
    CLLocalDecoration R L base (fun j => base+latticePoint L (β j)) ≃
      FlowFiber G.molecule U a b (Fin d → ℤ) (β 2-β 3) where
  toFun := clLocalToFlow hL hU R base β
  invFun := clLocalFromFlow hU R L base β hβ
  left_inv κ := by
    apply clLocalBondLabels_injective hL hU R base (fun j => base+latticePoint L (β j))
    exact (clLocalFromFlow_bondLabels hU R L base β hβ _).trans
      (clLocalToFlow_val hL hU R base β κ)
  right_inv k := by
    apply Subtype.ext
    exact (clLocalToFlow_val hL hU R base β _).trans
      (clLocalFromFlow_bondLabels hU R L base β hβ k)

end WaveTurbulence.VineEstS2
