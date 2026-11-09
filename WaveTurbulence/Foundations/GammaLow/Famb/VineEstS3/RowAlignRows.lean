/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Momenta
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlignRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Momenta
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlignRows` (sha256 a87edfabb6a3116a…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Row alignment, part 3: the rows of a vine block carry the branches and anchor pairs of that vine

`vineOf_assemblyBranchOf`: the branch carried by a row of block `i` is an interior atom of the vine `i`.
`assemblyPairOf_anchor`: the anchor pair of the vine `i` is carried by a row of block `i`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist VineParamContract TTree RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.Reg.Skeleton
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)

theorem assemblyBranchBij_assemblyBranchOfΓ (v : (assemblyShapeΓ hM9 B).VIdx) :
    assemblyBranchBijΓ hM9 B (assemblyBranchOfΓ hM9 B v) = v := by
  have h : (assemblyIntOrderΓ hM9 B).e (assemblyBranchOfΓ hM9 B v) = (assemblyRowEquivΓ hM9 B).symm v := by
    simp [assemblyBranchOfΓ]
  have h2 : (assemblyRowEquivΓ hM9 B) ((assemblyIntOrderΓ hM9 B).e (assemblyBranchOfΓ hM9 B v)) = v := by
    rw [h]; simp
  simpa [assemblyIntOrderΓ] using h2

variable (hG : G.IsPlain)

theorem assemblyPairBij_assemblyPairOfΓ (v : (assemblyShapeΓ hM9 B).VIdx) :
    assemblyPairBijΓ hG B hM9 (assemblyPairOfΓ hM9 B hG v) = v := by
  have h : (assemblyPairOrderΓ hG B hM9) (assemblyPairOfΓ hM9 B hG v) = (assemblyRowEquivΓ hM9 B).symm v := by
    simp [assemblyPairOfΓ]
  have h2 : (assemblyRowEquivΓ hM9 B) ((assemblyPairOrderΓ hG B hM9) (assemblyPairOfΓ hM9 B hG v)) = v := by
    rw [h]; simp
  simpa [assemblyPairOrderΓ] using h2

/-- The anchor pair of the vine `i` is carried by a row of block `i`. -/
theorem assemblyPairOf_anchorΓ (i : Fin n) (p : ↥(clRegionalPairs hG U)) (hp : vineAnchorΓ hG B i = some p) :
    ∃ v : (assemblyShapeΓ hM9 B).VIdx, v.1 = i ∧ assemblyPairOfΓ hM9 B hG v = p := by
  refine ⟨assemblyPairBijΓ hG B hM9 p, assemblyPairBij_anchorΓ hG B hM9 i p hp, ?_⟩
  apply (assemblyPairBijΓ hG B hM9).injective
  rw [assemblyPairBij_assemblyPairOfΓ]

end WaveTurbulence.GammaLow.Famb.VineEstS3
