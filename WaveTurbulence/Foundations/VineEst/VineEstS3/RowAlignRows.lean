/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Momenta

/-! # Row alignment, part 3: the rows of a vine block carry the branches and anchor pairs of that vine

`vineOf_assemblyBranchOf`: the branch carried by a row of block `i` is an interior atom of the vine `i`.
`assemblyPairOf_anchor`: the anchor pair of the vine `i` is carried by a row of block `i`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist VineParamContract TTree RegRed
open WaveTurbulence.Reg.Skeleton
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)

theorem assemblyBranchBij_assemblyBranchOf (v : (assemblyShape hM9 B).VIdx) :
    assemblyBranchBij hM9 B (assemblyBranchOf hM9 B v) = v := by
  have h : (assemblyIntOrder hM9 B).e (assemblyBranchOf hM9 B v) = (assemblyRowEquiv hM9 B).symm v := by
    simp [assemblyBranchOf]
  have h2 : (assemblyRowEquiv hM9 B) ((assemblyIntOrder hM9 B).e (assemblyBranchOf hM9 B v)) = v := by
    rw [h]; simp
  simpa [assemblyIntOrder] using h2

variable (hG : G.IsPlain)

theorem assemblyPairBij_assemblyPairOf (v : (assemblyShape hM9 B).VIdx) :
    assemblyPairBij hG B hM9 (assemblyPairOf hM9 B hG v) = v := by
  have h : (assemblyPairOrder hG B hM9) (assemblyPairOf hM9 B hG v) = (assemblyRowEquiv hM9 B).symm v := by
    simp [assemblyPairOf]
  have h2 : (assemblyRowEquiv hM9 B) ((assemblyPairOrder hG B hM9) (assemblyPairOf hM9 B hG v)) = v := by
    rw [h]; simp
  simpa [assemblyPairOrder] using h2

/-- The anchor pair of the vine `i` is carried by a row of block `i`. -/
theorem assemblyPairOf_anchor (i : Fin n) (p : ↥(clRegionalPairs hG U)) (hp : vineAnchor hG B i = some p) :
    ∃ v : (assemblyShape hM9 B).VIdx, v.1 = i ∧ assemblyPairOf hM9 B hG v = p := by
  refine ⟨assemblyPairBij hG B hM9 p, assemblyPairBij_anchor hG B hM9 i p hp, ?_⟩
  apply (assemblyPairBij hG B hM9).injective
  rw [assemblyPairBij_assemblyPairOf]

end WaveTurbulence.VineEstS3
