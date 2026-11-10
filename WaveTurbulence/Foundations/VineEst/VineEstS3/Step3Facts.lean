/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At

/-! # Step 3: bookkeeping facts (orders, cardinalities, `maxPar`) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng VineParamContract TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem card_U_eq (B : CLChainAssembly G R n) : Fintype.card ↥U = clLocalOrder1 R + 1 := by
  rw [Fintype.card_coe]
  have ha : a ∈ U := B.isBlock.2.1
  unfold clLocalOrder1 clInteriorBranches
  exact (Finset.card_erase_add_one ha).symm

theorem M_pos (hM9 : VINEPARAM) (B : CLChainAssembly G R n) : 1 ≤ clLocalOrder1 R := by
  have hI := assemblyShape_I_pos hM9 B
  have : 0 < Fintype.card (assemblyShape hM9 B).VIdx :=
    Fintype.card_pos_iff.2 ⟨⟨⟨0, hI⟩, ⟨0, by unfold SumintShape.n; split_ifs <;> omega⟩⟩⟩
  rw [Sumint.card_vector_index, assemblyShape_M] at this
  exact this

theorem order2_eq (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain) :
    clLocalOrder2 RD hG R = clLocalOrder1 R + ((∑ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size) +
      ∑ v : (assemblyShape hM9 B).VIdx, (rowTree hM9 B RD v).size) := by
  classical
  unfold clLocalOrder2
  rw [← add_assoc]
  congr 1
  congr 1
  · rw [← Finset.sum_coe_sort]
    exact (Equiv.sum_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyPairOrder hG B hM9).symm)
      (fun p : ↥(clRegionalPairs hG U) => (RD.couple p.1).size)).symm
  · rw [← Finset.sum_coe_sort]
    exact (Equiv.sum_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyIntOrder hM9 B).e.symm)
      (fun z : ↥(clInteriorBranches R) => (RD.tree z.1).size)).symm

end WaveTurbulence.VineEstS3
