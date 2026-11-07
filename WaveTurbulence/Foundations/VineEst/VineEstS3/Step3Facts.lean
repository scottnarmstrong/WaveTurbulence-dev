/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At
public import WaveTurbulence.Foundations.VineEst.VineEstS3.NumericCore

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

theorem card_Row_eq (D : SumintDatum d) : Fintype.card (Row D) = 2 * D.S.M := by
  unfold Row
  rw [Fintype.card_sum, Sumint.card_vector_index]; ring

theorem M_pos (hM9 : VINEPARAM) (B : CLChainAssembly G R n) : 1 ≤ clLocalOrder1 R := by
  have hI := assemblyShape_I_pos hM9 B
  have : 0 < Fintype.card (assemblyShape hM9 B).VIdx :=
    Fintype.card_pos_iff.2 ⟨⟨⟨0, hI⟩, ⟨0, by unfold SumintShape.n; split_ifs <;> omega⟩⟩⟩
  rw [Sumint.card_vector_index, assemblyShape_M] at this
  exact this

theorem maxPar_one (D : SumintDatum d) (hI : 0 < D.S.I) (h0 : ∀ v, D.param v = 0) : maxPar D = 1 := by
  unfold maxPar
  have : Nonempty D.S.TVar := ⟨Sum.inl ⟨⟨0, hI⟩, 0⟩⟩
  have : ∀ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v) = 1 := by
    intro v
    unfold jbr
    rw [h0 v]
    have : (WithLp.toLp 2 fun _ : Fin 1 => (0 : ℝ)) = 0 := by ext i; rfl
    simp [this]
  simp only [this, ciSup_const]

theorem sum_rowG (D : SumintDatum d) : ∑ ρ : Row D, (rowG D ρ) = D.M₁ := by
  unfold Row rowG SumintDatum.M₁
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]; rfl

theorem prod_rpow_rowG (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∏ ρ : Row D, L ^ (c * (rowG D ρ : ℝ)) = L ^ (c * (D.M₁ : ℝ)) := by
  rw [← Real.rpow_sum_of_pos hL, ← Finset.mul_sum]
  congr 2
  have := sum_rowG D
  exact_mod_cast this

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
