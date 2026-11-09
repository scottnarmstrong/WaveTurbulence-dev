/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLMatrixPredecessorIdentity
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLMatrixPredecessorCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLMatrixPredecessorIdentity
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLMatrixPredecessorCoefficients` (sha256 46ea9e877dec35c8…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact coefficient identity in frozen sumint hypothesis (ii) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Evaluate the actual source polynomial identity on one free lattice
basis vector. This proves the frozen coefficient equation, rather than
assuming a relation between proposed matrices. -/
theorem assembly_matrix_predecessor_coeffΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (hG : G.IsPlain) (v j : (assemblyShapeΓ hM9 B).VIdx) :
    assemblyBranchMatrixΓ hM9 B v j -
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => assemblyBranchMatrixΓ hM9 B u j) =
      ∑ p, assemblyCoeffΓ hM9 B hG v (.inl p) * assemblyPairMatrixΓ hM9 B hG p j := by
  classical
  let x : (assemblyShapeΓ hM9 B).VIdx → (Fin 1 → ℤ) := fun u _ => if u = j then 1 else 0
  have he := congrArg (fun f : Fin 1 → ℤ => f 0) (assembly_matrix_predecessor_applyΓ hM9 B hG x v)
  have hsum (f : (assemblyShapeΓ hM9 B).VIdx → ℤ) :
      ((∑ u, f u • x u) : Fin 1 → ℤ) 0 = f j := by
    simp [x,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have hprev : ((assemblyPrevΓ hM9 B v).elim (0 : Fin 1 → ℤ)
      (fun u => ∑ k, assemblyBranchMatrixΓ hM9 B u k • x k)) 0 =
      (assemblyPrevΓ hM9 B v).elim 0 (fun u => assemblyBranchMatrixΓ hM9 B u j) := by
    cases assemblyPrevΓ hM9 B v with
    | none => rfl
    | some u => exact hsum _
  simpa only [Pi.sub_apply,hsum,hprev,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he

end WaveTurbulence.GammaLow.Famb.VineEstS2
