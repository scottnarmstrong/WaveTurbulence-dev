/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLMatrixPredecessorIdentity

/-! # Exact coefficient identity in frozen sumint hypothesis (ii) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Evaluate the actual source polynomial identity on one free lattice
basis vector. This proves the frozen coefficient equation, rather than
assuming a relation between proposed matrices. -/
theorem assembly_matrix_predecessor_coeff (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (hG : G.IsPlain) (v j : (assemblyShape hM9 B).VIdx) :
    assemblyBranchMatrix hM9 B v j -
      (assemblyPrev hM9 B v).elim 0 (fun u => assemblyBranchMatrix hM9 B u j) =
      ∑ p, assemblyCoeff hM9 B hG v (.inl p) * assemblyPairMatrix hM9 B hG p j := by
  classical
  let x : (assemblyShape hM9 B).VIdx → (Fin 1 → ℤ) := fun u _ => if u = j then 1 else 0
  have he := congrArg (fun f : Fin 1 → ℤ => f 0) (assembly_matrix_predecessor_apply hM9 B hG x v)
  have hsum (f : (assemblyShape hM9 B).VIdx → ℤ) :
      ((∑ u, f u • x u) : Fin 1 → ℤ) 0 = f j := by
    simp [x,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have hprev : ((assemblyPrev hM9 B v).elim (0 : Fin 1 → ℤ)
      (fun u => ∑ k, assemblyBranchMatrix hM9 B u k • x k)) 0 =
      (assemblyPrev hM9 B v).elim 0 (fun u => assemblyBranchMatrix hM9 B u j) := by
    cases assemblyPrev hM9 B v with
    | none => rfl
    | some u => exact hsum _
  simpa only [Pi.sub_apply,hsum,hprev,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he

end WaveTurbulence.VineEstS2
