/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryPredecessorApply
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SourceBoundaryBasis

/-! # All four exact affine identities of frozen sumint hypothesis (ii) -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assembly_boundary_predecessor_coeff (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : (assemblyShape hM9 B).VIdx) (c : Fin 4) :
    assemblyBranchBoundaryRow hM9 B v c -
      (assemblyPrev hM9 B v).elim 0 (fun u => assemblyBranchBoundaryRow hM9 B u c) =
      (∑ p, assemblyCoeff hM9 B hG v (.inl p)*assemblyPairBoundaryRow hM9 B hG p c) +
        assemblyCoeff hM9 B hG v (.inr c) := by
  let β := sourceBoundaryBasis (G.sign a.toNode) c
  have he := congrArg (fun f : Fin 1 → ℤ => f 0)
    (assembly_boundary_predecessor_apply hM9 B hG β (sourceBoundaryBasis_conservation _ c) v)
  have hb (u : (assemblyShape hM9 B).VIdx) :
      ((∑ j, assemblyBranchBoundaryRow hM9 B u j • β j) : Fin 1 → ℤ) 0 = assemblyBranchBoundaryRow hM9 B u c :=
    sourceBoundaryBasis_eval _ c _ (assemblyBranchBoundaryRow_zero hM9 B u)
  have hp (u : (assemblyShape hM9 B).VIdx) :
      ((∑ j, assemblyPairBoundaryRow hM9 B hG u j • β j) : Fin 1 → ℤ) 0 = assemblyPairBoundaryRow hM9 B hG u c :=
    sourceBoundaryBasis_eval _ c _ (assemblyPairBoundaryRow_zero hM9 B hG u)
  have hs : ((∑ j, assemblyCoeff hM9 B hG v (.inr j) • β j) : Fin 1 → ℤ) 0 = assemblyCoeff hM9 B hG v (.inr c) :=
    sourceBoundaryBasis_eval _ c _ (assemblyCoeff_upper_zero hM9 B hG v)
  have hprev : ((assemblyPrev hM9 B v).elim (0 : Fin 1 → ℤ)
      (fun u => ∑ j, assemblyBranchBoundaryRow hM9 B u j • β j)) 0 =
      (assemblyPrev hM9 B v).elim 0 (fun u => assemblyBranchBoundaryRow hM9 B u c) := by
    cases assemblyPrev hM9 B v with
    | none => rfl
    | some u => exact hb u
  simpa only [Pi.sub_apply,Pi.add_apply,hb,hp,hs,hprev,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he

end WaveTurbulence.VineEstS2
