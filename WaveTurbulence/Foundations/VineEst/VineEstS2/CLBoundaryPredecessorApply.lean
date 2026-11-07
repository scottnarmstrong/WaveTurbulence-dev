/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAffineBoundaryRows

/-! # Source-consistent affine boundary predecessor identities -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assemblyCoeff_upper_zero (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : (assemblyShape hM9 B).VIdx) : assemblyCoeff hM9 B hG v (.inr 0) = 0 :=
  clOriginCoeff_upper B.isBlock R hG _ _

/-- Set only the free variables to zero; all actual boundary data remain
arbitrary subject to their original signed source momentum relation. -/
theorem assembly_boundary_predecessor_apply (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (v : (assemblyShape hM9 B).VIdx) :
    (∑ c, assemblyBranchBoundaryRow hM9 B v c • β c) -
      (assemblyPrev hM9 B v).elim 0 (fun u => ∑ c, assemblyBranchBoundaryRow hM9 B u c • β c) =
      (∑ p, assemblyCoeff hM9 B hG v (.inl p) • (∑ c, assemblyPairBoundaryRow hM9 B hG p c • β c)) +
      ∑ c, assemblyCoeff hM9 B hG v (.inr c) • β c := by
  let κ := (clChainCoordinateEquiv (L := 1) one_ne_zero B (0 : Mom d) β hβ hM9).symm 0
  have hb (u : (assemblyShape hM9 B).VIdx) :
      assemblyBranchValue hM9 B (clExtendIndices R κ.1) u = ∑ c, assemblyBranchBoundaryRow hM9 B u c • β c := by
    simpa only [Pi.zero_apply,smul_zero,Finset.sum_const_zero,zero_add] using
      clChain_branch_affine_value (L := 1) one_ne_zero B (0 : Mom d) β hβ hM9 0 u
  have hp (u : (assemblyShape hM9 B).VIdx) :
      assemblyPairValue hM9 B hG (clExtendIndices R κ.1) u = ∑ c, assemblyPairBoundaryRow hM9 B hG u c • β c := by
    simpa only [Pi.zero_apply,smul_zero,Finset.sum_const_zero,zero_add] using
      clChain_pair_affine_value (L := 1) one_ne_zero B (0 : Mom d) β hβ hM9 hG 0 u
  have hbound (c : Fin 4) : clExtendIndices R κ.1 (clBoundaryNodes R c) = β c :=
    latticePoint_injective_of_ne_zero one_ne_zero (add_left_cancel (κ.2.2.2 c))
  have hi := assembly_predecessor_identity hM9 B hG (clExtendIndices R κ.1) κ.2.1 κ.2.2.1 v
  have hprev : (assemblyPrev hM9 B v).elim 0 (assemblyBranchValue hM9 B (clExtendIndices R κ.1)) =
      (assemblyPrev hM9 B v).elim 0 (fun u => ∑ c, assemblyBranchBoundaryRow hM9 B u c • β c) := by
    cases assemblyPrev hM9 B v with
    | none => rfl
    | some u => exact hb u
  simpa only [hb,hp,hbound,hprev] using hi

end WaveTurbulence.VineEstS2
