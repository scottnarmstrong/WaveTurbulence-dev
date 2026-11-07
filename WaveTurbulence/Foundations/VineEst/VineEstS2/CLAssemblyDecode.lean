/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChartEquations

/-! # Exact affine inverse decoder of the full source chain -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- The explicit unit free matrix really decodes every original bond of
the chain equivalence, in any additive commutative group. -/
theorem chainFlowChart_decode (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) {E : Type} [AddCommGroup E] (g r : E)
    (x : chainInputIndex hM9 B → E) (e : Bond G.molecule U) :
    ((chainFlowChart hM9 B g r).symm x).1 e =
      g + (∑ j, chainDecodeFree hM9 B e j • x j) + chainDecodeGap hM9 B e • r := by
  induction B generalizing g with
  | single hV R => exact (chosenVineChart hM9 _ hV).decode_eq g r x e
  | append B hT hi hU R ih =>
    have hsum (f : chainInputIndex hM9 (.append B hT hi hU R) → E) :
        (∑ j, f j) = (∑ j, f (.inl j)) + ∑ j, f (.inr j) := by
      exact Fintype.sum_sum_type f
    rw [hsum,chainFlowChart_symm_append,glueFlowFiber_val]
    unfold glueBondLabels
    cases he : (bondUnionEquiv (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU).symm e with
    | inl eS =>
      simp only [Sum.elim_inl]
      rw [ih, (chosenVineChart hM9 _ hT).decode_eq]
      simp only [chainDecodeFree,chainDecodeGap,he,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,add_smul]
      abel
    | inr eT =>
      simp only [Sum.elim_inr]
      rw [(chosenVineChart hM9 _ hT).decode_eq]
      simp only [chainDecodeFree,chainDecodeGap,he,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
        zero_smul,Finset.sum_const_zero,add_zero]

end WaveTurbulence.VineEstS2
