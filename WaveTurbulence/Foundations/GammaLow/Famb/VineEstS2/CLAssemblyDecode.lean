/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyCoefficients
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChartEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyDecode
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChartEquations
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyCoefficients
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyDecode` (sha256 8d3aaebf40ea1e23…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact affine inverse decoder of the full source chain -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- The explicit unit free matrix really decodes every original bond of
the chain equivalence, in any additive commutative group. -/
theorem chainFlowChart_decodeΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) {E : Type} [AddCommGroup E] (g r : E)
    (x : chainInputIndexΓ hM9 B → E) (e : Bond G.molecule U) :
    ((chainFlowChartΓ hM9 B g r).symm x).1 e =
      g + (∑ j, chainDecodeFreeΓ hM9 B e j • x j) + chainDecodeGapΓ hM9 B e • r := by
  induction B generalizing g with
  | single hV R => exact (chosenVineChartΓ hM9 hV).decode_eq g r x e
  | append B hT hi hU R ih =>
    have hsum (f : chainInputIndexΓ hM9 (.append B hT hi hU R) → E) :
        (∑ j, f j) = (∑ j, f (.inl j)) + ∑ j, f (.inr j) := by
      exact Fintype.sum_sum_type f
    rw [hsum,chainFlowChart_symm_appendΓ,glueFlowFiber_val]
    unfold glueBondLabels
    cases he : (bondUnionEquiv (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU).symm e with
    | inl eS =>
      simp only [Sum.elim_inl]
      rw [ih, (chosenVineChartΓ hM9 hT).decode_eq]
      simp only [chainDecodeFreeΓ,chainDecodeGapΓ,he,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,add_smul]
      abel
    | inr eT =>
      simp only [Sum.elim_inr]
      rw [(chosenVineChartΓ hM9 hT).decode_eq]
      simp only [chainDecodeFreeΓ,chainDecodeGapΓ,he,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
        zero_smul,Finset.sum_const_zero,add_zero]

end WaveTurbulence.GammaLow.Famb.VineEstS2
