/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainInverseRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices

/-! # Unit integer inverse matrix selected from proved source rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def chainInverseCoeff (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (i : chainInputIndex hM9 B) : ↥(clRegionalPairs hG U) ⊕ Fin 4 → ℤ :=
  Classical.choose (exists_chainInverseRow hM9 B hG i)

theorem chainInverseCoeff_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (i : chainInputIndex hM9 B) (o : ↥(clRegionalPairs hG U) ⊕ Fin 4) : IsUnitCoeff (chainInverseCoeff hM9 B hG i o) :=
  (Classical.choose_spec (exists_chainInverseRow hM9 B hG i)).1 o

theorem chainInverseCoeff_identity (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (i : chainInputIndex hM9 B) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) :
    let κ := (clChainCoordinateEquiv hL B base β hβ hM9).symm x
    x (assemblyVectorEquiv hM9 B i) = ∑ o, chainInverseCoeff hM9 B hG i o •
      clOriginValue B.isBlock R hG (clExtendIndices R κ.1) o :=
  (Classical.choose_spec (exists_chainInverseRow hM9 B hG i)).2 hL base β hβ x

noncomputable def assemblyInversePairMatrix (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    Matrix (assemblyShape hM9 B).VIdx (assemblyShape hM9 B).VIdx ℤ :=
  fun v p => chainInverseCoeff hM9 B hG ((assemblyVectorEquiv hM9 B).symm v)
    (.inl ((assemblyPairOrder hG B hM9).symm ((assemblyRowEquiv hM9 B).symm p)))

theorem assemblyInversePairMatrix_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v p : (assemblyShape hM9 B).VIdx) : IsUnitCoeff (assemblyInversePairMatrix hM9 B hG v p) :=
  chainInverseCoeff_unit hM9 B hG _ _

end WaveTurbulence.VineEstS2
