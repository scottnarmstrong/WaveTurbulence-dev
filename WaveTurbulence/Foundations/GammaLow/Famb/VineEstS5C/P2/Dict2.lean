/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Datum
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TimeDomMeas
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.LevelAbs
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Dict2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P2.Recentered
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Dict2` (sha256 e415e70007525c9d…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P2: the `sumint` form is the clocked expression of the piece datum (`termFn = clockedExprMul3`, second half)

`engDatum`: the piece datum of the assembly (`modPiece (pieceDatum (sourceSumintDatum ..) ..) bk cons g g'`).  `sumint_eq_expr3`: the `sumint` form of
`Dict.recFac_cst_lkRaw_eq` equals `c ζ · clockedExprMul3 Mx cr` as soon as (`hint`) the engine integrand times the kind-1 prefactor is the `sumint` integrand
a.e. on the engine time domain, (`hsub`) the engine domain is contained in the `sumint` domain and (`hvan`) the `sumint` integrand vanishes a.e. on the rest. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The engine datum of a piece of the assembly. -/
noncomputable def engDatumΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ) : SumintPar.SumintDatum d :=
  modPiece (pieceDatum (sourceSumintDatumΓ hM9 B hG W) (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) wN wDec) bk cons g g'

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P2
