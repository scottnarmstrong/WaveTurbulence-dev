/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Datum
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TimeDomMeas
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.LevelAbs

/-! # P2: the `sumint` form is the clocked expression of the piece datum (`termFn = clockedExprMul3`, second half)

`engDatum`: the piece datum of the assembly (`modPiece (pieceDatum (sourceSumintDatum ..) ..) bk cons g g'`).  `sumint_eq_expr3`: the `sumint` form of
`Dict.recFac_cst_lkRaw_eq` equals `c ζ · clockedExprMul3 Mx cr` as soon as (`hint`) the engine integrand times the kind-1 prefactor is the `sumint` integrand
a.e. on the engine time domain, (`hsub`) the engine domain is contained in the `sumint` domain and (`hvan`) the `sumint` integrand vanishes a.e. on the rest. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The engine datum of a piece of the assembly. -/
noncomputable def engDatum (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar))
    (g g' : (assemblyShape hM9 B).VIdx → ℕ) : SumintPar.SumintDatum d :=
  modPiece (pieceDatum (sourceSumintDatum hM9 B hG W) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) wN wDec) bk cons g g'

/-- The kind-1 prefactor `‖E₀ - E₁‖^{#kind-1 blocks}` of `clockedExprMul3`. -/
noncomputable def kind1Pref {D : SumintPar.SumintDatum d} (E : Fin 4 → Mom d) : ℝ :=
  ‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card

end WaveTurbulence.VineEstS5C.P2
