/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AmbEng
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BadEng
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.AmbEng
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BadEng` (sha256 5b209893af457dba…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 10, step 4.1): the bad-case clause of the engine datum from per-block data

`badClauseP_engDatum`: `BadClauseP (engDatum ..)` from the three clauses written directly in terms of the block kinds `bk`, the constraints
`cons` and the exponents `g g'` (the fields `badKind`, `constraints`, `g`, `g'` of `modPiece` are `bk`, `cons`, `g`, `g'`).
`badKind_zero_clause`: the clause (a) for a block of kind `0` from its two order constraints in either orientation.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **`BadClauseP` of the engine datum** from the per-block data (`bk`, `cons`, `g`, `g'` are the fields of the datum). -/
theorem badClauseP_engDatumΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (h0 : ∀ i, (assemblyShapeΓ hM9 B).nor i = false → bk i = 0 → ∃ h : 0 < (assemblyShapeΓ hM9 B).m i,
      (((.inr (.inl ⟨i, ⟨0, h⟩⟩) : (assemblyShapeΓ hM9 B).TVar), (.inl ⟨i, 0⟩ : (assemblyShapeΓ hM9 B).TVar)) ∈ cons ∧
        ((.inl ⟨i, 0⟩ : (assemblyShapeΓ hM9 B).TVar), (.inl ⟨i, ⟨1, by omega⟩⟩ : (assemblyShapeΓ hM9 B).TVar)) ∈ cons) ∨
      (((.inl ⟨i, ⟨1, by omega⟩⟩ : (assemblyShapeΓ hM9 B).TVar), (.inl ⟨i, 0⟩ : (assemblyShapeΓ hM9 B).TVar)) ∈ cons ∧
        ((.inl ⟨i, 0⟩ : (assemblyShapeΓ hM9 B).TVar), (.inr (.inl ⟨i, ⟨0, h⟩⟩) : (assemblyShapeΓ hM9 B).TVar)) ∈ cons))
    (h2 : ∀ i, (assemblyShapeΓ hM9 B).nor i = false → bk i = 2 → 0 < (assemblyShapeΓ hM9 B).m i)
    (h3 : ∀ i, (assemblyShapeΓ hM9 B).nor i = false → bk i = 3 → ∃ j : Fin ((assemblyShapeΓ hM9 B).n i), 1 ≤ max (g ⟨i, j⟩) (g' ⟨i, j⟩)) :
    BadClauseP (engDatumΓ hM9 B hG W wN wDec bk cons g g') :=
  fun i hi => ⟨h0 i hi, h2 i hi, h3 i hi⟩

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
