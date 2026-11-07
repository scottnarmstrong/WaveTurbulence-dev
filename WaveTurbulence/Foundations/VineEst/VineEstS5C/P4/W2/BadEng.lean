/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AmbEng

/-! # P4-W2 (session 10, step 4.1): the bad-case clause of the engine datum from per-block data

`badClauseP_engDatum`: `BadClauseP (engDatum ..)` from the three clauses written directly in terms of the block kinds `bk`, the constraints
`cons` and the exponents `g g'` (the fields `badKind`, `constraints`, `g`, `g'` of `modPiece` are `bk`, `cons`, `g`, `g'`).
`badKind_zero_clause`: the clause (a) for a block of kind `0` from its two order constraints in either orientation.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **`BadClauseP` of the engine datum** from the per-block data (`bk`, `cons`, `g`, `g'` are the fields of the datum). -/
theorem badClauseP_engDatum (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (h0 : ∀ i, (assemblyShape hM9 B).nor i = false → bk i = 0 → ∃ h : 0 < (assemblyShape hM9 B).m i,
      (((.inr (.inl ⟨i, ⟨0, h⟩⟩) : (assemblyShape hM9 B).TVar), (.inl ⟨i, 0⟩ : (assemblyShape hM9 B).TVar)) ∈ cons ∧
        ((.inl ⟨i, 0⟩ : (assemblyShape hM9 B).TVar), (.inl ⟨i, ⟨1, by omega⟩⟩ : (assemblyShape hM9 B).TVar)) ∈ cons) ∨
      (((.inl ⟨i, ⟨1, by omega⟩⟩ : (assemblyShape hM9 B).TVar), (.inl ⟨i, 0⟩ : (assemblyShape hM9 B).TVar)) ∈ cons ∧
        ((.inl ⟨i, 0⟩ : (assemblyShape hM9 B).TVar), (.inr (.inl ⟨i, ⟨0, h⟩⟩) : (assemblyShape hM9 B).TVar)) ∈ cons))
    (h2 : ∀ i, (assemblyShape hM9 B).nor i = false → bk i = 2 → 0 < (assemblyShape hM9 B).m i)
    (h3 : ∀ i, (assemblyShape hM9 B).nor i = false → bk i = 3 → ∃ j : Fin ((assemblyShape hM9 B).n i), 1 ≤ max (g ⟨i, j⟩) (g' ⟨i, j⟩)) :
    BadClauseP (engDatum hM9 B hG W wN wDec bk cons g g') :=
  fun i hi => ⟨h0 i hi, h2 i hi, h3 i hi⟩

end WaveTurbulence.VineEstS5C.P4.W2
