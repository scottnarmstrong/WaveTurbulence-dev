/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceGap
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGreg
public import WaveTurbulence.Foundations.FinalCount.RedSpliceData
public import WaveTurbulence.Foundations.FinalCount.RedSpliceFinal
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the Stage 1 piece of `(G, σ)` (RULINGS R19)

`stage1PieceOf` is the `Stage1PieceD` value of the original layered garden `LG` with skeleton `S`, regular
reconstruction data `D` (REGRED) and SG/LG/ZG prescription `σ`:
* `Gsb`: the skeleton with all units of `𝒱_0` spliced (`stSt`);
* `Cs`: the choice data `C_1`, hinges and hinge pairs (`collectionChoices`);
* `ladders`: the selected maximal-ladder presentations (`ladderDataOf`);
* `layer`: the pre-layering inherited from `LG` (`coreLayer`, TARGET L1958);
* `gapSpecification`: the factor `Z` of TARGET L1956, L1963 (`RedSplice.gapSpecification`);
* `gsk = g_reg + Σ incoherency of the vines of 𝒱_0` and `bsk = #bad vines of 𝒱_0` (TARGET L1962; `gregOf`, `gskOf`,
  `bskOf`).
`SubproObligation` is the named S4 obligation (TARGET Prop `subpro` (2)-(6), L2040-L2051): the `support` field of
`Stage1Piece.Sound`.  `stage1Piece_sound` assembles every other field.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole WaveTurbulence.LGSpine WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton

variable {R : ℕ}

/-- **The Stage 1 piece of the original layered garden `LG` and the prescription `σ`.** -/
@[expose] noncomputable def stage1PieceOf (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (Mk : Set (Stage1.CLVine S) := ∅) : Stage1PieceD d R where
  Gsb := (stSt S σ Mk).G
  Cs := collectionChoices S σ Mk
  ladders := ladderDataOf (stSt S σ Mk).G
  layer := (stSt S σ Mk).layer (RegRed.coreLayer LG D hS hd)
  gapSpecification := gapSpecificationMk S σ Mk
  gsk := gskOf (gregOf D hS LG) S σ (RegRed.coreLayer LG D hS hd) Mk
  bsk := bskOf S σ Mk

end WaveTurbulence.RedSplice
