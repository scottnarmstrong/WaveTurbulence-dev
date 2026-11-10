/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSplicePiece` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Gate
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece


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
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open TTree Finset WaveTurbulence WaveTurbulence.Mole WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Reg.Skeleton

variable {R : ℕ}

/-- **The Stage 1 piece over `𝒱_γ` of the original layered garden `LG` and the prescription `σ`** (main's
`RedSplice.stage1PieceOf` with the `𝒱_γ` units, collection and incoherency; a `Stage1PieceGD γ d R`). -/
@[expose] noncomputable def stage1PieceOf [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact TVineIsoInvariant]
    (γ : ℝ) [Fact (γ ≤ 1 / 2)] (d : ℕ) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (Mk : Set (CLVineG γ S) := ∅) : Stage1PieceGD γ d R where
  Gsb := (stSt γ S σ Mk).G
  Cs := collectionChoices γ S σ Mk
  ladders := ladderDataOf (stSt γ S σ Mk).G
  layer := (stSt γ S σ Mk).layer (RegRed.coreLayer LG D hS hd)
  gapSpecification := gapSpecificationMk γ S σ Mk
  gsk := gskOf γ (gregOf D hS LG) S σ (RegRed.coreLayer LG D hS hd) Mk
  bsk := bskOf γ S σ Mk

/-- **S4 obligation (TARGET Prop `subpro` (2)–(6), L2040–L2051) over `𝒱_γ`:** on the support of the epsilon and gap
factors of the piece, the decorated conclusions of `subpro` hold. This is the `support` field of
`Stage1PieceG.Sound`. -/
def SubproObligation {P : WTParams} (π : Stage1PieceG P R) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop :=
  ∀ z : GenDecoration π.Gsb P.d roots 0,
    splicedEpsilon π.Gsb π.Cs.hinges z.1 ≠ 0 →
    splicedGapIndicator π.Gsb (π.data (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0))
      P.L P.γ P.η base z.1 ≠ 0 →
    Src.SubproSupport P.γ π.Gsb π.Cs P.L P.γ P.η base
      (Finset.univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex π.Gsb z.1)

end WaveTurbulence.GammaLow.Fama
