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
public import WaveTurbulence.Foundations.FinalCount.RedSpliceAmend7
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

/-- **S4 obligation (TARGET Prop `subpro` (2)-(6), L2040-L2051):** on the support of the epsilon and gap factors
of the piece, the decorated conclusions of `subpro` hold.  This is the `support` field of `Stage1Piece.Sound`. -/
@[expose] def SubproObligation {P : WTParams} (π : Stage1Piece P R) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop :=
  ∀ z : GenDecoration π.Gsb P.d roots 0,
    splicedEpsilon π.Gsb π.Cs.hinges z.1 ≠ 0 →
    splicedGapIndicator π.Gsb (π.data (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)) P.L P.γ P.η base z.1 ≠ 0 →
    SourceVine.SubproSupport π.Gsb π.Cs P.L P.γ P.η base
      (Finset.univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex π.Gsb z.1)

/-- **`Stage1Piece.Sound` for the construction**, given the skeleton hypotheses, `n ≤ N_{p+1}^4`, the layering
bound, and the S4 obligation. -/
theorem stage1Piece_sound (P : WTParams) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (hP : IsPrimeGarden S) (hI : S.Irreducible) (hbal : IsBalancedSig S.sig) (hn : 1 ≤ S.order)
    (p : ℕ) (hN : S.order ≤ P.N (p + 1) ^ 4) (hlayer : ∀ v, RegRed.coreLayer LG D hS hd v ≤ p)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hsub : SubproObligation (stage1PieceOf P.d hS LG hd σ) base roots) :
    Stage1Piece.Sound (P := P) (stage1PieceOf P.d hS LG hd σ) p base roots := by
  obtain ⟨hB, hStr, hHinge⟩ := construction_facts S hP hI hbal hn σ (RegRed.coreLayer LG D hS hd) p
    (P.N (p + 1) ^ 4) hN hlayer
  exact
    { plain := hB.plain
      irreducible := hB.irreducible
      balanced := hB.balanced
      order_pos := hB.order_pos
      order_le := hB.order_le
      layer_le := hB.layer_le
      molecule := hB.molecule
      connected := hB.connected
      atom_count := hB.atom_count
      bond_count := hB.bond_count
      structural := hStr
      support := hsub
      hingeOutsideFirst := hHinge
      tripleDesignated :=
        tripleDesignated_collectionChoices (garden_isMolecule S) (prime_noTriple S hP) σ
      hingeNoLoop := hingeNoLoop_collectionChoices σ }

/-- The two AMEND7 fields of `stage1Piece_sound`, stated for `(stage1PieceOf ..).Cs`. -/
theorem stage1Piece_sound_amend7 {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (hP : IsPrimeGarden S) (d : ℕ) :
    (stage1PieceOf d hS LG hd σ).Cs.TripleDesignated ∧ (stage1PieceOf d hS LG hd σ).Cs.HingeNoLoop :=
  ⟨tripleDesignated_collectionChoices (garden_isMolecule S) (prime_noTriple S hP) σ,
    hingeNoLoop_collectionChoices σ⟩

end WaveTurbulence.RedSplice
