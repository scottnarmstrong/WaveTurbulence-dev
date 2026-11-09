/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePlainA4
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceAmend7R83
public import WaveTurbulence.Foundations.Stage1.Shared.SkelFacts3
public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
import Mathlib.Tactic
/-! # Soundness of the normalized Stage 1 piece over `𝒱_γ` (packet L5a, item F)

Main's final producer uses the **normalized** piece `VineA.NormalizedSplice.stage1PieceOf` (the R83 successor of
`RedSplice.stage1PieceOf`), and `Represents.stage1Piece_sound_succ_uncond` (`Stage1/Represents/RepPr6.lean`) assembles
its `Stage1Piece.Sound` from the construction facts (`Stage1/Geometry/RedSplice{Final,Amend7}R83`, ported here as
`Fama.P.Stage1.Geometry.*`) and the S4 obligation `VineA.NormalizedSplice.Subpro.subproObligationA`
(`Stage1/Geometry/SubproFinal2R83.lean`).

The S4 obligation over `𝒱_γ` is packet L5c's item E (subpro′). Until L5c exports it, it is the named input
`NormalizedSubproInput`, stated exactly as main's `subproObligationA` with main's `SubproObligationA` replaced by its
`𝒱_γ` form `SubproObligation` (`Fama/Splice/Piece.lean`, the `support` field of `Stage1PieceG.Sound`). -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton

/-- **Named input (L5c, item E: subpro′ for the normalized piece).** Main's
`VineA.NormalizedSplice.Subpro.subproObligationA` over `𝒱_γ`, for every `γ = P.γ ≤ 1/2`: the S4 obligation holds for
the normalized Stage 1 piece of every prime skeleton. The three L5a inputs are hypotheses (they are instances of the
construction). -/
def NormalizedSubproInput : Prop :=
  ∀ (_ : Fact TVineF1Input) (_ : Fact VinechainlemPrimeInput) (_ : Fact TVineIsoInvariant)
    (P : WTParams) (_ : Fact (P.γ ≤ 1 / 2)) {R : ℕ} {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (_hP : IsPrimeGarden S) (_hI : S.Irreducible) (_hbal : IsBalancedSig S.sig) (_hn : 1 ≤ S.order)
    (p : ℕ) (_hN : S.order ≤ P.N (p + 1) ^ 4) (_hlayer : ∀ v, RegRed.coreLayer LG D hS hd v ≤ p)
    (_hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SubproObligation (P := P) (VineA.NormalizedSplice.stage1PieceOf P.γ P.d hS LG hd σ) base roots

variable {R : ℕ} [hF1 : Fact TVineF1Input] [hVC : Fact VinechainlemPrimeInput] [hIso : Fact TVineIsoInvariant]

/-- **`Stage1PieceG.Sound` for the normalized piece** (main's `Represents.stage1Piece_sound_succ_uncond`), from the
S4 obligation. -/
theorem normalizedStage1Piece_sound (hsub : NormalizedSubproInput) (P : WTParams) [hγ : Fact (P.γ ≤ 1 / 2)]
    {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (hP : IsPrimeGarden S) (hI : S.Irreducible) (hbal : IsBalancedSig S.sig) (hn : 1 ≤ S.order)
    (p : ℕ) (hN : S.order ≤ P.N (p + 1) ^ 4) (hlayer : ∀ v, RegRed.coreLayer LG D hS hd v ≤ p)
    (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    Stage1PieceG.Sound (P := P) (VineA.NormalizedSplice.stage1PieceOf P.γ P.d hS LG hd σ) p base roots := by
  obtain ⟨hB, hStr, hHinge⟩ := VineA.NormalizedSplice.construction_facts (γ := P.γ) S hP hI hbal hn σ
    (RegRed.coreLayer LG D hS hd) p (P.N (p + 1) ^ 4) hN hlayer
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
      support := hsub hF1 hVC hIso P hγ hS LG hd σ hP hI hbal hn p hN hlayer hL base roots
      hingeOutsideFirst := hHinge
      tripleDesignated := VineA.NormalizedSplice.tripleDesignated_collectionChoices (γ := P.γ)
        (Mole.garden_isMolecule S) (prime_noTriple S hP) σ
      hingeNoLoop := VineA.NormalizedSplice.hingeNoLoop_collectionChoices (γ := P.γ) σ }

/-- **Soundness of the normalized piece of a prescribed point** over a Stage-1 carried garden (truncation-free
carrier; main's `Represents.normalizedPiece_soundW`). -/
theorem normalizedPiece_soundW (hsub : NormalizedSubproInput) (P : WTParams) [Fact (P.γ ≤ 1 / 2)] (hR : 1 ≤ R)
    {p N : ℕ} (b : VineA.PrescribedPrimeGarden P.γ (2 * R)) (hc : Stage1Mk.Stage1CarriesW P p N b.layered)
    (hNb : N ≤ P.N (p + 1) ^ 4) (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    Stage1PieceG.Sound (P := P) (b.normalizedPiece P.d) p base roots := by
  obtain ⟨hI, hbal, hn⟩ := Represents.skelFacts_of_carriesW P p N hR hc b.prime
  have hsz := b.prime.data.decoded_order b.prime.prime.1 b.prime.decodes
  have hord : b.layered.garden.order = N := hc.2.1
  exact normalizedStage1Piece_sound hsub P b.prime.prime.1 b.layered b.prime.decodes
    (VineA.PrescribedPrimeGarden.totalSigma P.γ b) b.prime.prime hI hbal hn p (by omega)
    (fun v => Canon.layer_le_of_isCanonGC hc.1 _) hL base roots

/-- **Soundness of the normalized piece of a prescribed point** over a Stage-1 carried garden (main's
`Represents.normalizedPiece_sound`). -/
theorem normalizedPiece_sound (hsub : NormalizedSubproInput) (P : WTParams) [Fact (P.γ ≤ 1 / 2)] (hR : 1 ≤ R)
    {p N : ℕ} (b : VineA.PrescribedPrimeGarden P.γ (2 * R)) (hc : Stage1Carries P p N b.layered)
    (hNb : N ≤ P.N (p + 1) ^ 4) (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    Stage1PieceG.Sound (P := P) (b.normalizedPiece P.d) p base roots :=
  normalizedPiece_soundW hsub P hR b (Stage1Mk.stage1CarriesW_of_stage1Carries hc) hNb hL base roots

end WaveTurbulence.GammaLow.Fama
