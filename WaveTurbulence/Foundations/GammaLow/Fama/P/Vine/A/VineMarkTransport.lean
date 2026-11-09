/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineMarkTransport` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Vine.A.VineBatchIso
public import WaveTurbulence.Foundations.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
/-! B1b (R11, ruling R166): transport of a marked vine set along an actual molecule isomorphism.

`MarkTransported γ F M M'` (B0 probe, verbatim; the world's `Flower.MkDefs.MarkTransported` has the same body) says that
`F` carries the marked set `M` of the source skeleton onto the marked set `M'` of the target, vine by vine through the
atom map.  The twist-side transport lemmas (`VineA.vinesV0_imageMk`, `VineA.isV0Fam_twistMk`, `VineA.BatchIso.selectedMk`,
`VineA.fine_outputs_rebaseMk`) take it as a hypothesis; the world supplies it through `MarkInvariantBatchV` (Lemma 2⁺).
A composite transport splits through the intermediate skeleton (`markTransported_split`), with the intermediate marked
set `midMark`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.Stage1Mk
open WaveTurbulence.Stage1Mk WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Stage1 WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Transport of a marked set along a molecule isomorphism of skeletons. -/
def MarkTransported {S S' : Garden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (F : Stage1.MolIso S.molecule S'.molecule)
    (M : Set (CLVineG γ S)) (M' : Set (CLVineG γ S')) : Prop :=
  ∀ (c : CLVineG γ S) (c' : CLVineG γ S'), c'.atoms = F.img c.atoms → (c ∈ M ↔ c' ∈ M')

/-- Along the identity a marked set is transported only onto itself. -/
theorem markTransported_refl_eq {S : Garden w} {M M' : Set (CLVineG γ S)}
    (h : MarkTransported γ (molIsoRefl S) M M') : M = M' :=
  Set.ext fun c => h c c (by
    change c.atoms = c.atoms.image (Equiv.refl _)
    rw [Equiv.coe_refl, Finset.image_id])

/-- B1b-2: the empty marking is carried by every isomorphism (the `∅`-instance of the twist-side `…Mk` lemmas). -/
theorem markTransported_empty {S S' : Garden w} (F : Stage1.MolIso S.molecule S'.molecule) :
    MarkTransported γ F (∅ : Set (CLVineG γ S)) (∅ : Set (CLVineG γ S')) := fun _ _ _ => Iff.rfl


/-- The intermediate marked set of a composite transport: the pull-back of `M''` along `J`, together with the push-forward
of `M` along `F`. -/
def midMark {S S' S'' : Garden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (F : MolIso S.molecule S'.molecule) (J : MolIso S'.molecule S''.molecule)
    (M : Set (CLVineG γ S)) (M'' : Set (CLVineG γ S'')) : Set (CLVineG γ S') :=
  {c' | (∃ c'' ∈ M'', c''.atoms = J.img c'.atoms) ∨ ∃ c ∈ M, c'.atoms = F.img c.atoms}

/-- A transport along a composite splits through `midMark`. -/
theorem markTransported_split {S S' S'' : Garden w} (F : MolIso S.molecule S'.molecule)
    (J : MolIso S'.molecule S''.molecule) {M : Set (CLVineG γ S)} {M'' : Set (CLVineG γ S'')}
    (h : MarkTransported γ (molIsoTrans F J) M M'') :
    MarkTransported γ F M (midMark γ F J M M'') ∧ MarkTransported γ J (midMark γ F J M M'') M'' := by
  constructor
  · intro c c' hc
    constructor
    · intro hm
      exact Or.inr ⟨c, hm, hc⟩
    · rintro (⟨c'', hm'', he⟩ | ⟨d, hd, he⟩)
      · exact (h c c'' (by rw [he, hc, molIsoTrans_img])).mpr hm''
      · have := F.img_injective (he.symm.trans hc)
        rw [← VineA.clVine_eq_of_atoms this]
        exact hd
  · intro c' c'' hc
    constructor
    · rintro (⟨e, he, hea⟩ | ⟨d, hd, hda⟩)
      · rw [← VineA.clVine_eq_of_atoms (hea.trans hc.symm)]
        exact he
      · exact (h d c'' (by rw [hc, hda, molIsoTrans_img])).mp hd
    · intro hm
      exact Or.inl ⟨c'', hm, hc⟩

end WaveTurbulence.GammaLow.Fama.Stage1Mk
