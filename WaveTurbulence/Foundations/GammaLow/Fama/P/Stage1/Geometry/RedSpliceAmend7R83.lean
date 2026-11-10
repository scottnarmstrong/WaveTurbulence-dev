/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceAmend7R83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceFinalR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceTripleHingeR83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceAmend7R83
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceTripleDesigR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
-- R83 port of rs-src/RedSpliceAmend7.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# REDSPLICE-DEF (S2a), R48 AMEND7 producer obligations

the proofs that `collectionChoices γ S σ` satisfies `Src.SubproChoices.TripleDesignated` and `HingeNoLoop` (in lg-spine `SourceSubproObjects` since AMEND7):
* `tripleDesignated_collectionChoices` (R37 `triple_in_hingePair`, TARGET subpro (2),(5), DH23 L1775 (iii));
* `hingeNoLoop_collectionChoices` (`SpMap.od_range`: a dart of `G_sb` never has both ends in one merged class).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open TTree Finset WaveTurbulence WaveTurbulence.Mole WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- `collectionChoices γ G σ` satisfies `TripleDesignated` (term of S4's `triple_in_designated`, via
`triple_in_hingePair`; no S4 import). -/
theorem tripleDesignated_collectionChoices {G : Garden w} (hM : G.molecule.IsMolecule)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) (σ : Prescription G) :
    (collectionChoices γ G σ).TripleDesignated := by
  intro a b h
  rcases (stSt γ G σ).triple_hinge hno a b h with ha | hb
  · obtain ⟨x, y, hxy, hT, h1, h2⟩ := triple_in_hingePair hM σ ha h
    exact ⟨a, ha, b, x, y, Or.inl ⟨rfl, rfl⟩, by simp [collectionChoices, hxy], by simp [collectionChoices, hxy],
      hT, h1, h2⟩
  · have h' : (stSt γ G σ).G.molecule.bondsBetween b a = 3 := by
      rw [Mole.bondsBetween_symm]; exact h
    obtain ⟨x, y, hxy, hT, h1, h2⟩ := triple_in_hingePair hM σ hb h'
    exact ⟨b, hb, a, x, y, Or.inr ⟨rfl, rfl⟩, by simp [collectionChoices, hxy], by simp [collectionChoices, hxy],
      hT, h1, h2⟩

/-- B1b (Mk-general form of `hingeNoLoop_collectionChoices`). -/
theorem hingeNoLoop_collectionChoicesMk {G : Garden w} (σ : Prescription G) {Mk : Set (CLVineG γ _)} :
    (collectionChoices γ (Mk := Mk) G σ).HingeNoLoop := by
  intro x hx hloop
  have hcn := ((stSt γ (Mk := Mk) G σ).mem_hinges _).mp hx
  have hr := ((stSt γ (Mk := Mk) G σ).M.od_range ((stSt γ (Mk := Mk) G σ).M.od x)).mp ⟨x, rfl⟩
  have h1 := (stSt γ (Mk := Mk) G σ).M.ob_atom x
  have h2 := (stSt γ (Mk := Mk) G σ).M.ob_atom ((stSt γ (Mk := Mk) G σ).G.molecule.mate x)
  rw [(stSt γ (Mk := Mk) G σ).M.od_mate] at h2
  rw [← hloop] at h2
  set p := G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od x)
  set q := G.molecule.atom (G.molecule.mate ((stSt γ (Mk := Mk) G σ).M.od x))
  have hp : (stSt γ (Mk := Mk) G σ).cls p ≠ none := by
    intro hn
    apply hcn
    rw [h1]; simp [repC, hn]
  have hq : (stSt γ (Mk := Mk) G σ).cls q ≠ none := by
    intro hn
    apply hcn
    rw [h2]; simp [repC, hn]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hq
  have hab : a = b := by
    have e : repC (stSt γ (Mk := Mk) G σ).cls p = repC (stSt γ (Mk := Mk) G σ).cls q := h1.symm.trans h2
    simp [repC, ha, hb] at e; exact e
  exact hr ⟨a, ha, hab ▸ hb⟩

/-- No loop dart at a hinge of `G_sb`: both ends of a dart of `G_sb` never lie in one merged class (`od_range`). -/
theorem hingeNoLoop_collectionChoices {G : Garden w} (σ : Prescription G) :
    (collectionChoices γ G σ).HingeNoLoop := hingeNoLoop_collectionChoicesMk (Mk := ∅) σ

end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
