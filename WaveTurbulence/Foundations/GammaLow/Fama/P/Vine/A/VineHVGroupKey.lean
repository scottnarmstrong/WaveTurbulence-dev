/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineHVGroupKey` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.Vine.A.VineHVGroupKey
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
/-! R83 single-HV keys: normalized bond first, then ordered joint and dart names. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Both joints of a valid HV candidate belong to its support. -/
theorem HVCandidate.joints {t : GBranch G.tree × GBranch G.tree × GardenDart G}
    (h : HVCandidate γ G S t) : t.1 ∈ S ∧ t.2.1 ∈ S :=
  ⟨(isSomeVine_ends h.2).1, (isSomeVine_ends h.2).2.1⟩

/-- A candidate's deleted bond is internal to its support. -/
theorem HVCandidate.internal {t : GBranch G.tree × GBranch G.tree × GardenDart G}
    (h : HVCandidate γ G S t) : G.molecule.InGroup S t.2.2 := by
  have he := h.1
  unfold Molecule.ends at he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1.symm ▸ h.joints.1, h2.symm ▸ h.joints.2⟩
  · exact ⟨h1.symm ▸ h.joints.2, h2.symm ▸ h.joints.1⟩

/-- A valid single-HV candidate's deleted bond survives the all-SG splice. -/
def hvCandidateDart (γ : ℝ) [Fact (γ ≤ 1 / 2)] (hS : SingleHVGroup γ G S) (t : {t // HVCandidate γ G S t}) : CoarseDart γ G :=
  ⟨t.1.2.2, ((coarseSplice γ G).M.od_range _).mpr (by
    rintro ⟨a, ha, _⟩
    rw [hS.cls_none t.2.internal.1] at ha
    cases ha)⟩

/-- The bond is compared first in a fixed lexicographic address order; joint
and directed-dart names break ties. There is no prescription argument. -/
noncomputable def hvGroupKey (γ : ℝ) [Fact (γ ≤ 1 / 2)] (hS : SingleHVGroup γ G S) (t : {t // HVCandidate γ G S t}) : List (List ℕ) :=
  let d := coarseDartWord γ G (hvCandidateDart γ hS t)
  let m := coarseDartWord γ G (coarseDartMate γ G (hvCandidateDart γ hS t))
  [min d m, max d m, coarseAtomWord γ G t.1.1, coarseAtomWord γ G t.1.2.1, d]

/-- The complete normalized key distinguishes every valid single-HV triple. -/
theorem hvGroupKey_injective (hS : SingleHVGroup γ G S) : Function.Injective (hvGroupKey γ hS) := by
  intro x y he
  have htail := (List.cons.inj (List.cons.inj he).2).2
  have ha := (List.cons.inj htail).1
  have hb := (List.cons.inj (List.cons.inj htail).2).1
  have hd := (List.cons.inj (List.cons.inj (List.cons.inj htail).2).2).1
  have hea : x.1.1 = y.1.1 := coarseAtomWord_inj_of_none
    (hS.cls_none x.2.joints.1) (hS.cls_none y.2.joints.1) ha
  have heb : x.1.2.1 = y.1.2.1 := coarseAtomWord_inj_of_none
    (hS.cls_none x.2.joints.2) (hS.cls_none y.2.joints.2) hb
  have hed : x.1.2.2 = y.1.2.2 := congrArg Subtype.val (coarseDartWord_injective G hd)
  exact Subtype.ext (Prod.ext hea (Prod.ext heb hed))

/-- The single-HV normalized candidate set has exactly one least triple. -/
theorem hvGroupKey_existsUnique (hS : SingleHVGroup γ G S) :
    ∃! t : {t // HVCandidate γ G S t}, ∀ u, hvGroupKey γ hS t ≤ hvGroupKey γ hS u := by
  let : Nonempty {t // HVCandidate γ G S t} := hS.candidate
  exact existsUnique_least_key (hvGroupKey γ hS) (hvGroupKey_injective hS)

/-- R83's single-HV choice, made once in the sigma-independent normalization. -/
noncomputable def hvGroupPick (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (GBranch G.tree × GBranch G.tree × GardenDart G) := by
  classical
  exact if hS : SingleHVGroup γ G S then some (hvGroupKey_existsUnique hS).choose.1 else none


/-- The chosen triple is valid and is the unique least normalized candidate. -/
theorem hvGroupPick_spec {t : GBranch G.tree × GBranch G.tree × GardenDart G}
    (h : hvGroupPick γ G S = some t) : ∃ hS : SingleHVGroup γ G S, ∃ ht : HVCandidate γ G S t,
      ∀ u, hvGroupKey γ hS ⟨t, ht⟩ ≤ hvGroupKey γ hS u := by
  classical
  unfold hvGroupPick at h
  split_ifs at h with hS
  · have he := Option.some.inj h
    subst t
    exact ⟨hS, _, (hvGroupKey_existsUnique hS).choose_spec.1⟩

end WaveTurbulence.GammaLow.Fama.VineA
