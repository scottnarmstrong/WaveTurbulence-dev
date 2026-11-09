/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproCrownR83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproBlockGeo
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrownR83
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
-- R83 port of sp-src/SubproCrown.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): the darts at a hinge atom are the external darts of its unit
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
open WaveTurbulence.VineA.NormalizedSplice.Subpro WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Fama.VineA WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Stage1 WaveTurbulence.Mole

variable {R : ℕ} {G : Garden (2 * R)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b (Mk-general form of `crown_dart`). -/
theorem crown_dartMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {u : CLBlock G} {Mk : Set (CLVineG γ _)} (hu : u ∈ Fama.unitBlocks γ (Mk := Mk) G σ)
    {v : GBranch (stSt γ (Mk := Mk) G σ).G.tree} (hv : (stSt γ (Mk := Mk) G σ).M.ob v = u.upper) {x : GardenDart (stSt γ (Mk := Mk) G σ).G}
    (hx : (stSt γ (Mk := Mk) G σ).G.molecule.atom x = v) :
    G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od x) ∈ u.atoms ∧ ¬ G.molecule.InGroup u.atoms ((stSt γ (Mk := Mk) G σ).M.od x) ∧
      (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od x) = u.upper ∨ G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od x) = u.lower) := by
  have hrep : repC (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od x)) = u.upper := by
    rw [← (stSt γ (Mk := Mk) G σ).M.ob_atom, hx, hv]
  have hcls : (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od x)) = some u.upper := by
    unfold repC at hrep
    rcases hc : (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od x)) with _ | a
    · rw [hc] at hrep
      have h1 : (stSt γ (Mk := Mk) G σ).cls u.upper = some u.upper := Fama.stSt_cls_memMk (Mk := Mk) hM σ hu u.isBlock.2.1
      simp only [Option.getD_none] at hrep
      rw [hrep] at hc
      rw [hc] at h1; cases h1
    · rw [hc] at hrep; simp only [Option.getD_some] at hrep; rw [hrep]
  have hmem : G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od x) ∈ u.atoms := Fama.VineA.NormalizedSplice.mem_of_cls_eqMk (Mk := Mk) hM σ hu hcls
  have hext : ¬ G.molecule.InGroup u.atoms ((stSt γ (Mk := Mk) G σ).M.od x) := by
    intro hin
    have := ((stSt γ (Mk := Mk) G σ).M.od_range ((stSt γ (Mk := Mk) G σ).M.od x)).mp ⟨x, rfl⟩
    exact this ⟨u.upper, hcls, Fama.stSt_cls_memMk (Mk := Mk) hM σ hu hin.2⟩
  refine ⟨hmem, hext, ?_⟩
  by_contra hne
  push Not at hne
  exact hext (block_interior_ext hM u.isBlock hmem hne.1 hne.2 rfl)

/-- A dart of `M_sb` at the crown of a unit is the lift of an external dart of the unit at one of its Fama.ChainL.joints. -/
theorem crown_dart (hM : G.molecule.IsMolecule) (σ : Prescription G) {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ G σ)
    {v : GBranch (stSt γ G σ).G.tree} (hv : (stSt γ G σ).M.ob v = u.upper) {x : GardenDart (stSt γ G σ).G}
    (hx : (stSt γ G σ).G.molecule.atom x = v) :
    G.molecule.atom ((stSt γ G σ).M.od x) ∈ u.atoms ∧ ¬ G.molecule.InGroup u.atoms ((stSt γ G σ).M.od x) ∧
      (G.molecule.atom ((stSt γ G σ).M.od x) = u.upper ∨ G.molecule.atom ((stSt γ G σ).M.od x) = u.lower) := crown_dartMk (Mk := ∅) hM σ hu hv hx

/-- B1b (Mk-general form of `common_joint`). -/
theorem common_jointMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {u : CLBlock G} {Mk : Set (CLVineG γ _)} (hu : u ∈ Fama.unitBlocks γ (Mk := Mk) G σ)
    {v : GBranch (stSt γ (Mk := Mk) G σ).G.tree} (hv : (stSt γ (Mk := Mk) G σ).M.ob v = u.upper)
    {oc ic : GardenDart (stSt γ (Mk := Mk) G σ).G} {jc : GBranch G.tree} (hjc : jc = u.upper ∨ jc = u.lower)
    (hoc : G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od oc) = jc) (hic : G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od ic) = jc)
    (hoc_ext : ¬ G.molecule.InGroup u.atoms ((stSt γ (Mk := Mk) G σ).M.od oc))
    (hic_ext : ¬ G.molecule.InGroup u.atoms ((stSt γ (Mk := Mk) G σ).M.od ic))
    (hoc_out : (stSt γ (Mk := Mk) G σ).G.molecule.out oc = true) (hic_out : (stSt γ (Mk := Mk) G σ).G.molecule.out ic = false)
    {ao ai : GardenDart (stSt γ (Mk := Mk) G σ).G} (hao : (stSt γ (Mk := Mk) G σ).G.molecule.atom ao = v)
    (hai : (stSt γ (Mk := Mk) G σ).G.molecule.atom ai = v)
    (hao_out : (stSt γ (Mk := Mk) G σ).G.molecule.out ao = true) (hai_out : (stSt γ (Mk := Mk) G σ).G.molecule.out ai = false)
    (hxor : (ao = oc ∧ ai = ic) ∨ (ao ≠ oc ∧ ai ≠ ic)) :
    ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od ao) = j ∧
      G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od ai) = j := by
  classical
  rcases hxor with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · exact ⟨jc, hjc, hoc, hic⟩
  · obtain ⟨hao1, hao2, hao3⟩ := crown_dartMk (Mk := Mk) hM σ hu hv hao
    obtain ⟨hai1, hai2, hai3⟩ := crown_dartMk (Mk := Mk) hM σ hu hv hai
    -- the external darts at `jc` are exactly the lifts of the chosen pair
    have hblock : ∃ j', G.molecule.IsBlock u.atoms jc j' := by
      rcases hjc with h | h
      · exact ⟨u.lower, h ▸ u.isBlock⟩
      · exact ⟨u.upper, h ▸ block_swap_joints _ u.isBlock⟩
    have hcard := joint_ext_card hM hblock.choose_spec
    set E := (G.molecule.dartsAt jc).filter (fun d => ¬ G.molecule.InGroup u.atoms d) with hE
    have hoE : (stSt γ (Mk := Mk) G σ).M.od oc ∈ E := by simp [hE, Molecule.dartsAt, hoc, hoc_ext]
    have hiE : (stSt γ (Mk := Mk) G σ).M.od ic ∈ E := by simp [hE, Molecule.dartsAt, hic, hic_ext]
    have hne : (stSt γ (Mk := Mk) G σ).M.od oc ≠ (stSt γ (Mk := Mk) G σ).M.od ic := by
      intro h
      have := congrArg (G.molecule.out) h
      rw [(stSt γ (Mk := Mk) G σ).M.od_out, (stSt γ (Mk := Mk) G σ).M.od_out, hoc_out, hic_out] at this
      cases this
    have hE2 : E = {(stSt γ (Mk := Mk) G σ).M.od oc, (stSt γ (Mk := Mk) G σ).M.od ic} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hoE
        · rw [Finset.mem_singleton.mp hd]; exact hiE
      · have : ({(stSt γ (Mk := Mk) G σ).M.od oc, (stSt γ (Mk := Mk) G σ).M.od ic} : Finset (GardenDart G)).card = 2 := Finset.card_pair hne
        omega
    -- the Fama.ChainL.joints of the unit are distinct
    have hul : u.upper ≠ u.lower := u.isBlock.2.2.2.1
    have hao' : G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od ao) ≠ jc := by
      intro h
      have : (stSt γ (Mk := Mk) G σ).M.od ao ∈ E := by simp [hE, Molecule.dartsAt, h, hao2]
      rw [hE2] at this
      rcases Finset.mem_insert.mp this with h' | h'
      · exact h1 ((stSt γ (Mk := Mk) G σ).M.od_inj h')
      · have := (stSt γ (Mk := Mk) G σ).M.od_inj (Finset.mem_singleton.mp h')
        rw [this] at hao_out; rw [hic_out] at hao_out; cases hao_out
    have hai' : G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od ai) ≠ jc := by
      intro h
      have : (stSt γ (Mk := Mk) G σ).M.od ai ∈ E := by simp [hE, Molecule.dartsAt, h, hai2]
      rw [hE2] at this
      rcases Finset.mem_insert.mp this with h' | h'
      · have := (stSt γ (Mk := Mk) G σ).M.od_inj h'
        rw [this] at hai_out; rw [hoc_out] at hai_out; cases hai_out
      · exact h2 ((stSt γ (Mk := Mk) G σ).M.od_inj (Finset.mem_singleton.mp h'))
    rcases hjc with hj | hj
    · refine ⟨u.lower, Or.inr rfl, ?_, ?_⟩
      · rcases hao3 with h | h
        · exact absurd (h.trans hj.symm) hao'
        · exact h
      · rcases hai3 with h | h
        · exact absurd (h.trans hj.symm) hai'
        · exact h
    · refine ⟨u.upper, Or.inl rfl, ?_, ?_⟩
      · rcases hao3 with h | h
        · exact h
        · exact absurd (h.trans hj.symm) hao'
      · rcases hai3 with h | h
        · exact h
        · exact absurd (h.trans hj.symm) hai'

/-- The joint-pair dichotomy: the out/in darts at a hinge either are the chosen proper pair or avoid it; in both cases
their lifts sit at one common joint of the unit. -/
theorem common_joint (hM : G.molecule.IsMolecule) (σ : Prescription G) {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ G σ)
    {v : GBranch (stSt γ G σ).G.tree} (hv : (stSt γ G σ).M.ob v = u.upper)
    {oc ic : GardenDart (stSt γ G σ).G} {jc : GBranch G.tree} (hjc : jc = u.upper ∨ jc = u.lower)
    (hoc : G.molecule.atom ((stSt γ G σ).M.od oc) = jc) (hic : G.molecule.atom ((stSt γ G σ).M.od ic) = jc)
    (hoc_ext : ¬ G.molecule.InGroup u.atoms ((stSt γ G σ).M.od oc))
    (hic_ext : ¬ G.molecule.InGroup u.atoms ((stSt γ G σ).M.od ic))
    (hoc_out : (stSt γ G σ).G.molecule.out oc = true) (hic_out : (stSt γ G σ).G.molecule.out ic = false)
    {ao ai : GardenDart (stSt γ G σ).G} (hao : (stSt γ G σ).G.molecule.atom ao = v)
    (hai : (stSt γ G σ).G.molecule.atom ai = v)
    (hao_out : (stSt γ G σ).G.molecule.out ao = true) (hai_out : (stSt γ G σ).G.molecule.out ai = false)
    (hxor : (ao = oc ∧ ai = ic) ∨ (ao ≠ oc ∧ ai ≠ ic)) :
    ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt γ G σ).M.od ao) = j ∧
      G.molecule.atom ((stSt γ G σ).M.od ai) = j := common_jointMk (Mk := ∅) hM σ hu hv hjc hoc hic hoc_ext hic_ext hoc_out hic_out hao hai hao_out hai_out hxor

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
