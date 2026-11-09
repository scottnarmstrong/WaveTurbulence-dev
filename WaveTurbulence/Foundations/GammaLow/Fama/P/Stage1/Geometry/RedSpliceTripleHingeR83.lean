/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleHingeR83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceTripleDesigR83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleHingeR83
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
-- R83 port of rs-src/RedSpliceTripleHinge.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# REDSPLICE-DEF (S2a), R37: `hingePair` lies in every triple bond at its hinge

`triple_in_hingePair`: if a hinge `v` of `G_sb` has a triple bond to `c`, then `hingePair γ G σ v = some (x, y)` and the two
bonds `x`, `y` (a `TripleAt` pair at `v`) both lead to `c`.  The whole-group case uses the `HingeBest` choice of
`hingeOrigPair` (`whole_pair_in_triple`); the case of a unit of a skipped vine uses that the `HingeSpec` pair is forced
(`skip_pair_in_triple`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem group_eq_of_mem (hM : G.molecule.IsMolecule) {S S' : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroupsG γ G.molecule) (hS' : S' ∈ maximalGroupsG γ G.molecule) {u u' : CLBlock G}
    (hu : u ∈ (groupUnitsOf γ G S).units) (hu' : u' ∈ (groupUnitsOf γ G S').units) {z : GBranch G.tree}
    (hz : z ∈ u.atoms) (hz' : z ∈ u'.atoms) : S = S' := by
  by_contra hne
  exact Finset.disjoint_left.mp (groups_disjoint hM hS hS' hne) ((groupUnitsOf γ G S).sub u hu hz)
    ((groupUnitsOf γ G S').sub u' hu' hz')

theorem od_mem_tripleDarts (σ : Prescription G) {v c : GBranch (stSt γ G σ).G.tree}
    {x : GardenDart (stSt γ G σ).G} (h : (stSt γ G σ).M.od x ∈ tripleDarts γ G σ v c) :
    (stSt γ G σ).G.molecule.atom x = v ∧ (stSt γ G σ).G.molecule.atom ((stSt γ G σ).G.molecule.mate x) = c := by
  unfold tripleDarts at h
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h
  have := (stSt γ G σ).M.od_inj hyx
  subst this
  rw [Finset.mem_filter, Mole.mem_dartsAt] at hy
  exact hy

section glue
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

/-- B1b (Mk-general form of `hinge_crown`). -/
theorem hinge_crownMk {Mk : Set (CLVineG γ _)} {v : GBranch (stSt γ (Mk := Mk) G σ).G.tree} (hv : v ∈ (stSt γ (Mk := Mk) G σ).hinges) :
    ∃ u ∈ unitBlocks γ (Mk := Mk) G σ, (stSt γ (Mk := Mk) G σ).M.ob v = u.upper := by
  have hcn := ((stSt γ (Mk := Mk) G σ).mem_hinges v).mp hv
  by_cases h : ∃ u ∈ unitBlocks γ (Mk := Mk) G σ, (stSt γ (Mk := Mk) G σ).M.ob v ∈ u.atoms
  swap
  · push Not at h
    exact absurd (stSt_cls_noneMk (Mk := Mk) hM σ h) hcn
  obtain ⟨u, hu, hvu⟩ := h
  have h1 := stSt_cls_memMk (Mk := Mk) hM σ hu hvu
  refine ⟨u, hu, ?_⟩
  have := ((stSt γ (Mk := Mk) G σ).M.ob_range ((stSt γ (Mk := Mk) G σ).M.ob v)).mp ⟨v, rfl⟩
  rcases this with h3 | h3
  · rw [h1] at h3; cases h3
  · rw [h1] at h3; exact (Option.some.inj h3).symm

/-- A hinge is the crown of a spliced unit. -/
theorem hinge_crown {v : GBranch (stSt γ G σ).G.tree} (hv : v ∈ (stSt γ G σ).hinges) :
    ∃ u ∈ unitBlocks γ G σ, (stSt γ G σ).M.ob v = u.upper := hinge_crownMk (Mk := ∅) hM σ hv

/-- B1b (Mk-general form of `hinge_ne`). -/
theorem hinge_neMk {u : CLBlock G} {Mk : Set (CLVineG γ _)} (hu : u ∈ unitBlocks γ (Mk := Mk) G σ) {v c : GBranch (stSt γ (Mk := Mk) G σ).G.tree}
    (hcr : (stSt γ (Mk := Mk) G σ).M.ob v = u.upper) (h3 : (stSt γ (Mk := Mk) G σ).G.molecule.bondsBetween v c = 3) : v ≠ c := by
  intro hvc
  subst hvc
  have hpos : 0 < (stSt γ (Mk := Mk) G σ).G.molecule.bondsBetween v v := by rw [h3]; norm_num
  unfold Molecule.bondsBetween at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hx
  have h2 := hx.2
  unfold Molecule.ends at h2
  have hx1 : (stSt γ (Mk := Mk) G σ).G.molecule.atom x = v ∧ (stSt γ (Mk := Mk) G σ).G.molecule.atom ((stSt γ (Mk := Mk) G σ).G.molecule.mate x) = v := by
    rcases Sym2.eq_iff.mp h2 with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨a, b⟩
    · exact ⟨a, b⟩
  obtain ⟨hin, hn⟩ := od_extMk (Mk := Mk) hM σ hu hcr hx1.1
  obtain ⟨hin2, -⟩ := od_extMk (Mk := Mk) hM σ hu hcr hx1.2
  apply hn
  refine ⟨hin, ?_⟩
  rw [← (stSt γ (Mk := Mk) G σ).M.od_mate]
  exact hin2

/-- No bond of `G_sb` joins a hinge to itself. -/
theorem hinge_ne {u : CLBlock G} (hu : u ∈ unitBlocks γ G σ) {v c : GBranch (stSt γ G σ).G.tree}
    (hcr : (stSt γ G σ).M.ob v = u.upper) (h3 : (stSt γ G σ).G.molecule.bondsBetween v c = 3) : v ≠ c := hinge_neMk (Mk := ∅) hM σ hu hcr h3

/-- **R37 (S2a).**  If a hinge `v` of `G_sb` has a triple bond to `c`, the hinge pair `(ℓ_1, ℓ_2)` of `v` (TARGET subpro (5);
`hingePair`) consists of two bonds of that triple bond. -/
theorem triple_in_hingePair {v c : GBranch (stSt γ G σ).G.tree} (hv : v ∈ (stSt γ G σ).hinges)
    (h3 : (stSt γ G σ).G.molecule.bondsBetween v c = 3) :
    ∃ x y, hingePair γ G σ v = some (x, y) ∧ TripleAt (stSt γ G σ).G v x y ∧
      (stSt γ G σ).G.molecule.atom ((stSt γ G σ).G.molecule.mate x) = c ∧
      (stSt γ G σ).G.molecule.atom ((stSt γ G σ).G.molecule.mate y) = c := by
  classical
  obtain ⟨u, hu, hcr⟩ := hinge_crown hM σ hv
  obtain ⟨S, hSm, hσ, hmem⟩ := mem_unitBlocks.mp hu
  have hvc := hinge_ne hM σ hu hcr h3
  rcases hsk : (groupUnitsOf γ G S).skip with _ | sk
  · -- a whole-group unit
    have hUS := (groupUnitsOf γ G S).noskip_units hsk u hmem
    obtain ⟨a0, ha0⟩ := exists_groupJoint_eq hSm
    have ha0u : a0 ∈ u.atoms := hUS ▸ (groupJoint_kind ha0).1
    obtain ⟨p, hp, hbest⟩ := hingeOrigPair_best ha0 ⟨u, hmem, ha0u⟩
    obtain ⟨j, hj, hT, hn1, hn2, -, hrel⟩ := hingeSpec_body hM hSm hbest.1 hmem ha0u
    obtain ⟨-, hjw⟩ := hrel hsk
    obtain ⟨y1, y2, hy1, hy2, hP⟩ := ext_lift_darts hM σ hu hcr hj hjw hT.1 hT.2.1 hn1 hn2 hT.2.2.2
    obtain ⟨q, hq, hq1, hq2, hqT⟩ :=
      liftPair_of_exists (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hP.1⟩
    have hat : (stSt γ G σ).M.pi (stSt γ G σ).hcls a0 = v := by
      apply (stSt γ G σ).M.ob_inj
      rw [(stSt γ G σ).M.ob_pi (stSt γ G σ).hcls a0, hcr]
      exact stSt_repC_mem hM σ hu ha0u
    have hga : groupAtom γ G σ S = some v := by
      unfold groupAtom; rw [ha0]; simp [hat]
    have hentry : hingeEntryPair γ G σ S v = some q := by
      unfold hingeEntryPair; rw [hp]; exact hq
    have hPP : ProperPair γ G σ v q.1 q.2 :=
      properPair_congr hP (by rw [hq1, hy1]) (by rw [hq2, hy2]) hqT
    have hex : ∃ p' : GardenDart (stSt γ G σ).G × GardenDart (stSt γ G σ).G, ∃ S' ∈ maximalGroupsG γ G.molecule,
        groupAtom γ G σ S' = some v ∧ hingeEntryPair γ G σ S' v = some p' ∧ ProperPair γ G σ v p'.1 p'.2 :=
      ⟨q, S, hSm, hga, hentry, hPP⟩
    have hdef : hingePair γ G σ v = some (Classical.choose hex) := by
      unfold hingePair; rw [dif_neg (not_exists_survPairAt_empty σ v), dif_pos hex]
    obtain ⟨S'', hS''m, hga'', hent'', hP''⟩ := Classical.choose_spec hex
    have hSS : S = S'' := groupAtom_inj hM σ hSm hS''m hga hga''
    subst hSS
    rw [hentry] at hent''
    have hqq : q = Classical.choose hex := Option.some.inj hent''
    have hX := whole_pair_in_triple hM σ hSm hσ hmem hsk hcr hvc h3 ha0u hbest
    have e1 := od_mem_tripleDarts σ (hq1 ▸ hX.1)
    have e2 := od_mem_tripleDarts σ (hq2 ▸ hX.2)
    refine ⟨(Classical.choose hex).1, (Classical.choose hex).2, hdef, hP''.1, ?_, ?_⟩
    · rw [← hqq]; exact e1.2
    · rw [← hqq]; exact e2.2
  · -- a unit of a skipped vine
    obtain ⟨x, y, hxy, hPP, ⟨S', hS', u', hu', hob', p, hsp, hox, hoy⟩, -⟩ := hingePair_spec hM σ hv
    have hz : u.upper ∈ u'.atoms := by
      have : u.upper = u'.upper := hcr.symm.trans hob'
      rw [this]; exact u'.isBlock.2.1
    obtain rfl := group_eq_of_mem hM hSm hS' hmem hu' u.isBlock.2.1 hz
    obtain rfl := unit_eq_any hM hSm hSm hmem hu' u.isBlock.2.1 hz
    have hX := skip_pair_in_triple hM σ hSm hσ hmem hsk hcr hvc h3 u.isBlock.2.1 hsp
    have e1 := od_mem_tripleDarts σ (hox ▸ hX.1)
    have e2 := od_mem_tripleDarts σ (hoy ▸ hX.2)
    exact ⟨x, y, hxy, hPP.1, e1.2, e2.2⟩

end glue

end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
