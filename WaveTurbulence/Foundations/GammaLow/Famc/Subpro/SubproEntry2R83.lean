/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproEntry2R83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntryR83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproEntry2R83
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
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
-- R83 port of sp-src/SubproEntry2.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): `entry_obj`, the entry of the gap specification of a group with a `C_1` object lies inside the object
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
open WaveTurbulence.VineA.NormalizedSplice.Subpro WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Fama.VineA WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The HV case: the designated object and the object of `C_1` share the canonical triple. -/
theorem entry_obj_hv (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) {O : Src.Object γ (stSt γ G σ).G.molecule} {A : Finset (GBranch G.tree)}
    (hOa : O.atoms = A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls))
    (hnm : ∀ z ∈ S, (stSt γ G σ).cls z = none → z ∈ A)
    (hhv : ∃ a b, Src.IsHV γ G.molecule S a b) (hnhvc : ¬ ∃ a b, Src.IsHVC γ G.molecule S a b)
    (hnone : (Fama.groupUnitsOf γ G S).skip = none)
    {a0 b0 : GBranch G.tree} {e0 : GardenDart G} (hpk : Fama.VineA.hvGroupPick γ G S = some (a0, b0, e0))
    (hup : O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls a0)
    {R0 : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower}
    (hR : O.shape = Src.VineLikeObject.hyper R0) (hRe : (stSt γ G σ).M.od R0.added = e0)
    {a : GBranch G.tree} (ha : Fama.VineA.NormalizedSplice.groupJoint γ G S = some a)
    {e : LocalGapSpecification (stSt γ G σ).G ((stSt γ G σ).M.pi (stSt γ G σ).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt γ G σ).M.od e.first = p.1) (h2 : (stSt γ G σ).M.od e.second = p.2)
    (hnh : (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∉ (stSt γ G σ).hinges → Fama.VineA.NormalizedSplice.intPairOrig γ G S = some p ∧ Fama.VineA.NormalizedSplice.IntSpec γ G S p) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt γ G σ).M.pi (stSt γ G σ).hcls a = O.upper ∨ (stSt γ G σ).M.pi (stSt γ G σ).hcls a = O.lower) := by
  have hunits : (Fama.groupUnitsOf γ G S).units = [] := (Fama.groupUnitsOf γ G S).hv_empty hhv hnhvc
  have hnotH : (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∉ (stSt γ G σ).hinges := by
    intro hh
    obtain ⟨-, u, hu, -⟩ := Fama.VineA.NormalizedSplice.hinge_unit hM σ hSm ha hh
    rw [hunits] at hu; cases hu
  obtain ⟨-, a1, Q, ha1, hQ, -, hT, hQ1, hQ2⟩ := hnh hnotH
  obtain ⟨a', ha', hdes⟩ := Fama.VineA.NormalizedSplice.designatedObject_isDesig hQ
  rw [ha] at ha1 ha'
  cases ha1; cases ha'
  obtain ⟨b, e', hpk', hQa, -, R1, hR1, hR1e⟩ := hdes.2.2.2.2.2.1 hnone hunits hhv hnhvc
  rw [hpk] at hpk'
  obtain ⟨h_a, h_b, h_e⟩ : a = a0 ∧ b = b0 ∧ e' = e0 := by
    have := Option.some.inj hpk'
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩
  subst h_a h_b h_e
  have hall : ∀ z ∈ S, (stSt γ G σ).cls z = none := fun z hz =>
    Fama.stSt_cls_none hM σ (Fama.VineA.NormalizedSplice.no_unit_hv hM σ hSm hhv hnhvc hz)
  have hcd : ∀ (f : GardenDart (stSt γ G σ).G) (q : GardenDart G), (stSt γ G σ).M.od f = q → Q.ContainsDart q →
      O.ContainsDart f := by
    intro f q hf hq
    unfold Src.Object.ContainsDart at hq
    rw [hR1] at hq
    obtain ⟨n1, n2, hg⟩ := hq
    rw [hQa] at hg
    refine containsDart_of_orig σ hOa (A := A) (by rw [hf]; exact ⟨hnm _ hg.1 (hall _ hg.1), hnm _ hg.2 (hall _ hg.2)⟩) ?_
    intro R' hR'
    rw [hR] at hR'
    have hRR : R' = R0 := (Src.VineLikeObject.hyper.inj hR').symm
    subst hRR
    rw [hRe, hf, ← hR1e]
    exact ⟨n1, n2⟩
  exact ⟨hcd _ _ h1 hQ1, hcd _ _ h2 hQ2, Or.inl hup.symm⟩

/-- B1b (Mk-general form of `hsh_skip`). -/
theorem hsh_skipMk (σ : Prescription G) {S : Finset (GBranch G.tree)} (sk : Fama.SkipData γ G S)
    {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule}
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ (Mk := Mk) G σ).M.od R.added = e)
    {f : GardenDart (stSt γ (Mk := Mk) G σ).G}
    (hbond : ∀ e, sk.bond = some e → (stSt γ (Mk := Mk) G σ).M.od f ≠ e ∧ (stSt γ (Mk := Mk) G σ).M.od f ≠ G.molecule.mate e) :
    ∀ R', O.shape = Src.VineLikeObject.hyper R' →
      (stSt γ (Mk := Mk) G σ).M.od f ≠ (stSt γ (Mk := Mk) G σ).M.od R'.added ∧
        (stSt γ (Mk := Mk) G σ).M.od f ≠ G.molecule.mate ((stSt γ (Mk := Mk) G σ).M.od R'.added) := by
  intro R' hR'
  rcases hb : sk.bond with _ | e
  · obtain ⟨h, hh⟩ := hsh1 hb
    rw [hh] at hR'; cases hR'
  · obtain ⟨R'', hR'', hRe⟩ := hsh2 e hb
    rw [hR''] at hR'
    have : R'' = R' := Src.VineLikeObject.hyper.inj hR'
    subst this
    rw [hRe]
    exact hbond e hb

theorem hsh_skip (σ : Prescription G) {S : Finset (GBranch G.tree)} (sk : Fama.SkipData γ G S)
    {O : Src.Object γ (stSt γ G σ).G.molecule}
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e)
    {f : GardenDart (stSt γ G σ).G}
    (hbond : ∀ e, sk.bond = some e → (stSt γ G σ).M.od f ≠ e ∧ (stSt γ G σ).M.od f ≠ G.molecule.mate e) :
    ∀ R', O.shape = Src.VineLikeObject.hyper R' →
      (stSt γ G σ).M.od f ≠ (stSt γ G σ).M.od R'.added ∧
        (stSt γ G σ).M.od f ≠ G.molecule.mate ((stSt γ G σ).M.od R'.added) := hsh_skipMk (Mk := ∅) σ sk hsh1 hsh2 hbond

theorem x_mem_A {S : Finset (GBranch G.tree)} (sk : Fama.SkipData γ G S) : sk.x ∈ sk.A ∧ sk.y ∈ sk.A := by
  have hX := sk.vine
  exact ⟨(Src.isBlock_of_isSomeVine hX).2.1, (Src.isBlock_of_isSomeVine hX).2.2.1⟩

/-- B1b (Mk-general form of `entry_obj_hinge`). -/
theorem entry_obj_hingeMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : Fama.SkipData γ G S) (hsk : (Fama.groupUnitsOf γ G S).skip = some sk)
    {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls))
    (hup : O.upper = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.x) (hlo : O.lower = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.y)
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ (Mk := Mk) G σ).M.od R.added = e)
    {a : GBranch G.tree}
    {e : LocalGapSpecification (stSt γ (Mk := Mk) G σ).G ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt γ (Mk := Mk) G σ).M.od e.first = p.1) (h2 : (stSt γ (Mk := Mk) G σ).M.od e.second = p.2)
    (hsp : Fama.VineA.NormalizedSplice.HingeSpec γ G S a p) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls a = O.upper ∨ (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls a = O.lower) := by
  obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩ := hsp
  obtain ⟨hjxy, hm1, hm2, hbond⟩ := hrel.1 sk hsk
  obtain ⟨hxA, hyA⟩ := x_mem_A sk
  have hjA : j ∈ sk.A := by rcases hjxy with rfl | rfl; exact hxA; exact hyA
  have hg1 : G.molecule.InGroup sk.A p.1 := ⟨hT.1 ▸ hjA, hm1⟩
  have hg2 : G.molecule.InGroup sk.A p.2 := ⟨hT.2.1 ▸ hjA, hm2⟩
  refine ⟨containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h1]; exact hg1)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h1]; exact ⟨(hbond e' he').1, (hbond e' he').2.1⟩)),
    containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h2]; exact hg2)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h2]; exact ⟨(hbond e' he').2.2.1, (hbond e' he').2.2.2⟩)), ?_⟩
  have hat : (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls a = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls j := by
    rw [← e.at_first, (atom_eq_piMk (Mk := Mk) σ e.first).1, h1, hT.1]
  rw [hat]
  rcases hjxy with rfl | rfl
  · exact Or.inl hup.symm
  · exact Or.inr hlo.symm

/-- The merged-first-joint case: a pair of the skipped vine at a hinge. -/
theorem entry_obj_hinge (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : Fama.SkipData γ G S) (hsk : (Fama.groupUnitsOf γ G S).skip = some sk)
    {O : Src.Object γ (stSt γ G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls))
    (hup : O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.x) (hlo : O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.y)
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e)
    {a : GBranch G.tree}
    {e : LocalGapSpecification (stSt γ G σ).G ((stSt γ G σ).M.pi (stSt γ G σ).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt γ G σ).M.od e.first = p.1) (h2 : (stSt γ G σ).M.od e.second = p.2)
    (hsp : Fama.VineA.NormalizedSplice.HingeSpec γ G S a p) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt γ G σ).M.pi (stSt γ G σ).hcls a = O.upper ∨ (stSt γ G σ).M.pi (stSt γ G σ).hcls a = O.lower) := entry_obj_hingeMk (Mk := ∅) hM σ sk hsk hOa hup hlo hsh1 hsh2 h1 h2 hsp

/-- A non-hinge group joint of a group with a skipped vine has `L0 = ∅` and `x = a`. -/
theorem left_trivial (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    (sk : Fama.SkipData γ G S) (hsk : (Fama.groupUnitsOf γ G S).skip = some sk)
    (hnh : (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.a ∉ (stSt γ G σ).hinges) : sk.x = sk.a := by
  rcases sk.left with ⟨-, hx⟩ | ⟨-, haL, -, -⟩
  · exact hx
  · exfalso
    apply hnh
    rcases ((Fama.groupUnitsOf γ G S).skip_units sk hsk).2.1 with h0 | ⟨u, hu, hL⟩
    · rw [h0] at haL; cases haL
    · have hau : sk.a ∈ u.atoms := hL ▸ haL
      have huB : u ∈ Fama.unitBlocks γ G σ := Fama.mem_unitBlocks.mpr ⟨S, hSm, hσ, hu⟩
      rw [(stSt γ G σ).mem_hinges, (stSt γ G σ).M.ob_pi, Fama.stSt_repC_mem hM σ huB hau,
        Fama.stSt_cls_mem hM σ huB u.isBlock.2.1]
      simp

theorem entry_obj_nonhinge (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    (sk : Fama.SkipData γ G S) (hsk : (Fama.groupUnitsOf γ G S).skip = some sk)
    {O : Src.Object γ (stSt γ G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls))
    (hup : O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.x)
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e)
    {a : GBranch G.tree} (ha : Fama.VineA.NormalizedSplice.groupJoint γ G S = some a)
    {e : LocalGapSpecification (stSt γ G σ).G ((stSt γ G σ).M.pi (stSt γ G σ).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt γ G σ).M.od e.first = p.1) (h2 : (stSt γ G σ).M.od e.second = p.2)
    (hnh : (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∉ (stSt γ G σ).hinges → Fama.VineA.NormalizedSplice.intPairOrig γ G S = some p ∧ Fama.VineA.NormalizedSplice.IntSpec γ G S p)
    (hnotH : (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∉ (stSt γ G σ).hinges) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt γ G σ).M.pi (stSt γ G σ).hcls a = O.upper ∨ (stSt γ G σ).M.pi (stSt γ G σ).hcls a = O.lower) := by
  have haa : a = sk.a := (Fama.VineA.NormalizedSplice.groupJoint_spec ha).1 sk hsk
  subst haa
  have hxa := left_trivial hM σ hSm hσ sk hsk hnotH
  obtain ⟨-, a1, Q, ha1, hQ, -, hT, hQ1, hQ2⟩ := hnh hnotH
  obtain ⟨a', ha', hdes⟩ := Fama.VineA.NormalizedSplice.designatedObject_isDesig hQ
  rw [ha] at ha1 ha'
  cases ha1; cases ha'
  -- the darts of `p` at `a` that are in `S` are in `A`
  have key : ∀ q : GardenDart G, G.molecule.atom q = sk.a → Q.ContainsDart q →
      (∀ e', sk.bond = some e' → q ≠ e' ∧ q ≠ G.molecule.mate e') ∧ G.molecule.InGroup sk.A q := by
    intro q hq hQq
    rcases hb : sk.bond with _ | e'
    · obtain ⟨hQS, hv, hsh⟩ := hdes.2.2.1 sk hsk hb
      unfold Src.Object.ContainsDart at hQq
      rw [hsh] at hQq
      dsimp only at hQq
      refine ⟨(fun e' he' => by cases he'), ?_⟩
      have := skel_darts_in_A (sk.skelM hb) hxa (d := q) hq (by rw [hQS] at hQq; exact hQq)
      exact this
    · obtain ⟨hQS, R1, hR1, hR1e⟩ := hdes.2.2.2.1 sk e' hsk hb
      unfold Src.Object.ContainsDart at hQq
      rw [hR1] at hQq
      obtain ⟨n1, n2, hg⟩ := hQq
      rw [hR1e] at n1 n2
      refine ⟨fun e'' he'' => ?_, ?_⟩
      · cases he''; exact ⟨n1, n2⟩
      · have := skel_darts_in_A (sk.skelN e' hb) hxa (d := ⟨q, n1, n2⟩) hq (by rw [hQS] at hg; exact hg)
        exact this
  obtain ⟨b1, g1⟩ := key p.1 hT.1 hQ1
  obtain ⟨b2, g2⟩ := key p.2 hT.2.1 hQ2
  refine ⟨containsDart_of_orig σ hOa (by rw [h1]; exact g1)
      (hsh_skip σ sk hsh1 hsh2 (by intro e' he'; rw [h1]; exact b1 e' he')),
    containsDart_of_orig σ hOa (by rw [h2]; exact g2)
      (hsh_skip σ sk hsh1 hsh2 (by intro e' he'; rw [h2]; exact b2 e' he')), ?_⟩
  rw [hxa] at hup
  exact Or.inl hup.symm

/-- **The entry of the gap specification of a group with an object `O` of `C_1` lies inside `O`**, at a joint of `O`. -/
theorem entry_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG) {O : Src.Object γ (stSt γ G σ).G.molecule}
    (hO : Fama.VineA.NormalizedSplice.objOf γ G σ S = some O) :
    ∃ a, Fama.VineA.NormalizedSplice.groupJoint γ G S = some a ∧
      ∃ e : LocalGapSpecification (stSt γ G σ).G ((stSt γ G σ).M.pi (stSt γ G σ).hcls a),
        Fama.VineA.NormalizedSplice.gapSpecification γ G σ ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) = some e ∧ e.kind = σ S ∧
        O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
        ((stSt γ G σ).M.pi (stSt γ G σ).hcls a = O.upper ∨ (stSt γ G σ).M.pi (stSt γ G σ).hcls a = O.lower) := by
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := Fama.VineA.NormalizedSplice.gapSpecification_group hM σ hSm
  obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_spec (Option.mem_def.mpr hO)
  obtain ⟨A, hAS, hOa, hnm, hsrc⟩ := hSpec.src
  refine ⟨a, ha, e, he, hk, ?_⟩
  rcases hsrc with ⟨⟨hhv, hnhvc⟩, hnone, a0, b0, e0, hpk, hup, hlo, R0, hR, hRe⟩ |
      ⟨sk, hsk, hAeq, hup, hlo, hsh1, hsh2⟩
  · exact entry_obj_hv hM σ hSm hOa hnm hhv hnhvc hnone hpk hup hR hRe ha h1 h2 hnh.2
  · subst hAeq
    by_cases hh : (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∈ (stSt γ G σ).hinges
    · exact entry_obj_hinge hM σ sk hsk hOa hup hlo hsh1 hsh2 h1 h2 (hnh.1 hh).2
    · exact entry_obj_nonhinge hM σ hSm hσ sk hsk hOa hup hsh1 hsh2 ha h1 h2 hnh.2 hh

/-- B1b (Mk-general form of `hinge_dart_obj`). -/
theorem hinge_dart_objMk (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : Fama.SkipData γ G S) (hsk : (Fama.groupUnitsOf γ G S).skip = some sk)
    {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls))
    (hup : O.upper = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.x) (hlo : O.lower = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.y)
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ (Mk := Mk) G σ).M.od R.added = e)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hsp : Fama.VineA.NormalizedSplice.HingeSpec γ G S a p)
    {f1 f2 : GardenDart (stSt γ (Mk := Mk) G σ).G} (h1 : (stSt γ (Mk := Mk) G σ).M.od f1 = p.1) (h2 : (stSt γ (Mk := Mk) G σ).M.od f2 = p.2) :
    O.ContainsDart f1 ∧ O.ContainsDart f2 ∧
      ((stSt γ (Mk := Mk) G σ).G.molecule.atom f1 = O.upper ∨ (stSt γ (Mk := Mk) G σ).G.molecule.atom f1 = O.lower) := by
  obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩ := hsp
  obtain ⟨hjxy, hm1, hm2, hbond⟩ := hrel.1 sk hsk
  obtain ⟨hxA, hyA⟩ := x_mem_A sk
  have hjA : j ∈ sk.A := by rcases hjxy with rfl | rfl; exact hxA; exact hyA
  have hg1 : G.molecule.InGroup sk.A p.1 := ⟨hT.1 ▸ hjA, hm1⟩
  have hg2 : G.molecule.InGroup sk.A p.2 := ⟨hT.2.1 ▸ hjA, hm2⟩
  refine ⟨containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h1]; exact hg1)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h1]; exact ⟨(hbond e' he').1, (hbond e' he').2.1⟩)),
    containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h2]; exact hg2)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h2]; exact ⟨(hbond e' he').2.2.1, (hbond e' he').2.2.2⟩)), ?_⟩
  rw [(atom_eq_piMk (Mk := Mk) σ f1).1, h1, hT.1]
  rcases hjxy with rfl | rfl
  · exact Or.inl hup.symm
  · exact Or.inr hlo.symm

/-- The darts of a `Fama.VineA.NormalizedSplice.HingeSpec` pair of a unit of a skipped-vine group lie inside the residual object, at a joint. -/
theorem hinge_dart_obj (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : Fama.SkipData γ G S) (hsk : (Fama.groupUnitsOf γ G S).skip = some sk)
    {O : Src.Object γ (stSt γ G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls))
    (hup : O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.x) (hlo : O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.y)
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hsp : Fama.VineA.NormalizedSplice.HingeSpec γ G S a p)
    {f1 f2 : GardenDart (stSt γ G σ).G} (h1 : (stSt γ G σ).M.od f1 = p.1) (h2 : (stSt γ G σ).M.od f2 = p.2) :
    O.ContainsDart f1 ∧ O.ContainsDart f2 ∧
      ((stSt γ G σ).G.molecule.atom f1 = O.upper ∨ (stSt γ G σ).G.molecule.atom f1 = O.lower) := hinge_dart_objMk (Mk := ∅) σ sk hsk hOa hup hlo hsh1 hsh2 hsp h1 h2

/-- If a hinge is a joint of an object of `C_1`, the group of its unit has a skipped vine and the object is its image. -/
theorem obj_skip_data (hM : G.molecule.IsMolecule) (σ : Prescription G) {O : Src.Object γ (stSt γ G σ).G.molecule}
    (hOm : O ∈ Fama.VineA.NormalizedSplice.objects γ G σ) {v : GBranch (stSt γ G σ).G.tree} (hvO : v ∈ O.atoms)
    {S : Finset (GBranch G.tree)} (hSm : S ∈ maximalGroupsG γ G.molecule) {u : CLBlock G}
    (hu : u ∈ (Fama.groupUnitsOf γ G S).units) (hob : (stSt γ G σ).M.ob v = u.upper) :
    ∃ sk : Fama.SkipData γ G S, (Fama.groupUnitsOf γ G S).skip = some sk ∧
      O.atoms = sk.A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls) ∧
      O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.x ∧ O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.y ∧
      (sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h) ∧
      (∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e) := by
  obtain ⟨S', -, hS'm, hO'⟩ := mem_objects' hOm
  obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_spec (Option.mem_def.mpr hO')
  obtain ⟨z, hz, hvz⟩ := hSpec.atoms_sub v hvO
  have h1 : repC (stSt γ G σ).cls z ∈ S' := Fama.VineA.NormalizedSplice.repC_mem_group hM σ hS'm hz
  have h2 : (stSt γ G σ).M.ob v = repC (stSt γ G σ).cls z := by rw [hvz, (stSt γ G σ).M.ob_pi]
  have h3 : u.upper ∈ S := (Fama.groupUnitsOf γ G S).sub u hu u.isBlock.2.1
  have hSS : S' = S := by
    by_contra hne
    rw [h2] at hob
    exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS'm hSm hne) h1 (hob ▸ h3)
  subst hSS
  obtain ⟨A, -, hOa, -, hsrc⟩ := hSpec.src
  rcases hsrc with ⟨⟨hhv, hnh⟩, -⟩ | ⟨sk, hsk, hAeq, hup, hlo, hsh1, hsh2⟩
  · have := (Fama.groupUnitsOf γ G S').hv_empty hhv hnh
    rw [this] at hu; cases hu
  · subst hAeq
    exact ⟨sk, hsk, hOa, hup, hlo, hsh1, hsh2⟩

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
