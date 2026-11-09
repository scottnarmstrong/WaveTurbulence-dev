/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceColl` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceObj2
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceColl
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport


/-!
# R83 successor copy: the normalized collection `C_1`

Source copy: pinned/r83-RedSpliceColl.lean; hash recorded in COPIED-SHA256SUMS.

For every SG group `S` of `𝒞` that is an HV, or has a skipped ingredient, `exists_obj` produces the residual
object in `G_sb` (an HV; a (CN) vine; a root (CL) vine) with the properties used for
`Src.SubproChoices.Structural` and `hingeOutsideFirst`: allowed, supported on the image of `S`, and hinge atoms
occur in it only as joints.  `objects γ G σ` is the list of these objects.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem groups_disjoint (hM : G.molecule.IsMolecule) :
    (maximalGroupsG γ G.molecule).Pairwise (fun S T => Disjoint S T) := by
  have hpart := partition_eq_maximalGroups (maximalGroupsG_partition (γ := γ) hM)
  have := (maximalGroupsG_partition (γ := γ) hM).2.1
  rwa [hpart] at this

/-- B1b (Mk-general form of `repC_mem_group`). -/
theorem repC_mem_groupMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) {z : GBranch G.tree} (hz : z ∈ S) {Mk : Set (CLVineG γ _)} :
    repC (stSt γ (Mk := Mk) G σ).cls z ∈ S := by
  by_cases h : ∃ u ∈ unitBlocks γ (Mk := Mk) G σ, z ∈ u.atoms
  · obtain ⟨u, hu, hzu⟩ := h
    rw [stSt_repC_memMk (Mk := Mk) hM σ hu hzu]
    obtain ⟨S'', hS''m, _, hu''⟩ := (mem_unitBlocksMk (Mk := Mk)).mp hu
    have hsub := groupUnitsMk_sub (Mk := Mk) (u := u) hu''
    by_cases hSS : S'' = S
    · subst hSS
      exact hsub u.isBlock.2.1
    · exact absurd hz (Finset.disjoint_left.mp (groups_disjoint hM hS''m hSm hSS) (hsub hzu)).elim
  · push Not at h
    rw [stSt_repC_noneMk (Mk := Mk) hM σ h]
    exact hz

/-- The crown of an atom of a group lies in the group. -/
theorem repC_mem_group (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) {z : GBranch G.tree} (hz : z ∈ S) :
    repC (stSt γ G σ).cls z ∈ S := repC_mem_groupMk (Mk := ∅) hM σ hSm hz

/-- An SG group contributes an object to `C_1`. -/
@[expose] def HasObj (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  ((∃ a b, Src.IsHV γ G.molecule S a b) ∧ ¬ ∃ a b, Src.IsHVC γ G.molecule S a b) ∨
    ∃ sk : SkipData γ G S, (groupUnitsOf γ G S).skip = some sk

/-- The properties of the object of the group `S` in `G_sb` (B1a: for the marked vine set `Mk`). -/
structure ObjSpecMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree)) (Mk : Set (CLVineG γ G))
    (O : Src.Object γ (stSt γ G σ Mk).G.molecule) : Prop where
  allowed : Src.AllowedCollectionObject γ (stSt γ G σ Mk).G O
  atoms_sub : ∀ v ∈ O.atoms, ∃ z ∈ S, v = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls z
  hinge : ∀ c, (stSt γ G σ Mk).cls ((stSt γ G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower
  /-- SUBPRO amendment A2: the atoms of the object are exactly the image of a subset `A` of the group, and every
  unmerged atom of the group lies in `A` -/
  src : ∃ A : Finset (GBranch G.tree), A ⊆ S ∧ O.atoms = A.image ((stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls) ∧
    (∀ z ∈ S, (stSt γ G σ Mk).cls z = none → z ∈ A) ∧
    ((((∃ a b, Src.IsHV γ G.molecule S a b) ∧ ¬ ∃ a b, Src.IsHVC γ G.molecule S a b) ∧
        (groupUnitsOf γ G S).skip = none ∧
        ∃ a b e, hvGroupPick γ G S = some (a, b, e) ∧ O.upper = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls a ∧
          O.lower = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls b ∧
          ∃ R : Src.HyperLikeRealization γ (stSt γ G σ Mk).G.molecule O.atoms O.upper O.lower,
            O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ Mk).M.od R.added = e) ∨
      ∃ sk : SkipData γ G S, (groupUnitsOf γ G S).skip = some sk ∧ A = sk.A ∧
        O.upper = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls sk.x ∧ O.lower = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls sk.y ∧
        (sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h) ∧
        ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ G σ Mk).G.molecule O.atoms O.upper O.lower,
          O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ Mk).M.od R.added = e)

/-- The properties of the object of the group `S` in `G_sb` (main's, at the default marked set `∅`).  B1a: the
Mk-general structure is `ObjSpecMk`; the object's type depends on the marked set, so the default cannot be a trailing
argument here. -/
abbrev ObjSpec (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    (O : Src.Object γ (stSt γ G σ).G.molecule) : Prop :=
  ObjSpecMk γ G σ S ∅ O


/-- B1b (Mk-general form of `objSpec_of_skip`). -/
theorem objSpec_of_skipMk (_hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : SkipData γ G S) {Mk : Set (CLVineG γ _)} (O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule)
    (hO : Src.AllowedCollectionObject γ (stSt γ (Mk := Mk) G σ).G O)
    (hOa : O.atoms = sk.A.image ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls))
    (hu : O.upper = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.x)
    (hl : O.lower = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.y)
    (hcase : ∀ z ∈ sk.A, (stSt γ (Mk := Mk) G σ).cls (((stSt γ (Mk := Mk) G σ).cls z).getD z) ≠ none → z = sk.x ∨ z = sk.y)
    (hnm : ∀ z ∈ S, (stSt γ (Mk := Mk) G σ).cls z = none → z ∈ sk.A) (hsk : (groupUnitsOf γ G S).skip = some sk)
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ (Mk := Mk) G σ).M.od R.added = e) :
    ObjSpecMk γ (Mk := Mk) G σ S O := by
  have hc := (stSt γ (Mk := Mk) G σ).hcls
  refine ⟨hO, ?_, ?_, ⟨sk.A, ?_, hOa, hnm, Or.inr ⟨sk, hsk, rfl, hu, hl, hsh1, hsh2⟩⟩⟩
  · intro v hv
    rw [hOa] at hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    have hzS : z ∈ S := by
      rw [sk.hS]
      exact mem_union_left _ (mem_union_right _ hz)
    exact ⟨z, hzS, rfl⟩
  · intro c hcn hcO
    rw [hOa] at hcO
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hcO
    rw [(stSt γ (Mk := Mk) G σ).M.ob_pi hc] at hcn
    rcases hcase z hz hcn with rfl | rfl
    · exact Or.inl hu.symm
    · exact Or.inr hl.symm
  · intro z hz
    rw [sk.hS]
    exact mem_union_left _ (mem_union_right _ hz)

theorem objSpec_of_skip (_hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : SkipData γ G S) (O : Src.Object γ (stSt γ G σ).G.molecule)
    (hO : Src.AllowedCollectionObject γ (stSt γ G σ).G O)
    (hOa : O.atoms = sk.A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls))
    (hu : O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.x)
    (hl : O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.y)
    (hcase : ∀ z ∈ sk.A, (stSt γ G σ).cls (((stSt γ G σ).cls z).getD z) ≠ none → z = sk.x ∨ z = sk.y)
    (hnm : ∀ z ∈ S, (stSt γ G σ).cls z = none → z ∈ sk.A) (hsk : (groupUnitsOf γ G S).skip = some sk)
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e) :
    ObjSpec γ G σ S O := objSpec_of_skipMk (Mk := ∅) _hM σ sk O hO hOa hu hl hcase hnm hsk hsh1 hsh2

theorem exists_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : HasObj γ G S) :
    ∃ O, ObjSpec γ G σ S O := by
  have hc := (stSt γ G σ).hcls
  have hsk_or : (((∃ a b, Src.IsHV γ G.molecule S a b) ∧
      ¬ ∃ a b, Src.IsHVC γ G.molecule S a b) ∧ (groupUnitsOf γ G S).skip = none) ∨
      ∃ sk : SkipData γ G S, (groupUnitsOf γ G S).skip = some sk := by
    rcases h with hl | hr
    · rcases hs : (groupUnitsOf γ G S).skip with _ | sk
      · exact Or.inl ⟨hl, rfl⟩
      · exact Or.inr ⟨sk, rfl⟩
    · exact Or.inr hr
  rcases hsk_or with ⟨⟨⟨a, b, hhv⟩, hnhvc⟩, hnone⟩ | ⟨sk, hsk⟩
  · obtain ⟨a0, b0, e0, hpk, hends, hvine⟩ := hvGroupPick_some ⟨hSm, ⟨a, b, hhv⟩, hnhvc⟩
    obtain ⟨O, hO, hOa, hou, hol, R, hR, hRe⟩ := hv_object hM σ hSm hnhvc hends hvine
    refine ⟨O, hO, ?_, ?_, ⟨S, subset_refl _, hOa, fun z hz _ => hz,
      Or.inl ⟨⟨⟨a, b, hhv⟩, hnhvc⟩, hnone, a0, b0, e0, hpk, hou, hol, R, hR, hRe⟩⟩⟩
    · intro v hv
      rw [hOa] at hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨z, hz, rfl⟩
    · intro c hcn hcO
      exfalso
      rw [hOa] at hcO
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hcO
      apply hcn
      rw [(stSt γ G σ).M.ob_pi hc]
      have hnone := stSt_cls_none hM σ (no_unit_hv hM σ hSm ⟨a, b, hhv⟩ hnhvc hz)
      have hr : repC (stSt γ G σ).cls z = z := by simp [repC, hnone]
      rw [hr]; exact hnone
  · rcases hb : sk.bond with _ | e
    · obtain ⟨O, hO, hOa, hu, hl, hsh⟩ := vc_object hM σ hSm hσ hsk hb
      have H := skip_sdecomp hM σ hSm hσ hsk G.molecule (sk.skelM hb)
      exact ⟨O, objSpec_of_skip hM σ sk O hO hOa hu hl (fun z hz hn => H.hinge_cases hz hn)
        (fun z hz hn => SDecomp.nonmerged_mem H hz hn) hsk (fun _ => hsh)
        (fun e' he' => by rw [hb] at he'; cases he')⟩
    · obtain ⟨O, hO, hOa, hu, hl, hsh⟩ := hvc_object hM σ hSm hσ hsk hb
      have H := skip_sdecomp hM σ hSm hσ hsk (Mole.eraseBond G.molecule e) (sk.skelN e hb)
      exact ⟨O, objSpec_of_skip hM σ sk O hO hOa hu hl (fun z hz hn => H.hinge_cases hz hn)
        (fun z hz hn => SDecomp.nonmerged_mem H hz hn) hsk (fun h => by rw [hb] at h; cases h)
        (fun e' he' => by
          rw [hb] at he'
          have : e = e' := Option.some.inj he'
          subst this
          exact hsh)⟩

end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
