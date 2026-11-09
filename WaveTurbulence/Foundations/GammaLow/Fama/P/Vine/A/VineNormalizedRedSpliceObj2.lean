/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceObj2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceObj2
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover


/-!
# R83 successor copy: HV objects γ and normalized candidate selection

Source copy: pinned/r83-RedSpliceObj2.lean; hash recorded in COPIED-SHA256SUMS.
The arbitrary hvPick γ definition is replaced by VineGroupPickSpec.hvGroupPick.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- B1b (Mk-general form of `hyper_object`). -/
theorem hyper_objectMk (σ : Prescription G) {S A L0 R0 : Finset (GBranch G.tree)} {a b x y : GBranch G.tree}
    {e : GardenDart G}
    {Mk : Set (CLVineG γ _)} (H : SDecomp (Mole.eraseBond G.molecule e) (stSt γ (Mk := Mk) G σ).cls S A L0 R0 a b x y)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Src.IsSomeVine γ (Mole.eraseBond G.molecule e) A x y) :
    ∃ O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule, Src.AllowedCollectionObject γ (stSt γ (Mk := Mk) G σ).G O ∧
      O.atoms = A.image ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls) ∧
      O.upper = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls x ∧ O.lower = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls y ∧
      ∃ R : Src.HyperLikeRealization γ (stSt γ (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ (Mk := Mk) G σ).M.od R.added = e := by
  have hnc : ¬ ∃ a', (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom e) = some a' ∧
      (stSt γ (Mk := Mk) G σ).cls (G.molecule.atom (G.molecule.mate e)) = some a' := by
    unfold Molecule.ends at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact H.ends_not_class
    · rw [h1, h2]
      rintro ⟨r, ha, hb⟩
      exact H.ends_not_class ⟨r, hb, ha⟩
  obtain ⟨e', rfl⟩ := ((stSt γ (Mk := Mk) G σ).M.od_range e).mpr hnc
  have hc := (stSt γ (Mk := Mk) G σ).hcls
  let I := H.inducedIso ((stSt γ (Mk := Mk) G σ).M.eraseMol hc e')
  have hX := hvine
  have hv : Src.IsSomeVine γ (Mole.eraseBond (stSt γ (Mk := Mk) G σ).G.molecule e')
      (A.image ((stSt γ (Mk := Mk) G σ).M.pi hc)) ((stSt γ (Mk := Mk) G σ).M.pi hc x) ((stSt γ (Mk := Mk) G σ).M.pi hc y) :=
    isSomeVine_iso I hX
  have hobx : (stSt γ (Mk := Mk) G σ).M.ob ((stSt γ (Mk := Mk) G σ).M.pi hc x) = ((stSt γ (Mk := Mk) G σ).cls x).getD x :=
    (stSt γ (Mk := Mk) G σ).M.ob_pi hc x
  have hoby : (stSt γ (Mk := Mk) G σ).M.ob ((stSt γ (Mk := Mk) G σ).M.pi hc y) = ((stSt γ (Mk := Mk) G σ).cls y).getD y :=
    (stSt γ (Mk := Mk) G σ).M.ob_pi hc y
  have hpx : (stSt γ (Mk := Mk) G σ).M.ob ((stSt γ (Mk := Mk) G σ).G.molecule.atom e') = ((stSt γ (Mk := Mk) G σ).cls a).getD a ∨
      (stSt γ (Mk := Mk) G σ).M.ob ((stSt γ (Mk := Mk) G σ).G.molecule.atom e') = ((stSt γ (Mk := Mk) G σ).cls b).getD b := by
    rw [(stSt γ (Mk := Mk) G σ).M.ob_atom e']
    unfold Molecule.ends at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by rw [h1]; rfl)
    · exact Or.inr (by rw [h1]; rfl)
  have hends' : (stSt γ (Mk := Mk) G σ).G.molecule.ends e' = s((stSt γ (Mk := Mk) G σ).M.pi hc x, (stSt γ (Mk := Mk) G σ).M.pi hc y) := by
    unfold Molecule.ends at hends ⊢
    have hm : (stSt γ (Mk := Mk) G σ).M.ob ((stSt γ (Mk := Mk) G σ).G.molecule.atom ((stSt γ (Mk := Mk) G σ).G.molecule.mate e')) =
        ((stSt γ (Mk := Mk) G σ).cls (G.molecule.atom (G.molecule.mate ((stSt γ (Mk := Mk) G σ).M.od e')))).getD
          (G.molecule.atom (G.molecule.mate ((stSt γ (Mk := Mk) G σ).M.od e'))) := by
      rw [(stSt γ (Mk := Mk) G σ).M.ob_atom, (stSt γ (Mk := Mk) G σ).M.od_mate]; rfl
    have h0 : (stSt γ (Mk := Mk) G σ).M.ob ((stSt γ (Mk := Mk) G σ).G.molecule.atom e') =
        ((stSt γ (Mk := Mk) G σ).cls (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od e'))).getD (G.molecule.atom ((stSt γ (Mk := Mk) G σ).M.od e')) :=
      (stSt γ (Mk := Mk) G σ).M.ob_atom e'
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at h0; rw [h2] at hm
      have e1 : (stSt γ (Mk := Mk) G σ).G.molecule.atom e' = (stSt γ (Mk := Mk) G σ).M.pi hc x :=
        (stSt γ (Mk := Mk) G σ).M.ob_inj (h0.trans (H.rc_a.trans hobx.symm))
      have e2 : (stSt γ (Mk := Mk) G σ).G.molecule.atom ((stSt γ (Mk := Mk) G σ).G.molecule.mate e') = (stSt γ (Mk := Mk) G σ).M.pi hc y :=
        (stSt γ (Mk := Mk) G σ).M.ob_inj (hm.trans (H.rc_b.trans hoby.symm))
      rw [e1, e2]
    · rw [h1] at h0; rw [h2] at hm
      have e1 : (stSt γ (Mk := Mk) G σ).G.molecule.atom e' = (stSt γ (Mk := Mk) G σ).M.pi hc y :=
        (stSt γ (Mk := Mk) G σ).M.ob_inj (h0.trans (H.rc_b.trans hoby.symm))
      have e2 : (stSt γ (Mk := Mk) G σ).G.molecule.atom ((stSt γ (Mk := Mk) G σ).G.molecule.mate e') = (stSt γ (Mk := Mk) G σ).M.pi hc x :=
        (stSt γ (Mk := Mk) G σ).M.ob_inj (hm.trans (H.rc_a.trans hobx.symm))
      rw [e1, e2, Sym2.eq_swap]
  exact ⟨objHyper γ e' _ _ _ hends' hv, allowed_hyper e' _ _ _ hends' hv, rfl, rfl, rfl, _, rfl, rfl⟩

/-- **The HV residual** of a vine `A` of the adjoint `eraseBond M e` of a decomposed group, in `G_sb`: the vine
`π''A` with the image `e'` of the added bond `e` (TARGET `blockchainprop` and subpro(2): an HVC reduces to an
SG HV; an SG HV is unchanged). -/
theorem hyper_object (σ : Prescription G) {S A L0 R0 : Finset (GBranch G.tree)} {a b x y : GBranch G.tree}
    {e : GardenDart G}
    (H : SDecomp (Mole.eraseBond G.molecule e) (stSt γ G σ).cls S A L0 R0 a b x y)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Src.IsSomeVine γ (Mole.eraseBond G.molecule e) A x y) :
    ∃ O : Src.Object γ (stSt γ G σ).G.molecule, Src.AllowedCollectionObject γ (stSt γ G σ).G O ∧
      O.atoms = A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls) ∧
      O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls x ∧ O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls y ∧
      ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e := hyper_objectMk (Mk := ∅) σ H hends hvine

/-- The HV of the skipped vine of an SG HVC group. -/
theorem hvc_object (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    {sk : SkipData γ G S} (hsk : (groupUnitsOf γ G S).skip = some sk) {e : GardenDart G}
    (hbond : sk.bond = some e) :
    ∃ O : Src.Object γ (stSt γ G σ).G.molecule, Src.AllowedCollectionObject γ (stSt γ G σ).G O ∧
      O.atoms = sk.A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls) ∧
      O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.x ∧ O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.y ∧
      ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e :=
  hyper_object σ (skip_sdecomp hM σ hSm hσ hsk _ (sk.skelN e hbond)) (sk.blockN e hbond).1 (sk.vineN e hbond)

/-- No unit meets an HV group. -/
theorem no_unit_hv (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (hhv : ∃ a b, Src.IsHV γ G.molecule S a b)
    (hnhvc : ¬ ∃ a b, Src.IsHVC γ G.molecule S a b)
    {v : GBranch G.tree} (hvS : v ∈ S) : ∀ u ∈ unitBlocks γ G σ, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := mem_unitBlocks.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rw [(groupUnitsOf γ G S').hv_empty hhv hnhvc] at hu'
    simp at hu'
  · have hpart := partition_eq_maximalGroups (maximalGroupsG_partition (γ := γ) hM)
    have hdisj : (maximalGroupsG γ G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (maximalGroupsG_partition (γ := γ) hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) ((groupUnitsOf γ G S').sub u hu' hv) hvS

/-- The residual of an SG HV group (not touched by the splice): the canonical triple gives the object. -/
theorem hv_object (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) {a b : GBranch G.tree} {e : GardenDart G}
    (hnhvc : ¬ ∃ a b, Src.IsHVC γ G.molecule S a b)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Src.IsSomeVine γ (Mole.eraseBond G.molecule e) S a b) :
    ∃ O : Src.Object γ (stSt γ G σ).G.molecule, Src.AllowedCollectionObject γ (stSt γ G σ).G O ∧
      O.atoms = S.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls) ∧
      O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∧ O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls b ∧
      ∃ R : Src.HyperLikeRealization γ (stSt γ G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ).M.od R.added = e := by
  have hab : a ≠ b := (isSomeVine_ends hvine).2.2
  have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
    intro h
    unfold Molecule.ends at hends
    rw [h] at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab (h1.symm.trans h2)
    · exact hab (h2.symm.trans h1)
  have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
  have hnone : ∀ {v : GBranch G.tree}, v ∈ S → ∀ u ∈ unitBlocks γ G σ, v ∉ u.atoms :=
    fun hv => no_unit_hv hM σ hSm ⟨a, b, e, hends, hvine⟩ hnhvc hv
  have hsk : SkelDecomp (Mole.eraseBond G.molecule e) S S ∅ ∅ a b a b :=
    ⟨hN, by simp, Src.isBlock_of_isSomeVine hvine, Src.isBlock_of_isSomeVine hvine, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩,
      Finset.disjoint_empty_left _⟩
  have H : SDecomp (Mole.eraseBond G.molecule e) (stSt γ G σ).cls S S ∅ ∅ a b a b :=
    { toSkelDecomp := hsk
      hcls := (stSt γ G σ).hcls
      hLcl := fun p v hv => by simp at hv
      hRcl := fun p v hv => by simp at hv
      hLc := fun p hp => by simp at hp
      hRc := fun p hp => by simp at hp
      hNone := fun v hvS _ _ => stSt_cls_none hM σ (hnone hvS) }
  exact hyper_object σ H hends hvine

end WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice
