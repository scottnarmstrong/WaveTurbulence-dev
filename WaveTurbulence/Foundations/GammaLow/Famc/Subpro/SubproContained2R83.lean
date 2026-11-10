/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproContained2R83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContained2R83
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
-- R83 port of sp-src/SubproContained2.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): TARGET `subpro` (4), atom form, for the construction
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

theorem contained_atoms (hM : G.molecule.IsMolecule) (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt γ G σ).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecification γ G σ)
    (L γ' η : ℝ) (base : Mom d) (z : GNode (stSt γ G σ).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt γ G σ).G D L γ' η base z ≠ 0)
    (P : Src.Object γ (stSt γ G σ).G.molecule)
    (hout : ∀ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, ¬ P.atoms ⊆ O.atoms)
    (hdis : Disjoint P.atoms (stSt γ G σ).hinges) :
    (∃ S a b, Src.IsDV γ (stSt γ G σ).G.molecule S a b ∧ P.atoms ⊆ S ∧ Disjoint S (stSt γ G σ).hinges ∧
        ∀ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, Disjoint S O.atoms) ∨
      ∃ Q : Src.Object γ (stSt γ G σ).G.molecule, P.atoms ⊆ Q.atoms ∧
        (Q.HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z) Molecule.GapKind.LG ∨
          Q.HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z) Molecule.GapKind.ZG) ∧
        Disjoint Q.atoms (stSt γ G σ).hinges ∧ ∀ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, Disjoint Q.atoms O.atoms := by
  classical
  have hB := nohinge_unmerged σ hdis
  obtain ⟨I, hIπ, -⟩ := exists_iso_down (stSt γ G σ).M (stSt γ G σ).hcls P.atoms hB
  have hP0 : IsVineLikeSetG γ G.molecule (P.atoms.image (stSt γ G σ).M.ob) := by
    have := Fama.isVineLikeSet_of_object (I.mapObjFc P (subset_refl _))
    rw [InducedIso.mapObj_atomsFc, hIπ] at this
    exact this
  obtain ⟨g, hg, hPg⟩ := cover_group hM hP0
  have hPg' : ∀ c ∈ P.atoms, (stSt γ G σ).M.ob c ∈ g := fun c hc => hPg (Finset.mem_image_of_mem _ hc)
  have hne : P.upper ∈ P.atoms := Fama.VineA.NormalizedSplice.Object.upper_mem P
  by_cases hmeet : ∃ u ∈ Fama.unitBlocks γ G σ, ∃ z0 ∈ g, z0 ∈ u.atoms
  · exfalso
    obtain ⟨u, hu, z0, hz0g, hz0u⟩ := hmeet
    obtain ⟨S'', hS''m, hσ'', hu''⟩ := Fama.mem_unitBlocks.mp hu
    have hgS : S'' = g := by
      by_contra hne'
      exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS''m hg hne')
        ((Fama.groupUnitsOf γ G S'').sub u hu'' hz0u) hz0g
    have hσg : σ g = Molecule.GapKind.SG := hgS ▸ hσ''
    have hu_g : u ∈ (Fama.groupUnitsOf γ G g).units := hgS ▸ hu''
    rcases hskip : (Fama.groupUnitsOf γ G g).skip with _ | sk
    · have hua := (Fama.groupUnitsOf γ G g).noskip_units hskip u hu_g
      have hcl := Fama.stSt_cls_mem hM σ hu (hua ▸ hPg' P.upper hne : (stSt γ G σ).M.ob P.upper ∈ u.atoms)
      rw [hB _ hne] at hcl
      cases hcl
    · obtain ⟨O, hO⟩ := objOf_some hM σ hg hσg (Or.inr ⟨sk, hskip⟩)
      exact hout O (mem_objects_of σ hg hσg hO)
        (atoms_sub_obj hM σ hO (fun c hc => ⟨hPg' c hc, hB c hc⟩))
  · have hall : ∀ z0 ∈ g, (stSt γ G σ).cls z0 = none := fun z0 hz0 =>
      Fama.stSt_cls_none hM σ (fun u hu hzu => hmeet ⟨u, hu, z0, hz0, hzu⟩)
    by_cases hobj : σ g = Molecule.GapKind.SG ∧ Fama.VineA.NormalizedSplice.HasObj γ G g
    · exfalso
      obtain ⟨O, hO⟩ := objOf_some hM σ hg hobj.1 hobj.2
      have hsub : P.atoms ⊆ O.atoms := by
        obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_spec (Option.mem_def.mpr hO)
        obtain ⟨A, -, hOA, hnm, -⟩ := hSpec.src
        intro c hc
        rw [hOA]
        exact Finset.mem_image.mpr ⟨(stSt γ G σ).M.ob c, hnm _ (hPg' c hc) (hall _ (hPg' c hc)), pi_ob σ (hB c hc)⟩
      exact hout O (mem_objects_of σ hg hobj.1 hO) hsub
    · have hO : Fama.VineA.NormalizedSplice.objOf γ G σ g = none := objOf_none σ (fun h => hobj ⟨h.2.2.1, h.2.2.2⟩)
      have hdisH := image_pi_disjoint_hinges σ hall
      have hdisO := image_pi_disjoint_objects hM σ hg hall hO
      obtain ⟨I2, hI2π, hI2od⟩ := exists_iso_up (stSt γ G σ).M (stSt γ G σ).hcls g hall
      have hPsub : P.atoms ⊆ g.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls) := by
        intro c hc
        exact Finset.mem_image.mpr ⟨(stSt γ G σ).M.ob c, hPg' c hc, pi_ob σ (hB c hc)⟩
      by_cases hvl : IsVineLikeSetG γ G.molecule g
      · right
        obtain ⟨a, Q, ha, hQ, e, he, hek, hnh', -⟩ := Fama.VineA.NormalizedSplice.gapSpecification_pair_of_object hM σ hg
        obtain ⟨a', ha', hdes⟩ := Fama.VineA.NormalizedSplice.designatedObject_isDesig hQ
        rw [ha] at ha'; cases ha'
        have haQ : a = Q.upper := hdes.1
        have haG : a ∈ g := (Fama.VineA.NormalizedSplice.groupJoint_kind ha).1
        have hQa : Q.atoms = g := by
          rcases hsk : (Fama.groupUnitsOf γ G g).skip with _ | sk
          · by_cases hu : (Fama.groupUnitsOf γ G g).units = []
            · exact hdes.2.2.2.2.2.2.1 hsk hu hvl
            · exact (hdes.2.2.2.2.1 hsk hu).1
          · rcases hb : sk.bond with _ | e'
            · exact (hdes.2.2.1 sk hsk hb).1
            · exact (hdes.2.2.2.1 sk e' hsk hb).1
        have hσne : σ g ≠ Molecule.GapKind.SG := by
          intro hσ
          apply hobj
          refine ⟨hσ, ?_⟩
          have hvl' : (∃ a b, Src.IsVC γ G.molecule g a b ∨ Src.IsHVC γ G.molecule g a b) → Fama.VineA.NormalizedSplice.HasObj γ G g := by
            intro hx
            rcases (Fama.groupUnitsOf γ G g).vl hM hg hx with hu | ⟨sk, hsk⟩
            · exfalso
              obtain ⟨u, hu'⟩ := List.exists_mem_of_ne_nil _ hu
              exact hmeet ⟨u, Fama.mem_unitBlocks.mpr ⟨g, hg, hσ, hu'⟩, u.upper,
                (Fama.groupUnitsOf γ G g).sub u hu' u.isBlock.2.1, u.isBlock.2.1⟩
            · exact Or.inr ⟨sk, hsk⟩
          obtain ⟨a0, b0, hab⟩ := hvl
          rcases hab with hhv | hvc | hhvc
          · by_cases hh : ∃ a b, Src.IsHVC γ G.molecule g a b
            · exact hvl' (by obtain ⟨a', b', h'⟩ := hh; exact ⟨a', b', Or.inr h'⟩)
            · exact Or.inl ⟨⟨a0, b0, hhv⟩, hh⟩
          · exact hvl' ⟨a0, b0, Or.inl hvc⟩
          · exact hvl' ⟨a0, b0, Or.inr hhvc⟩
        have hQup : Q.upper ∈ g := by rw [← haQ]; exact haG
        have hnotH : (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∉ (stSt γ G σ).hinges := by
          intro hh
          have := ((stSt γ G σ).mem_hinges _).mp hh
          rw [(stSt γ G σ).M.ob_pi, repC_of_none (hall a haG)] at this
          exact this (hall a haG)
        obtain ⟨-, hc1, hc2⟩ := hnh' hnotH
        have hk := gapKind_of_Z (stSt γ G σ).G D L γ' η base z hZ (q := e) (by rw [hD]; exact he)
        rw [hek] at hk
        have hQsub : Q.atoms ⊆ g := hQa ▸ subset_refl _
        set Q' := I2.mapObjFc Q hQsub with hQ'
        have hQ'a : Q'.atoms = g.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls) := by
          rw [hQ', InducedIso.mapObj_atomsFc, hQa, hI2π]
        have hcd : ∀ f : GardenDart (stSt γ G σ).G, Q.ContainsDart ((stSt γ G σ).M.od f) → Q'.ContainsDart f := by
          intro f hf
          have hx : G.molecule.InGroup g ((stSt γ G σ).M.od f) := hQa ▸ containsDart_inGroup Q hf
          have h1 := (I2.containsDart_mapFc Q hQsub hx).mpr hf
          have h2 : (I2.e ⟨(stSt γ G σ).M.od f, hx⟩).1 = f := (stSt γ G σ).M.od_inj (hI2od ⟨_, hx⟩)
          rw [h2] at h1
          exact h1
        have hQ'up : Q'.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls Q.upper := by
          rw [hQ', InducedIso.mapObj_upperFc, hI2π]
        have hgap : ∀ k, k = σ g → Q'.HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z) k := by
          intro k hk'
          exact hasGapKind_of_pair Q' L γ' η base _ e.first e.second (e.at_first.trans (haQ ▸ hQ'up).symm)
            (e.at_second.trans (haQ ▸ hQ'up).symm) e.opposite (hcd _ hc1) (hcd _ hc2) k (hk.trans hk'.symm)
        refine ⟨Q', hQ'a ▸ hPsub, ?_, hQ'a ▸ hdisH, fun O hO' => hQ'a ▸ hdisO O hO'⟩
        cases hs : σ g
        · exact Or.inr (hgap _ hs.symm)
        · exact absurd hs hσne
        · exact Or.inl (hgap _ hs.symm)
      · left
        have hst := hg.1
        rcases Fama.isStage1Group_iff.mp hst with hv | ⟨a, b, hdv⟩
        · exact absurd hv hvl
        · have := I2.isDV_mapFc hdv (subset_refl _)
          rw [hI2π] at this
          exact ⟨g.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls), _, _, this, hPsub, hdisH, hdisO⟩

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
