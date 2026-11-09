/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproCross3R83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCross2R83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCross3R83
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossIsoR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrownR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntry2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntryR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproGap2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproItems2R83
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
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.VineNormalizedRedSpliceGapKind
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
-- R83 port of sp-src/SubproCross3.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): TARGET `subpro` (6), atom-set form (R28 session 2)
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
  WaveTurbulence.Stage1 WaveTurbulence.Mole

variable {R : ℕ} {G : Garden (2 * R)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem crossing_atoms (hM : G.molecule.IsMolecule) (σ : Prescription G) (P : Src.Object γ (stSt γ G σ).G.molecule)
    (hout : ∀ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, ¬ P.atoms ⊆ O.atoms) (hnd : ¬ Disjoint P.atoms (stSt γ G σ).hinges) :
    ∃ v ∈ (Fama.VineA.NormalizedSplice.collectionChoices γ G σ).hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).first v) ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).second v)
            (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y)))) := by
  classical
  by_contra hcon
  have hjoint : ∀ v ∈ (stSt γ G σ).hinges, v ∈ P.atoms → v = P.upper ∨ v = P.lower := by
    intro v hv hvP
    by_contra h
    push Not at h
    exact hcon ⟨v, hv, hvP, Or.inl h⟩
  have hnx : ∀ v ∈ (stSt γ G σ).hinges, v ∈ P.atoms → ∀ x y, Fama.VineA.NormalizedSplice.hingePair γ G σ v = some (x, y) →
      (P.ContainsDart x ↔ P.ContainsDart y) := by
    intro v hv hvP x y hp
    by_contra hne
    apply hcon
    refine ⟨v, hv, hvP, Or.inr ⟨hjoint v hv hvP, x, y, by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp],
      by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], ?_⟩⟩
    by_cases hx : P.ContainsDart x
    · exact Or.inl ⟨hx, fun hy => hne ⟨fun _ => hy, fun _ => hx⟩⟩
    · have hy : P.ContainsDart y := by
        by_contra hy
        exact hne ⟨fun h => absurd h hx, fun h => absurd h hy⟩
      exact Or.inr ⟨hy, hx⟩
  have hK : ∀ v, v ∈ P.atoms → v ∈ (stSt γ G σ).hinges → ∃ j, (v = P.upper ∨ v = P.lower) ∧
      ∃ u ∈ Fama.unitBlocks γ G σ, (stSt γ G σ).M.ob v = u.upper ∧ (j = u.upper ∨ j = u.lower) ∧
        ∀ x, (stSt γ G σ).G.molecule.atom x = v → P.ContainsDart x → G.molecule.atom ((stSt γ G σ).M.od x) = j := by
    intro v hvP hvh
    obtain ⟨u, hu, hob, j, hj, hx⟩ := hinge_common_joint hM σ P hvh (hjoint v hvh hvP) (hnx v hvh hvP)
    exact ⟨j, hjoint v hvh hvP, u, hu, hob, hj, hx⟩
  let jf : GBranch (stSt γ G σ).G.tree → GBranch G.tree := fun c =>
    if h : c ∈ P.atoms ∧ c ∈ (stSt γ G σ).hinges then Classical.choose (hK c h.1 h.2) else (stSt γ G σ).M.ob c
  have hjnon : ∀ c ∈ P.atoms, c ∉ (stSt γ G σ).hinges → jf c = (stSt γ G σ).M.ob c := by
    intro c hc hch
    simp only [jf]
    rw [dif_neg (fun h => hch h.2)]
  have hjsp : ∀ w ∈ P.atoms, w ∈ (stSt γ G σ).hinges → (w = P.upper ∨ w = P.lower) ∧
      ∃ u ∈ Fama.unitBlocks γ G σ, (stSt γ G σ).M.ob w = u.upper ∧ (jf w = u.upper ∨ jf w = u.lower) ∧
        ∀ x, (stSt γ G σ).G.molecule.atom x = w → P.ContainsDart x →
          G.molecule.atom ((stSt γ G σ).M.od x) = jf w := by
    intro w hw hwh
    have := Classical.choose_spec (hK w hw hwh)
    simp only [jf]
    rw [dif_pos ⟨hw, hwh⟩]
    exact this
  have hKd : KData γ σ P jf := hjsp
  obtain ⟨v0, hv0P, hv0h⟩ : ∃ v0, v0 ∈ P.atoms ∧ v0 ∈ (stSt γ G σ).hinges := by
    by_contra h
    push Not at h
    exact hnd (Finset.disjoint_left.mpr fun v hv hvh => h v hv hvh)
  have hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (stSt γ G σ).hinges :=
    ⟨v0, hjoint v0 hv0h hv0P, hv0h⟩
  have hvc := cross_isvc hM σ P jf hjnon hKd hend
  obtain ⟨g, hg, hBg⟩ := cover_group hM (T := P.atoms.image jf) ⟨_, _, Or.inr (Or.inl hvc)⟩
  have hjg : ∀ c ∈ P.atoms, jf c ∈ g := fun c hc => hBg (Finset.mem_image_of_mem _ hc)
  -- the group of the hinge `v0`
  obtain ⟨-, u0, hu0, hob0, hj0, -⟩ := hjsp v0 hv0P hv0h
  obtain ⟨S0, hS0m, hσ0, hmem0⟩ := Fama.mem_unitBlocks.mp hu0
  have hj0m : jf v0 ∈ u0.atoms := by rcases hj0 with h | h <;> rw [h]; exacts [u0.isBlock.2.1, u0.isBlock.2.2.1]
  have hgS : g = S0 := by
    by_contra hne
    exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hg hS0m hne) (hjg v0 hv0P)
      ((Fama.groupUnitsOf γ G S0).sub u0 hmem0 hj0m)
  subst hgS
  rcases hsk : (Fama.groupUnitsOf γ G g).skip with _ | sk
  · -- a whole-group unit: the image has at most one atom
    have hall : ∀ z ∈ g, z ∈ u0.atoms := fun z hz => ((Fama.groupUnitsOf γ G g).noskip_units hsk u0 hmem0) ▸ hz
    have hhinge : ∀ c ∈ P.atoms, c ∈ (stSt γ G σ).hinges := by
      intro c hc
      by_contra hch
      have h1 := Fama.stSt_cls_mem hM σ hu0 (hall _ (hjg c hc))
      rw [hjnon c hc hch] at h1
      have h2 : (stSt γ G σ).cls ((stSt γ G σ).M.ob c) = none := by
        by_contra hne; exact hch (((stSt γ G σ).mem_hinges c).mpr hne)
      rw [h2] at h1; cases h1
    have hone : ∀ c ∈ P.atoms, c = v0 := by
      intro c hc
      obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hjsp c hc (hhinge c hc)
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      have hucu : uc = u0 := Fama.VineA.NormalizedSplice.unit_eq_of_mem hM σ huc hu0 hjcm (hall _ (hjg c hc))
      subst hucu
      exact (stSt γ G σ).M.ob_inj (hobc.trans hob0.symm)
    exact Object.upper_ne_lower' P ((hone _ (Fama.VineA.NormalizedSplice.Object.upper_mem P)).trans (hone _ (Fama.VineA.NormalizedSplice.Object.lower_mem P)).symm)
  · -- a skipped vine: `P` lies in the residual object
    have hσg : σ g = Molecule.GapKind.SG := hσ0
    obtain ⟨O, hO⟩ := objOf_some hM σ hg hσg (Or.inr ⟨sk, hsk⟩)
    obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_spec (Option.mem_def.mpr hO)
    obtain ⟨A, -, hOa, hnm, hsrc⟩ := hSpec.src
    obtain ⟨sk', hsk', hAeq, hup, hlo, -, -⟩ : ∃ sk', (Fama.groupUnitsOf γ G g).skip = some sk' ∧ A = sk'.A ∧
        O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk'.x ∧ O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk'.y ∧ True ∧ True := by
      rcases hsrc with ⟨⟨hhv, hnh⟩, hnone, -⟩ | ⟨sk', hsk', hAeq, hup, hlo, -, -⟩
      · rw [hsk] at hnone; cases hnone
      · exact ⟨sk', hsk', hAeq, hup, hlo, trivial, trivial⟩
    rw [hsk] at hsk'
    cases hsk'
    subst hAeq
    apply hout O (mem_objects_of σ hg hσg hO)
    intro c hc
    by_cases hch : c ∈ (stSt γ G σ).hinges
    · obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hjsp c hc hch
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      obtain ⟨Sc, hScm, hσc, hmemc⟩ := Fama.mem_unitBlocks.mp huc
      have hScg : Sc = g := by
        by_contra hne
        exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hScm hg hne) ((Fama.groupUnitsOf γ G Sc).sub uc hmemc hjcm)
          (hjg c hc)
      subst hScg
      exact hinge_mem_obj hM σ hg sk hsk hOa hup hlo huc hmemc hobc
    · have hcn : (stSt γ G σ).cls ((stSt γ G σ).M.ob c) = none := by
        by_contra hne; exact hch (((stSt γ G σ).mem_hinges c).mpr hne)
      have hobg : (stSt γ G σ).M.ob c ∈ g := by rw [← hjnon c hc hch]; exact hjg c hc
      exact atoms_sub_obj hM σ hO (P := {c}) (by
        intro c' hc'
        rw [Finset.mem_singleton] at hc'
        subst hc'
        exact ⟨hobg, hcn⟩) (Finset.mem_singleton_self c)

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
