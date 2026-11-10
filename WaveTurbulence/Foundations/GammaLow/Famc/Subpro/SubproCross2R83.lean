/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproCross2R83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossR83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCross2R83
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
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossIsoR83
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
-- R83 port of sp-src/SubproCross2.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): `crossing`, the far darts of a hinge (R28 session 2)
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

/-- The data of the substitution at the hinges of `P`: `jf` sends a hinge of `P` to the common joint of its unit that carries
the inside darts of `P`. -/
@[expose] def KData (γ : ℝ) [Fact (γ ≤ 1 / 2)] (σ : Prescription G) (P : Src.Object γ (stSt γ G σ).G.molecule)
    (jf : GBranch (stSt γ G σ).G.tree → GBranch G.tree) : Prop :=
  ∀ w ∈ P.atoms, w ∈ (stSt γ G σ).hinges → (w = P.upper ∨ w = P.lower) ∧
    ∃ u ∈ Fama.unitBlocks γ G σ, (stSt γ G σ).M.ob w = u.upper ∧ (jf w = u.upper ∨ jf w = u.lower) ∧
      ∀ x, (stSt γ G σ).G.molecule.atom x = w → P.ContainsDart x → G.molecule.atom ((stSt γ G σ).M.od x) = jf w

/-- A dart at a hinge of `P` that is not inside `P` has its image at the other joint of the unit, hence outside the image. -/
theorem far_dart (hM : G.molecule.IsMolecule) (σ : Prescription G) (P : Src.Object γ (stSt γ G σ).G.molecule)
    (jf : GBranch (stSt γ G σ).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P.atoms, c ∉ (stSt γ G σ).hinges → jf c = (stSt γ G σ).M.ob c)
    (hK : KData γ σ P jf) {w : GBranch (stSt γ G σ).G.tree} (hw : w ∈ P.atoms) (hwh : w ∈ (stSt γ G σ).hinges)
    {d : GardenDart (stSt γ G σ).G} (hd : (stSt γ G σ).G.molecule.atom d = w) (hnc : ¬ P.ContainsDart d) :
    G.molecule.atom ((stSt γ G σ).M.od d) ∉ P.atoms.image jf := by
  classical
  intro hmem
  obtain ⟨hwj, u, hu, hob, hjw, hKw⟩ := hK w hw hwh
  obtain ⟨ao, hao, hao_c, hao_o, -⟩ := contained_unique (stSt γ G σ).G P hwj true
  obtain ⟨ai, hai, hai_c, hai_o, -⟩ := contained_unique (stSt γ G σ).G P hwj false
  obtain ⟨hdm, hde, hdj⟩ := crown_dart hM σ hu hob hd
  -- the image atom of `d` is `jf w`
  have hatom : G.molecule.atom ((stSt γ G σ).M.od d) = jf w := by
    obtain ⟨c, hc, hcj⟩ := Finset.mem_image.mp hmem
    by_cases hch : c ∈ (stSt γ G σ).hinges
    · obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hK c hc hch
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      have hucu : uc = u := Fama.VineA.NormalizedSplice.unit_eq_of_mem hM σ huc hu hjcm (hcj ▸ hdm)
      subst hucu
      have : c = w := (stSt γ G σ).M.ob_inj (hobc.trans hob.symm)
      rw [← hcj, this]
    · exfalso
      have h1 : (stSt γ G σ).cls (G.molecule.atom ((stSt γ G σ).M.od d)) = some u.upper := by
        have := Fama.stSt_cls_mem hM σ hu hdm
        exact this
      have h2 : (stSt γ G σ).cls (jf c) = none := by
        rw [hjnon c hc hch]
        by_contra hne
        exact hch (((stSt γ G σ).mem_hinges c).mpr hne)
      rw [← hcj, h2] at h1
      cases h1
  -- the external darts at `jf w` are exactly the lifts of the two inside darts
  have hblock : ∃ j', G.molecule.IsBlock u.atoms (jf w) j' := by
    rcases hjw with h | h
    · exact ⟨u.lower, h ▸ u.isBlock⟩
    · exact ⟨u.upper, h ▸ block_swap_joints _ u.isBlock⟩
  have hcard := joint_ext_card hM hblock.choose_spec
  set E := (G.molecule.dartsAt (jf w)).filter (fun e => ¬ G.molecule.InGroup u.atoms e) with hE
  have hao_a := hKw ao hao hao_c
  have hai_a := hKw ai hai hai_c
  have hoE : (stSt γ G σ).M.od ao ∈ E := by
    obtain ⟨-, hext, -⟩ := crown_dart hM σ hu hob hao
    simp [hE, Molecule.dartsAt, hao_a, hext]
  have hiE : (stSt γ G σ).M.od ai ∈ E := by
    obtain ⟨-, hext, -⟩ := crown_dart hM σ hu hob hai
    simp [hE, Molecule.dartsAt, hai_a, hext]
  have hne : (stSt γ G σ).M.od ao ≠ (stSt γ G σ).M.od ai := by
    intro h
    have := congrArg G.molecule.out h
    rw [(stSt γ G σ).M.od_out, (stSt γ G σ).M.od_out, hao_o, hai_o] at this
    cases this
  have hE2 : E = {(stSt γ G σ).M.od ao, (stSt γ G σ).M.od ai} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hoE
      · rw [Finset.mem_singleton.mp he]; exact hiE
    · have : ({(stSt γ G σ).M.od ao, (stSt γ G σ).M.od ai} : Finset (GardenDart G)).card = 2 := Finset.card_pair hne
      omega
  have hdE : (stSt γ G σ).M.od d ∈ E := by simp [hE, Molecule.dartsAt, hatom, hde]
  rw [hE2] at hdE
  rcases Finset.mem_insert.mp hdE with h | h
  · exact hnc (by rw [(stSt γ G σ).M.od_inj h]; exact hao_c)
  · exact hnc (by rw [(stSt γ G σ).M.od_inj (Finset.mem_singleton.mp h)]; exact hai_c)

/-- **The substituted object is a VC of the original molecule.** -/
theorem cross_isvc (hM : G.molecule.IsMolecule) (σ : Prescription G) (P : Src.Object γ (stSt γ G σ).G.molecule)
    (jf : GBranch (stSt γ G σ).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P.atoms, c ∉ (stSt γ G σ).hinges → jf c = (stSt γ G σ).M.ob c)
    (hK : KData γ σ P jf) (hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (stSt γ G σ).hinges) :
    Src.IsVC γ G.molecule (P.atoms.image jf) (jf P.upper) (jf P.lower) := by
  classical
  have J1 : ∀ v ∈ P.atoms, v ∈ (stSt γ G σ).hinges → ∃ u ∈ Fama.unitBlocks γ G σ, (stSt γ G σ).M.ob v = u.upper ∧
      (jf v = u.upper ∨ jf v = u.lower) := by
    intro v hv hvh
    obtain ⟨-, u, hu, hob, hj, -⟩ := hK v hv hvh
    exact ⟨u, hu, hob, hj⟩
  cases hs : P.shape with
  | vc h =>
    obtain ⟨I, hI⟩ := crossing_iso hM σ (stSt γ G σ).G.molecule id Function.injective_id (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) P.atoms jf hjnon J1
      (by
        intro v hv hvh x hx hxv
        obtain ⟨-, u, hu, hob, hj, hKw⟩ := hK v hv hvh
        refine hKw x hxv ?_
        unfold Src.Object.ContainsDart
        rw [hs]; exact hx)
      (fun x0 _ => ⟨x0, rfl⟩)
    have := I.isVC_mapFc h (subset_refl _)
    rw [hI] at this
    exact this
  | hyper R =>
    obtain ⟨I, hI⟩ := crossing_iso hM σ (Mole.eraseBond (stSt γ G σ).G.molecule R.added)
      (fun x => x.1) Subtype.val_injective (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) P.atoms jf hjnon J1
      (by
        intro v hv hvh x hx hxv
        obtain ⟨-, u, hu, hob, hj, hKw⟩ := hK v hv hvh
        refine hKw x.1 hxv ?_
        unfold Src.Object.ContainsDart
        rw [hs]; exact ⟨x.2.1, x.2.2, hx⟩)
      (by
        intro x0 hx0
        by_contra hnot
        have hbad : x0 = R.added ∨ x0 = (stSt γ G σ).G.molecule.mate R.added := by
          by_contra hh
          push Not at hh
          exact hnot ⟨⟨x0, hh.1, hh.2⟩, rfl⟩
        obtain ⟨w, hwj, hwh⟩ := hend
        have hends := R.ends_eq
        unfold Molecule.ends at hends
        have hwP : w ∈ P.atoms := by rcases hwj with rfl | rfl; exact Fama.VineA.NormalizedSplice.Object.upper_mem P; exact Fama.VineA.NormalizedSplice.Object.lower_mem P
        have hwd : ∃ d, (d = R.added ∨ d = (stSt γ G σ).G.molecule.mate R.added) ∧
            (stSt γ G σ).G.molecule.atom d = w := by
          rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hwj with rfl | rfl
            · exact ⟨R.added, Or.inl rfl, h1⟩
            · exact ⟨(stSt γ G σ).G.molecule.mate R.added, Or.inr rfl, h2⟩
          · rcases hwj with rfl | rfl
            · exact ⟨(stSt γ G σ).G.molecule.mate R.added, Or.inr rfl, h2⟩
            · exact ⟨R.added, Or.inl rfl, h1⟩
        obtain ⟨d, hdd, hdw⟩ := hwd
        have hnc : ¬ P.ContainsDart d := by
          unfold Src.Object.ContainsDart
          rw [hs]
          rintro ⟨h1, h2, -⟩
          rcases hdd with rfl | rfl
          · exact h1 rfl
          · exact h2 rfl
        have hfar := far_dart hM σ P jf hjnon hK hwP hwh hdw hnc
        apply hfar
        obtain ⟨hin1, hin2⟩ := hx0
        have hmate : ∀ y : GardenDart (stSt γ G σ).G, (stSt γ G σ).M.od ((stSt γ G σ).G.molecule.mate y) =
            G.molecule.mate ((stSt γ G σ).M.od y) := (stSt γ G σ).M.od_mate
        have hdx : d = x0 ∨ d = (stSt γ G σ).G.molecule.mate x0 := by
          rcases hbad with h0 | h0 <;> rcases hdd with hd | hd
          · exact Or.inl (hd.trans h0.symm)
          · exact Or.inr (by rw [hd, h0])
          · exact Or.inr (by rw [hd, h0, (stSt γ G σ).G.molecule.mate_mate])
          · exact Or.inl (hd.trans h0.symm)
        rcases hdx with h | h
        · rw [h]; exact hin1
        · rw [h, hmate]; exact hin2)
    have := I.isVC_mapFc R.adjoint (subset_refl _)
    rw [hI] at this
    exact this

theorem Object.upper_ne_lower' {w : ℕ} {G' : Garden w} (P : Src.Object γ G'.molecule) : P.upper ≠ P.lower := by
  obtain ⟨A, a, b, sh⟩ := P
  cases sh with
  | vc h => exact h.1.2.2.2.1
  | hyper R => exact R.adjoint.1.2.2.2.1

/-- B1b (Mk-general form of `hinge_mem_obj`). -/
theorem hinge_mem_objMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (sk : Fama.SkipData γ G S) (hsk : (Fama.groupUnitsOf γ G S).skip = some sk)
    {Mk : Set (CLVineG γ _)} {O : Src.Object γ (stSt γ (Mk := Mk) G σ).G.molecule} (hOa : O.atoms = sk.A.image ((stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls))
    (hup : O.upper = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.x) (hlo : O.lower = (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.y)
    {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ (Mk := Mk) G σ) (hu' : u ∈ (Fama.groupUnitsOf γ G S).units)
    {c : GBranch (stSt γ (Mk := Mk) G σ).G.tree} (hob : (stSt γ (Mk := Mk) G σ).M.ob c = u.upper) : c ∈ O.atoms := by
  have hsu := (Fama.groupUnitsOf γ G S).skip_units sk hsk
  rcases hsu.1 u hu' with ⟨hL, hl⟩ | ⟨hR, hr⟩
  · have hxu : sk.x ∈ u.atoms := by
      rcases hl with ⟨_, h2⟩ | ⟨h2, _⟩
      · rw [← h2]; exact u.isBlock.2.2.1
      · rw [← h2]; exact u.isBlock.2.1
    have : (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.x = c := by
      apply (stSt γ (Mk := Mk) G σ).M.ob_inj
      rw [(stSt γ (Mk := Mk) G σ).M.ob_pi, hob]
      exact Fama.stSt_repC_memMk (Mk := Mk) hM σ hu hxu
    rw [← this, ← hup]; exact Fama.VineA.NormalizedSplice.Object.upper_mem O
  · have hyu : sk.y ∈ u.atoms := by
      rcases hr with ⟨h2, _⟩ | ⟨_, h2⟩
      · rw [← h2]; exact u.isBlock.2.1
      · rw [← h2]; exact u.isBlock.2.2.1
    have : (stSt γ (Mk := Mk) G σ).M.pi (stSt γ (Mk := Mk) G σ).hcls sk.y = c := by
      apply (stSt γ (Mk := Mk) G σ).M.ob_inj
      rw [(stSt γ (Mk := Mk) G σ).M.ob_pi, hob]
      exact Fama.stSt_repC_memMk (Mk := Mk) hM σ hu hyu
    rw [← this, ← hlo]; exact Fama.VineA.NormalizedSplice.Object.lower_mem O

/-- A hinge that is the crown of a unit of a group with a skipped vine is an atom (a joint) of the residual object. -/
theorem hinge_mem_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) (sk : Fama.SkipData γ G S) (hsk : (Fama.groupUnitsOf γ G S).skip = some sk)
    {O : Src.Object γ (stSt γ G σ).G.molecule} (hOa : O.atoms = sk.A.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls))
    (hup : O.upper = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.x) (hlo : O.lower = (stSt γ G σ).M.pi (stSt γ G σ).hcls sk.y)
    {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γ G σ) (hu' : u ∈ (Fama.groupUnitsOf γ G S).units)
    {c : GBranch (stSt γ G σ).G.tree} (hob : (stSt γ G σ).M.ob c = u.upper) : c ∈ O.atoms := hinge_mem_objMk (Mk := ∅) hM σ hSm sk hsk hOa hup hlo hu hu' hob

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
