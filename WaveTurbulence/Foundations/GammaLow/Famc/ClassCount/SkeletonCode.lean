/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonCode` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Lab
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.SkeletonLeg
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.WaveB.Ladders
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonCode
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Assembly
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Layout
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: `SkeletonCodeLeg` from the abstract LAB lemma

The molecule of a plain skeleton `S` with a prescription `σ` and the molecule of its spliced garden `(stSt γ S σ).G`
form a `SpliceData`: `ob`, `od` from the `SpMap`, units `Fama.unitBlocks γ S σ` with representatives `u.upper`, classes `repC cls`.
-/

@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Reg.Skeleton

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]


/-- B1b (Mk-general form of `cls_same_iff`). -/
theorem cls_same_iffMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (p p' : GBranch S.tree) {Mk : Set (CLVineG γ _)} :
    (∃ a, (stSt γ (Mk := Mk) S σ).cls p = some a ∧ (stSt γ (Mk := Mk) S σ).cls p' = some a) ↔
      ∃ i : ℕ, ∃ hi : i < (Fama.unitBlocks γ (Mk := Mk) S σ).length,
        p ∈ ((Fama.unitBlocks γ (Mk := Mk) S σ).get ⟨i, hi⟩).atoms ∧ p' ∈ ((Fama.unitBlocks γ (Mk := Mk) S σ).get ⟨i, hi⟩).atoms := by
  constructor
  · rintro ⟨a, h1, h2⟩
    have hp : ∃ u ∈ Fama.unitBlocks γ (Mk := Mk) S σ, p ∈ u.atoms := by
      by_contra hno
      push Not at hno
      rw [Fama.stSt_cls_noneMk (Mk := Mk) hM σ hno] at h1; exact absurd h1 (by simp)
    have hp' : ∃ u ∈ Fama.unitBlocks γ (Mk := Mk) S σ, p' ∈ u.atoms := by
      by_contra hno
      push Not at hno
      rw [Fama.stSt_cls_noneMk (Mk := Mk) hM σ hno] at h2; exact absurd h2 (by simp)
    obtain ⟨u, hu, hpu⟩ := hp
    obtain ⟨u', hu', hpu'⟩ := hp'
    have e1 := Fama.stSt_cls_memMk (Mk := Mk) hM σ hu hpu
    have e2 := Fama.stSt_cls_memMk (Mk := Mk) hM σ hu' hpu'
    rw [e1] at h1; rw [e2] at h2
    have hup : u.upper = u'.upper := (Option.some.inj h1).trans (Option.some.inj h2).symm
    have : u = u' := by
      apply Fama.units_eq_of_not_disjointMk (Mk := Mk) hM σ hu hu'
      rw [Finset.not_disjoint_iff]
      exact ⟨u.upper, u.isBlock.2.1, hup ▸ u'.isBlock.2.1⟩
    subst this
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
    exact ⟨i.1, i.2, by rw [show (⟨i.1, i.2⟩ : Fin _) = i from rfl, hi]; exact ⟨hpu, hpu'⟩⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨_, Fama.stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) h1, Fama.stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) h2⟩

/-- B2d: the `SpliceData` of a skeleton and its spliced garden at the marked set `Mk`. -/
noncomputable def spliceDataOfMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (Mk : Set (CLVineG γ S)) (v0 : GBranch S.tree) : SpliceData S.molecule (stSt γ S σ Mk).G.molecule where
  ob := (stSt γ S σ Mk).M.ob
  od := (stSt γ S σ Mk).M.od
  q := (Fama.unitBlocks γ S σ Mk).length
  U := fun i => if h : i < (Fama.unitBlocks γ S σ Mk).length then ((Fama.unitBlocks γ S σ Mk).get ⟨i, h⟩).atoms else ∅
  rep := fun i => if h : i < (Fama.unitBlocks γ S σ Mk).length then ((Fama.unitBlocks γ S σ Mk).get ⟨i, h⟩).upper else v0
  cl := repC (stSt γ S σ Mk).cls
  ob_inj := (stSt γ S σ Mk).M.ob_inj
  od_inj := (stSt γ S σ Mk).M.od_inj
  od_mate := (stSt γ S σ Mk).M.od_mate
  od_out := (stSt γ S σ Mk).M.od_out
  U_disj := by
    intro i j hi hj hij
    simp only [dif_pos hi, dif_pos hj]
    have hp := List.pairwise_iff_get.mp (Fama.unitBlocks_pairwiseMk hM σ Mk)
    rcases lt_or_gt_of_ne hij with h | h
    · exact hp ⟨i, hi⟩ ⟨j, hj⟩ h
    · exact (hp ⟨j, hj⟩ ⟨i, hi⟩ h).symm
  rep_mem := by
    intro i hi
    simp only [dif_pos hi]
    exact ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).isBlock.2.1
  cl_unit := by
    intro i hi v hv
    simp only [dif_pos hi] at hv ⊢
    exact Fama.stSt_repC_memMk (Mk := Mk) hM σ (List.get_mem _ _) hv
  cl_free := by
    intro v hv
    refine Fama.stSt_repC_noneMk (Mk := Mk) hM σ (fun u hu hvu => ?_)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
    have := hv i.1 i.2
    simp only [dif_pos i.2] at this
    rw [show (⟨i.1, i.2⟩ : Fin _) = i from rfl, hi] at this
    exact this hvu
  ob_atom := (stSt γ S σ Mk).M.ob_atom
  ob_range := by
    intro v
    rw [(stSt γ S σ Mk).M.ob_range]
    simp only [repC]
    cases h : (stSt γ S σ Mk).cls v <;> simp
  od_range := by
    intro x
    rw [(stSt γ S σ Mk).M.od_range]
    refine not_congr ?_
    rw [cls_same_iffMk (Mk := Mk) S hM σ]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by simpa [dif_pos hi] using h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by simpa [dif_pos hi] using h⟩


theorem spliceDataOf_UMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVineG γ S))
    (v0 : GBranch S.tree)
    {i : ℕ} (hi : i < (Fama.unitBlocks γ S σ Mk).length) :
    (spliceDataOfMk γ S hM σ Mk v0).U i = ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).atoms := by
  simp [spliceDataOfMk, dif_pos hi]

theorem spliceDataOf_repMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVineG γ S))
    (v0 : GBranch S.tree)
    {i : ℕ} (hi : i < (Fama.unitBlocks γ S σ Mk).length) :
    (spliceDataOfMk γ S hM σ Mk v0).rep i = ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).upper := by
  simp [spliceDataOfMk, dif_pos hi]

theorem spliceDataOf_qMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVineG γ S))
    (v0 : GBranch S.tree) :
    (spliceDataOfMk γ S hM σ Mk v0).q = (Fama.unitBlocks γ S σ Mk).length := rfl


/-- The ladders of the spliced garden as a `LadderFam`. -/
noncomputable def ladderFamOf (G : Garden w) : LadderFam G.molecule {T // T ∈ G.molecule.maximalLadders} where
  len := (Fama.ladderDataOf G).length
  u := (Fama.ladderDataOf G).upper
  v := (Fama.ladderDataOf G).lower
  lad := (Fama.ladderDataOf G).ladder

theorem ladderFamOf_atomsOf (G : Garden w) (i : {T // T ∈ G.molecule.maximalLadders}) :
    (ladderFamOf G).atomsOf i = i.1 := (Fama.ladderDataOf G).atoms i

theorem ladderFamOf_disj (G : Garden w) (hM : G.molecule.IsMolecule)
    (i j : {T // T ∈ G.molecule.maximalLadders}) (hij : i ≠ j) :
    Disjoint ((ladderFamOf G).atomsOf i) ((ladderFamOf G).atomsOf j) := by
  rw [ladderFamOf_atomsOf, ladderFamOf_atomsOf]
  exact Molecule.maximalLadders_pairwiseDisjoint G.molecule hM i.2 j.2 (fun h => hij (Subtype.ext h))

theorem ladderFamOf_r (G : Garden w) :
    (G.molecule.atoms.filter (fun a => ∀ i, a ∉ (ladderFamOf G).atomsOf i)).card +
        Fintype.card {T // T ∈ G.molecule.maximalLadders} = G.molecule.rho := by
  classical
  have hset : ∀ a : GBranch G.tree, (∀ i, a ∉ (ladderFamOf G).atomsOf i) ↔
      (∀ T ∈ G.molecule.maximalLadders, a ∉ T) := by
    intro a
    constructor
    · intro h T hT hmem
      exact h ⟨T, hT⟩ (by rw [ladderFamOf_atomsOf]; exact hmem)
    · intro h i hmem
      rw [ladderFamOf_atomsOf] at hmem
      exact h i.1 i.2 hmem
  unfold Molecule.rho Molecule.numLadders Molecule.numFree
  rw [Fintype.card_coe, add_comm]
  refine congrArg (fun t => G.molecule.maximalLadders.card + t) ?_
  refine Finset.card_bij (fun a _ => a) ?_ (fun a _ b _ h => h) ?_
  · intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, (hset a).mp ha.2⟩
  · intro b hb
    simp only [Finset.mem_filter] at hb
    exact ⟨b, Finset.mem_filter.mpr ⟨hb.1, (hset b).mpr hb.2⟩, rfl⟩


/-- B2d: **`SkeletonCodeLegMk`** (nonempty case). -/
theorem skeletonCode_nonemptyMk {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S) (Mk : Set (CLVineG γ S))
    (v0 : GBranch S.tree) :
    ∃ nsb : ℕ, nsb ≤ Fintype.card (GBranch S.tree) ∧ ∃ ℓ : GBranch S.tree ≃ Fin (Fintype.card (GBranch S.tree)),
      ∃ L ∈ arcLists (Fintype.card (GBranch S.tree)) (4 * rbarOfMkG γ S σ Mk)
          (unitFamily (Fintype.card (GBranch S.tree)) nsb (rbarOfMkG γ S σ Mk) (Fintype.card (GBranch S.tree) - nsb)),
        ∀ x : Fin (Fintype.card (GBranch S.tree)) × Fin (Fintype.card (GBranch S.tree)),
          Fintype.card {b : {y : GardenDart S // S.molecule.out y = true} //
            (ℓ (S.molecule.atom b.1), ℓ (S.molecule.atom (S.molecule.mate b.1))) = x} = L.count x := by
  classical
  have hM := Mole.garden_isMolecule S
  have hM' := Mole.garden_isMolecule (stSt γ S σ Mk).G
  let SD := spliceDataOfMk γ S hM σ Mk v0
  have hex : ∀ i : ℕ, ∃ (c : List IngCodeG) (l : GBranch S.tree → ℕ), ∀ h : i < SD.q,
      (∀ d ∈ c, d.Wf) ∧ Set.InjOn l (SD.U i) ∧ (SD.U i).image l = Finset.range (unitWeight c + 1) ∧
      groupArcs S.molecule (SD.U i) l = ((unitArcs c : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
    intro i
    by_cases h : i < SD.q
    · obtain ⟨cs, hwf, lab, hinj, himg, harcs⟩ :=
        unit_decodeMk S hM σ (Mk := Mk) (u := (Fama.unitBlocks γ S σ Mk).get ⟨i, h⟩) (List.get_mem _ _)
      have hU := spliceDataOf_UMk S hM σ Mk v0 (show i < (Fama.unitBlocks γ S σ Mk).length from h)
      refine ⟨cs, lab, fun _ => ⟨hwf, ?_, ?_, ?_⟩⟩
      · rw [hU]; exact hinj
      · rw [hU]; exact himg
      · rw [hU]; exact harcs
    · exact ⟨[], fun _ => 0, fun h' => absurd h' h⟩
  choose cs lab hprop using hex
  let W : ℕ → ℕ := fun i => unitWeight (cs i)
  have hcardU : ∀ i, i < SD.q → (SD.U i).card = W i + 1 := by
    intro i hi
    obtain ⟨-, hinj, himg, -⟩ := hprop i hi
    have := Finset.card_image_of_injOn hinj
    rw [himg, Finset.card_range] at this
    exact this.symm
  have hW : ∀ i, i < SD.q → W i = unitWeight (cs i) ∧ 1 ≤ W i := by
    intro i hi
    refine ⟨rfl, ?_⟩
    have h2 : 2 ≤ (SD.U i).card := by
      have hb := ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).isBlock
      have hU := spliceDataOf_UMk S hM σ Mk v0 (show i < (Fama.unitBlocks γ S σ Mk).length from hi)
      rw [hU]
      have hne : ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).upper ≠ ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).lower := hb.2.2.2.1
      have : ({((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).upper, ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).lower} : Finset _) ⊆
          ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).atoms := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hb.2.1
        · exact hb.2.2.1
      have := Finset.card_le_card this
      rwa [Finset.card_pair hne] at this
    have := hcardU i hi
    omega
  have hH : ∀ c, (∃ i, i < SD.q ∧ SD.ob c = SD.rep i) → c ∈ (stSt γ S σ Mk).hinges := by
    rintro c ⟨i, hi, hc⟩
    rw [SpState.mem_hinges]
    have hc' : (stSt γ S σ Mk).M.ob c = ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).upper := by
      have : SD.ob c = SD.rep i := hc
      rw [spliceDataOf_repMk S hM σ Mk v0 (show i < (Fama.unitBlocks γ S σ Mk).length from hi)] at this
      exact this
    rw [hc']
    have := Fama.stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem (Fama.unitBlocks γ S σ Mk) ⟨i, hi⟩) ((Fama.unitBlocks γ S σ Mk).get ⟨i, hi⟩).isBlock.2.1
    rw [this]; simp
  obtain ⟨nsb, hnsb, ℓ, L, hL, hcount⟩ := SpliceData.lab_arcs SD hM hM' (fun v => Finset.mem_univ v)
    (ladderFamOf (stSt γ S σ Mk).G) (ladderFamOf_disj (stSt γ S σ Mk).G hM') (stSt γ S σ Mk).hinges hH cs W lab
    (fun i hi => (hprop i hi).1) hW (fun i hi => (hprop i hi).2.1) (fun i hi => (hprop i hi).2.2.1)
    (fun i hi => (hprop i hi).2.2.2)
  have hr : (((stSt γ S σ Mk).G.molecule.atoms.filter (fun a => ∀ i, a ∉ (ladderFamOf (stSt γ S σ Mk).G).atomsOf i)).card +
      Fintype.card {T // T ∈ (stSt γ S σ Mk).G.molecule.maximalLadders} + (stSt γ S σ Mk).hinges.card) =
      rbarOfMkG γ S σ Mk := by
    have := ladderFamOf_r (stSt γ S σ Mk).G
    unfold rbarOfMkG
    rw [← this]
    simp only [Fama.collectionChoices]
  rw [hr] at hL
  exact ⟨nsb, hnsb, ℓ, L, hL, hcount⟩


/-- B2d: in the empty case there is nothing to code (any marked set). -/
theorem skeletonCode_emptyMk {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S) (Mk : Set (CLVineG γ S))
    (hE : IsEmpty (GBranch S.tree)) :
    ∃ nsb : ℕ, nsb ≤ Fintype.card (GBranch S.tree) ∧ ∃ ℓ : GBranch S.tree ≃ Fin (Fintype.card (GBranch S.tree)),
      ∃ L ∈ arcLists (Fintype.card (GBranch S.tree)) (4 * rbarOfMkG γ S σ Mk)
          (unitFamily (Fintype.card (GBranch S.tree)) nsb (rbarOfMkG γ S σ Mk) (Fintype.card (GBranch S.tree) - nsb)),
        ∀ x : Fin (Fintype.card (GBranch S.tree)) × Fin (Fintype.card (GBranch S.tree)),
          Fintype.card {b : {y : GardenDart S // S.molecule.out y = true} //
            (ℓ (S.molecule.atom b.1), ℓ (S.molecule.atom (S.molecule.mate b.1))) = x} = L.count x := by
  classical
  have h0 : Fintype.card (GBranch S.tree) = 0 := Fintype.card_eq_zero
  have hM := Mole.garden_isMolecule S
  -- the spliced garden has no atoms
  have hE' : IsEmpty (GBranch (stSt γ S σ Mk).G.tree) :=
    ⟨fun c => hE.false ((stSt γ S σ Mk).M.ob c)⟩
  have hr : rbarOfMkG γ S σ Mk = 0 := by
    unfold rbarOfMkG
    have h1 : (stSt γ S σ Mk).G.molecule.rho = 0 := by
      unfold Molecule.rho Molecule.numLadders Molecule.numFree
      have hl : (stSt γ S σ Mk).G.molecule.maximalLadders = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro T hT
        simp only [Molecule.maximalLadders, Finset.mem_filter] at hT
        obtain ⟨-, ⟨m, u, v, hu, -⟩, -⟩ := hT
        exact hE'.false (u 0)
      have hf : ((stSt γ S σ Mk).G.molecule.atoms.filter (fun v => ∀ T ∈ (stSt γ S σ Mk).G.molecule.maximalLadders, v ∉ T)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v; exact hE'.elim v
      have ha : (stSt γ S σ Mk).G.molecule.atoms = ∅ :=
        Finset.eq_empty_of_forall_notMem (fun v _ => hE'.elim v)
      simp [hl, hf, ha]
    have h2 : (Fama.collectionChoices γ S σ Mk).hinges.card = 0 := by
      simp only [Fama.collectionChoices]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro c; exact hE'.elim c
    omega
  refine ⟨0, by omega, ?_⟩
  rw [h0]
  refine ⟨Equiv.equivOfIsEmpty _ _, [], ?_, fun x => x.1.elim0⟩
  rw [hr]
  simp only [Nat.sub_self, mul_zero]
  unfold arcLists
  refine Finset.mem_image.mpr ⟨((fun _ => 0, fun _ => 0), []), ?_, by simp [cntList]⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, mem_listsLe (by simp)⟩
  · unfold nearFns
    rw [Fintype.mem_piFinset]
    intro x; exact x.1.elim0
  · have := mem_unitFamily (n := 0) (nsb := 0) (r := 0) (E := 0) (us := []) (by simpa [unitLists] using nil_mem_wlists unitDataAt)
      (fun i => i.elim0)
    convert this using 1
    funext x; exact x.1.elim0

/-- **`SkeletonCodeLeg` over `𝒱_γ`** (main `skeletonCodeLeg`, via `skeletonCodeLegMk` at `Mk = ∅`): the structural
code leg, with the T-branch of the unit decoding (`chain_decode`, `vine_chain_codeG`). -/
theorem skeletonCodeLegG : SkeletonCodeLegG := by
  intro γ _ R S σ hS
  classical
  have hcard : Fintype.card (GBranch S.tree) = S.order := by
    rw [← Mole.garden_card_atoms S, ← Finset.card_univ]; rfl
  rw [← hcard]
  by_cases hne : Nonempty (GBranch S.tree)
  · obtain ⟨v0⟩ := hne
    exact skeletonCode_nonemptyMk S σ ∅ v0
  · exact skeletonCode_emptyMk S σ ∅ (not_nonempty_iff.mp hne)

end WaveTurbulence.GammaLow.Famc.ClassCount
