/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Lab
public import WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonLeg
public import WaveTurbulence.Foundations.WaveB.Ladders
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
import Mathlib.Tactic

/-!
# CLASSCOUNT: `SkeletonCodeLeg` from the abstract LAB lemma

The molecule of a plain skeleton `S` with a prescription `σ` and the molecule of its spliced garden `(stSt S σ).G`
form a `SpliceData`: `ob`, `od` from the `SpMap`, units `unitBlocks S σ` with representatives `u.upper`, classes `repC cls`.
-/

@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Stage1
  WaveTurbulence.Reg.Skeleton

variable {w : ℕ}

/-- B1b (Mk-general form of `cls_same_iff`). -/
theorem cls_same_iffMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (p p' : GBranch S.tree) {Mk : Set (Stage1.CLVine _)} :
    (∃ a, (stSt (Mk := Mk) S σ).cls p = some a ∧ (stSt (Mk := Mk) S σ).cls p' = some a) ↔
      ∃ i : ℕ, ∃ hi : i < (unitBlocks (Mk := Mk) S σ).length,
        p ∈ ((unitBlocks (Mk := Mk) S σ).get ⟨i, hi⟩).atoms ∧ p' ∈ ((unitBlocks (Mk := Mk) S σ).get ⟨i, hi⟩).atoms := by
  constructor
  · rintro ⟨a, h1, h2⟩
    have hp : ∃ u ∈ unitBlocks (Mk := Mk) S σ, p ∈ u.atoms := by
      by_contra hno
      push Not at hno
      rw [stSt_cls_noneMk (Mk := Mk) hM σ hno] at h1; exact absurd h1 (by simp)
    have hp' : ∃ u ∈ unitBlocks (Mk := Mk) S σ, p' ∈ u.atoms := by
      by_contra hno
      push Not at hno
      rw [stSt_cls_noneMk (Mk := Mk) hM σ hno] at h2; exact absurd h2 (by simp)
    obtain ⟨u, hu, hpu⟩ := hp
    obtain ⟨u', hu', hpu'⟩ := hp'
    have e1 := stSt_cls_memMk (Mk := Mk) hM σ hu hpu
    have e2 := stSt_cls_memMk (Mk := Mk) hM σ hu' hpu'
    rw [e1] at h1; rw [e2] at h2
    have hup : u.upper = u'.upper := (Option.some.inj h1).trans (Option.some.inj h2).symm
    have : u = u' := by
      apply units_eq_of_not_disjointMk (Mk := Mk) hM σ hu hu'
      rw [Finset.not_disjoint_iff]
      exact ⟨u.upper, u.isBlock.2.1, hup ▸ u'.isBlock.2.1⟩
    subst this
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
    exact ⟨i.1, i.2, by rw [show (⟨i.1, i.2⟩ : Fin _) = i from rfl, hi]; exact ⟨hpu, hpu'⟩⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨_, stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) h1, stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) h2⟩

theorem cls_same_iff (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (p p' : GBranch S.tree) :
    (∃ a, (stSt S σ).cls p = some a ∧ (stSt S σ).cls p' = some a) ↔
      ∃ i : ℕ, ∃ hi : i < (unitBlocks S σ).length,
        p ∈ ((unitBlocks S σ).get ⟨i, hi⟩).atoms ∧ p' ∈ ((unitBlocks S σ).get ⟨i, hi⟩).atoms := cls_same_iffMk (Mk := ∅) S hM σ p p'

/-- The `SpliceData` of a skeleton and its spliced garden. -/
noncomputable def spliceDataOf (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (v0 : GBranch S.tree) : SpliceData S.molecule (stSt S σ).G.molecule where
  ob := (stSt S σ).M.ob
  od := (stSt S σ).M.od
  q := (unitBlocks S σ).length
  U := fun i => if h : i < (unitBlocks S σ).length then ((unitBlocks S σ).get ⟨i, h⟩).atoms else ∅
  rep := fun i => if h : i < (unitBlocks S σ).length then ((unitBlocks S σ).get ⟨i, h⟩).upper else v0
  cl := repC (stSt S σ).cls
  ob_inj := (stSt S σ).M.ob_inj
  od_inj := (stSt S σ).M.od_inj
  od_mate := (stSt S σ).M.od_mate
  od_out := (stSt S σ).M.od_out
  U_disj := by
    intro i j hi hj hij
    simp only [dif_pos hi, dif_pos hj]
    have hp := List.pairwise_iff_get.mp (unitBlocks_pairwise hM σ)
    rcases lt_or_gt_of_ne hij with h | h
    · exact hp ⟨i, hi⟩ ⟨j, hj⟩ h
    · exact (hp ⟨j, hj⟩ ⟨i, hi⟩ h).symm
  rep_mem := by
    intro i hi
    simp only [dif_pos hi]
    exact ((unitBlocks S σ).get ⟨i, hi⟩).isBlock.2.1
  cl_unit := by
    intro i hi v hv
    simp only [dif_pos hi] at hv ⊢
    exact stSt_repC_mem hM σ (List.get_mem _ _) hv
  cl_free := by
    intro v hv
    refine stSt_repC_none hM σ (fun u hu hvu => ?_)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
    have := hv i.1 i.2
    simp only [dif_pos i.2] at this
    rw [show (⟨i.1, i.2⟩ : Fin _) = i from rfl, hi] at this
    exact this hvu
  ob_atom := (stSt S σ).M.ob_atom
  ob_range := by
    intro v
    rw [(stSt S σ).M.ob_range]
    simp only [repC]
    cases h : (stSt S σ).cls v <;> simp
  od_range := by
    intro x
    rw [(stSt S σ).M.od_range]
    refine not_congr ?_
    rw [cls_same_iff S hM σ]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by simpa [dif_pos hi] using h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by simpa [dif_pos hi] using h⟩


theorem spliceDataOf_U (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (v0 : GBranch S.tree)
    {i : ℕ} (hi : i < (unitBlocks S σ).length) :
    (spliceDataOf S hM σ v0).U i = ((unitBlocks S σ).get ⟨i, hi⟩).atoms := by
  simp [spliceDataOf, dif_pos hi]

theorem spliceDataOf_rep (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (v0 : GBranch S.tree)
    {i : ℕ} (hi : i < (unitBlocks S σ).length) :
    (spliceDataOf S hM σ v0).rep i = ((unitBlocks S σ).get ⟨i, hi⟩).upper := by
  simp [spliceDataOf, dif_pos hi]

theorem spliceDataOf_q (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S) (v0 : GBranch S.tree) :
    (spliceDataOf S hM σ v0).q = (unitBlocks S σ).length := rfl

/-- The ladders of the spliced garden as a `LadderFam`. -/
noncomputable def ladderFamOf (G : Garden w) : LadderFam G.molecule {T // T ∈ G.molecule.maximalLadders} where
  len := (ladderDataOf G).length
  u := (ladderDataOf G).upper
  v := (ladderDataOf G).lower
  lad := (ladderDataOf G).ladder

theorem ladderFamOf_atomsOf (G : Garden w) (i : {T // T ∈ G.molecule.maximalLadders}) :
    (ladderFamOf G).atomsOf i = i.1 := (ladderDataOf G).atoms i

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


/-- **`SkeletonCodeLeg`** (nonempty case). -/
theorem skeletonCode_nonempty {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S) (v0 : GBranch S.tree) :
    ∃ nsb : ℕ, nsb ≤ Fintype.card (GBranch S.tree) ∧ ∃ ℓ : GBranch S.tree ≃ Fin (Fintype.card (GBranch S.tree)),
      ∃ L ∈ arcLists (Fintype.card (GBranch S.tree)) (4 * rbarOf S σ)
          (unitFamily (Fintype.card (GBranch S.tree)) nsb (rbarOf S σ) (Fintype.card (GBranch S.tree) - nsb)),
        ∀ x : Fin (Fintype.card (GBranch S.tree)) × Fin (Fintype.card (GBranch S.tree)),
          Fintype.card {b : {y : GardenDart S // S.molecule.out y = true} //
            (ℓ (S.molecule.atom b.1), ℓ (S.molecule.atom (S.molecule.mate b.1))) = x} = L.count x := by
  classical
  have hM := Mole.garden_isMolecule S
  have hM' := Mole.garden_isMolecule (stSt S σ).G
  let SD := spliceDataOf S hM σ v0
  have hex : ∀ i : ℕ, ∃ (c : List IngCode) (l : GBranch S.tree → ℕ), ∀ h : i < SD.q,
      (∀ d ∈ c, d.Wf) ∧ Set.InjOn l (SD.U i) ∧ (SD.U i).image l = Finset.range (unitWeight c + 1) ∧
      groupArcs S.molecule (SD.U i) l = ((unitArcs c : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
    intro i
    by_cases h : i < SD.q
    · obtain ⟨cs, hwf, lab, hinj, himg, harcs⟩ :=
        unit_decode S hM σ (u := (unitBlocks S σ).get ⟨i, h⟩) (List.get_mem _ _)
      have hU := spliceDataOf_U S hM σ v0 (show i < (unitBlocks S σ).length from h)
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
      have hb := ((unitBlocks S σ).get ⟨i, hi⟩).isBlock
      have hU := spliceDataOf_U S hM σ v0 (show i < (unitBlocks S σ).length from hi)
      rw [hU]
      have hne : ((unitBlocks S σ).get ⟨i, hi⟩).upper ≠ ((unitBlocks S σ).get ⟨i, hi⟩).lower := hb.2.2.2.1
      have : ({((unitBlocks S σ).get ⟨i, hi⟩).upper, ((unitBlocks S σ).get ⟨i, hi⟩).lower} : Finset _) ⊆
          ((unitBlocks S σ).get ⟨i, hi⟩).atoms := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hb.2.1
        · exact hb.2.2.1
      have := Finset.card_le_card this
      rwa [Finset.card_pair hne] at this
    have := hcardU i hi
    omega
  have hH : ∀ c, (∃ i, i < SD.q ∧ SD.ob c = SD.rep i) → c ∈ (stSt S σ).hinges := by
    rintro c ⟨i, hi, hc⟩
    rw [SpState.mem_hinges]
    have hc' : (stSt S σ).M.ob c = ((unitBlocks S σ).get ⟨i, hi⟩).upper := by
      have : SD.ob c = SD.rep i := hc
      rw [spliceDataOf_rep S hM σ v0 (show i < (unitBlocks S σ).length from hi)] at this
      exact this
    rw [hc']
    have := stSt_cls_mem hM σ (List.get_mem (unitBlocks S σ) ⟨i, hi⟩) ((unitBlocks S σ).get ⟨i, hi⟩).isBlock.2.1
    rw [this]; simp
  obtain ⟨nsb, hnsb, ℓ, L, hL, hcount⟩ := SD.lab_arcs hM hM' (fun v => Finset.mem_univ v)
    (ladderFamOf (stSt S σ).G) (ladderFamOf_disj (stSt S σ).G hM') (stSt S σ).hinges hH cs W lab
    (fun i hi => (hprop i hi).1) hW (fun i hi => (hprop i hi).2.1) (fun i hi => (hprop i hi).2.2.1)
    (fun i hi => (hprop i hi).2.2.2)
  have hr : (((stSt S σ).G.molecule.atoms.filter (fun a => ∀ i, a ∉ (ladderFamOf (stSt S σ).G).atomsOf i)).card +
      Fintype.card {T // T ∈ (stSt S σ).G.molecule.maximalLadders} + (stSt S σ).hinges.card) =
      rbarOf S σ := by
    have := ladderFamOf_r (stSt S σ).G
    unfold rbarOf
    rw [← this]
    simp only [collectionChoices]
  rw [hr] at hL
  exact ⟨nsb, hnsb, ℓ, L, hL, hcount⟩


/-- In the empty case there is nothing to code. -/
theorem skeletonCode_empty {R : ℕ} (S : Garden (2 * R)) (σ : Prescription S) (hE : IsEmpty (GBranch S.tree)) :
    ∃ nsb : ℕ, nsb ≤ Fintype.card (GBranch S.tree) ∧ ∃ ℓ : GBranch S.tree ≃ Fin (Fintype.card (GBranch S.tree)),
      ∃ L ∈ arcLists (Fintype.card (GBranch S.tree)) (4 * rbarOf S σ)
          (unitFamily (Fintype.card (GBranch S.tree)) nsb (rbarOf S σ) (Fintype.card (GBranch S.tree) - nsb)),
        ∀ x : Fin (Fintype.card (GBranch S.tree)) × Fin (Fintype.card (GBranch S.tree)),
          Fintype.card {b : {y : GardenDart S // S.molecule.out y = true} //
            (ℓ (S.molecule.atom b.1), ℓ (S.molecule.atom (S.molecule.mate b.1))) = x} = L.count x := by
  classical
  have h0 : Fintype.card (GBranch S.tree) = 0 := Fintype.card_eq_zero
  have hM := Mole.garden_isMolecule S
  -- the spliced garden has no atoms
  have hE' : IsEmpty (GBranch (stSt S σ).G.tree) :=
    ⟨fun c => hE.false ((stSt S σ).M.ob c)⟩
  have hr : rbarOf S σ = 0 := by
    unfold rbarOf
    have h1 : (stSt S σ).G.molecule.rho = 0 := by
      unfold Molecule.rho Molecule.numLadders Molecule.numFree
      have hl : (stSt S σ).G.molecule.maximalLadders = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro T hT
        simp only [Molecule.maximalLadders, Finset.mem_filter] at hT
        obtain ⟨-, ⟨m, u, v, hu, -⟩, -⟩ := hT
        exact hE'.false (u 0)
      have hf : ((stSt S σ).G.molecule.atoms.filter (fun v => ∀ T ∈ (stSt S σ).G.molecule.maximalLadders, v ∉ T)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v; exact hE'.elim v
      have ha : (stSt S σ).G.molecule.atoms = ∅ :=
        Finset.eq_empty_of_forall_notMem (fun v _ => hE'.elim v)
      simp [hl, hf, ha]
    have h2 : (collectionChoices S σ).hinges.card = 0 := by
      simp only [collectionChoices]
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

theorem skeletonCodeLeg : SkeletonCodeLeg := by
  intro R S σ hS
  classical
  have hcard : Fintype.card (GBranch S.tree) = S.order := by
    rw [← Mole.garden_card_atoms S, ← Finset.card_univ]; rfl
  rw [← hcard]
  by_cases hne : Nonempty (GBranch S.tree)
  · obtain ⟨v0⟩ := hne
    exact skeletonCode_nonempty S σ v0
  · exact skeletonCode_empty S σ (not_nonempty_iff.mp hne)

end WaveTurbulence.ClassCount
