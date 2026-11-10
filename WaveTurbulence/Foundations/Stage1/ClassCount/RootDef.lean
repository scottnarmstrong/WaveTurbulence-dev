/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Irregular
public import WaveTurbulence.Foundations.Stage1.ClassCount.Lab
public import WaveTurbulence.Foundations.Stage1.ClassCount.BondSplit
public import WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.Stage1.ClassCount.Slots3
public import WaveTurbulence.Foundations.Molecule.GardenDeficitBound
import Mathlib.Tactic

/-!
# CLASSCOUNT: degree deficits

* the degree deficit `Σ_v (4 - deg v)` of a molecule with disjoint ladders is at most `16 (#ladders) + 4 (#free atoms)`
  (interior ladder atoms have degree `4`);
* the root things of a plain garden (`rootThings`) are bounded by its degree deficit.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sum_bb_le_deg (M : Molecule V D) {a : V} (B : Finset V) (haB : a ∉ B) :
    ∑ b ∈ B, M.bondsBetween a b ≤ M.deg a := by
  classical
  have h2 : ∑ b ∈ B, M.bondsBetween a b =
      ((M.dartsAt a).filter (fun x => M.atom (M.mate x) ∈ B)).card := by
    refine Eq.trans ?_ (Finset.card_eq_sum_card_fiberwise (f := fun x => M.atom (M.mate x)) (t := B)
      (fun x hx => Finset.mem_coe.mpr (Finset.mem_filter.mp hx).2)).symm
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := fun h => haB (h ▸ hb)
    rw [Mole.bondsBetween_eq_card_darts M hab]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨⟨hx, h ▸ hb⟩, h⟩
    · rintro ⟨⟨hx, _⟩, h⟩; exact ⟨hx, h⟩
  rw [h2]
  exact Finset.card_le_card (Finset.filter_subset _ _)

namespace LadderFam
variable {M : Molecule V D} {ι : Type} (F : LadderFam M ι) (i : ι)

theorem deg_int_u (j : Fin (F.len i + 1)) (h0 : j.1 ≠ 0) (hm' : j.1 ≠ F.len i) : 4 ≤ M.deg (F.u i j) := by
  have hm : 1 ≤ F.len i := (F.lad i).1
  have hjm : (⟨j.1 - 1, by omega⟩ : Fin (F.len i + 1)).1 + 1 = j.1 := by show j.1 - 1 + 1 = j.1; omega
  have hjp : (⟨j.1 + 1, by omega⟩ : Fin (F.len i + 1)).1 = j.1 + 1 := rfl
  have hne1 : F.v i j ≠ F.u i ⟨j.1 - 1, by omega⟩ := (ne_uv F i _ _).symm
  have hne2 : F.v i j ≠ F.u i ⟨j.1 + 1, by omega⟩ := (ne_uv F i _ _).symm
  have hne3 : F.u i ⟨j.1 - 1, by omega⟩ ≠ F.u i ⟨j.1 + 1, by omega⟩ := fun h => by
    have := congrArg Fin.val (inj_u F i h); dsimp only at this; omega
  have haB : F.u i j ∉ ({F.v i j, F.u i ⟨j.1 - 1, by omega⟩, F.u i ⟨j.1 + 1, by omega⟩} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne_uv F i _ _, fun h => ?_, fun h => ?_⟩
    · have := congrArg Fin.val (inj_u F i h); dsimp only at this; omega
    · have := congrArg Fin.val (inj_u F i h); dsimp only at this; omega
  have := sum_bb_le_deg M _ haB
  rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_pair hne3, bb_uv F i j, bb_uu' F i j _ hjm,
    bb_uu F i j _ hjp.symm] at this
  omega

theorem deg_int_v (j : Fin (F.len i + 1)) (h0 : j.1 ≠ 0) (hm' : j.1 ≠ F.len i) : 4 ≤ M.deg (F.v i j) := by
  have hm : 1 ≤ F.len i := (F.lad i).1
  have hjm : (⟨j.1 - 1, by omega⟩ : Fin (F.len i + 1)).1 + 1 = j.1 := by show j.1 - 1 + 1 = j.1; omega
  have hjp : (⟨j.1 + 1, by omega⟩ : Fin (F.len i + 1)).1 = j.1 + 1 := rfl
  have hne1 : F.u i j ≠ F.v i ⟨j.1 - 1, by omega⟩ := ne_uv F i _ _
  have hne2 : F.u i j ≠ F.v i ⟨j.1 + 1, by omega⟩ := ne_uv F i _ _
  have hne3 : F.v i ⟨j.1 - 1, by omega⟩ ≠ F.v i ⟨j.1 + 1, by omega⟩ := fun h => by
    have := congrArg Fin.val (inj_v F i h); dsimp only at this; omega
  have haB : F.v i j ∉ ({F.u i j, F.v i ⟨j.1 - 1, by omega⟩, F.v i ⟨j.1 + 1, by omega⟩} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨(ne_uv F i _ _).symm, fun h => ?_, fun h => ?_⟩
    · have := congrArg Fin.val (inj_v F i h); dsimp only at this; omega
    · have := congrArg Fin.val (inj_v F i h); dsimp only at this; omega
  have := sum_bb_le_deg M _ haB
  rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_pair hne3, bb_vu F i j, bb_vv' F i j _ hjm,
    bb_vv F i j _ hjp.symm] at this
  omega

theorem deficit_u (hM : M.IsMolecule) (j : Fin (F.len i + 1)) :
    4 - M.deg (F.u i j) ≤ 4 * ((if j.1 = 0 then 1 else 0) + (if j.1 = F.len i then 1 else 0)) := by
  by_cases h0 : j.1 = 0
  · simp [h0]; omega
  · by_cases hm' : j.1 = F.len i
    · simp [hm', h0]; omega
    · have := F.deg_int_u i j h0 hm'
      simp [h0, hm']; omega

theorem deficit_v (hM : M.IsMolecule) (j : Fin (F.len i + 1)) :
    4 - M.deg (F.v i j) ≤ 4 * ((if j.1 = 0 then 1 else 0) + (if j.1 = F.len i then 1 else 0)) := by
  by_cases h0 : j.1 = 0
  · simp [h0]; omega
  · by_cases hm' : j.1 = F.len i
    · simp [hm', h0]; omega
    · have := F.deg_int_v i j h0 hm'
      simp [h0, hm']; omega

theorem sum_deficit_ladder (hM : M.IsMolecule) :
    ∑ a ∈ F.atomsOf i, (4 - M.deg a) ≤ 16 := by
  classical
  have hm : 1 ≤ F.len i := (F.lad i).1
  unfold atomsOf Molecule.ladderAtoms
  have hdisj : Disjoint (univ.image (F.u i)) (univ.image (F.v i)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hb
    exact ne_uv F i x y hy.symm
  rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => inj_u F i h),
    Finset.sum_image (fun a _ b _ h => inj_v F i h)]
  calc ∑ j : Fin (F.len i + 1), (4 - M.deg (F.u i j)) + ∑ j : Fin (F.len i + 1), (4 - M.deg (F.v i j))
      ≤ ∑ j : Fin (F.len i + 1), 4 * ((if j.1 = 0 then 1 else 0) + (if j.1 = F.len i then 1 else 0)) +
        ∑ j : Fin (F.len i + 1), 4 * ((if j.1 = 0 then 1 else 0) + (if j.1 = F.len i then 1 else 0)) :=
        add_le_add (Finset.sum_le_sum fun j _ => F.deficit_u i hM j) (Finset.sum_le_sum fun j _ => F.deficit_v i hM j)
    _ = 16 := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_ite_fin _ 0 (by omega), sum_ite_fin _ _ (by omega)]
      norm_num

end LadderFam

/-- **Degree deficit of a molecule with disjoint ladders.** -/
theorem sum_deficit_le (M : Molecule V D) (hM : M.IsMolecule) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : LadderFam M ι) (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j)) :
    ∑ a ∈ M.atoms, (4 - M.deg a) ≤
      4 * (M.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 16 * Fintype.card ι := by
  classical
  set free := M.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i) with hfree
  have hsub : M.atoms ⊆ free ∪ (univ : Finset ι).biUnion F.atomsOf := by
    intro a ha
    by_cases h : ∃ i, a ∈ F.atomsOf i
    · obtain ⟨i, hi⟩ := h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
    · push_neg at h
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, h⟩)
  have hd : Disjoint free ((univ : Finset ι).biUnion F.atomsOf) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hb
    exact (Finset.mem_filter.mp ha).2 i hi
  have hpw : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint F.atomsOf := fun i _ j _ hij => hdisj i j hij
  calc ∑ a ∈ M.atoms, (4 - M.deg a)
      ≤ ∑ a ∈ free ∪ (univ : Finset ι).biUnion F.atomsOf, (4 - M.deg a) :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ a ∈ free, (4 - M.deg a) + ∑ i : ι, ∑ a ∈ F.atomsOf i, (4 - M.deg a) := by
        rw [Finset.sum_union hd, Finset.sum_biUnion hpw]
    _ ≤ ∑ a ∈ free, 4 + ∑ i : ι, 16 :=
        add_le_add (Finset.sum_le_sum fun a _ => Nat.sub_le _ _)
          (Finset.sum_le_sum fun i _ => F.sum_deficit_ladder i hM)
    _ = 4 * free.card + 16 * Fintype.card ι := by simp [mul_comm]

section splice
variable {V' D' : Type*} [DecidableEq V'] [Fintype D'] [DecidableEq D']

/-- At a non-hinge atom the splice does not decrease the degree: `deg_{M'} c ≤ deg_M (ob c)`. -/
theorem deg_le_of_not_hinge {M : Molecule V D} {M' : Molecule V' D'} (SD : SpliceData M M') (c : V')
    (hc : ∀ i, i < SD.q → SD.ob c ≠ SD.rep i) : M'.deg c ≤ M.deg (SD.ob c) := by
  classical
  unfold Molecule.deg
  refine Finset.card_le_card_of_injOn SD.od ?_ (fun a _ b _ h => SD.od_inj h)
  intro y hy
  have hya : M'.atom y = c := (Finset.mem_filter.1 hy).2
  rw [Finset.mem_coe, Molecule.dartsAt, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have h1 : SD.ob c = SD.cl (M.atom (SD.od y)) := by rw [← hya]; exact SD.ob_atom y
  by_cases hU : ∃ i, i < SD.q ∧ M.atom (SD.od y) ∈ SD.U i
  · obtain ⟨i, hi, hmem⟩ := hU
    exact absurd (h1.trans (SD.cl_unit i hi _ hmem)) (hc i hi)
  · push_neg at hU
    rw [SD.cl_free _ hU] at h1
    exact h1.symm

/-- **Degree deficit of the skeleton versus the spliced molecule.** -/
theorem deficit_splice_le {M : Molecule V D} {M' : Molecule V' D'} (SD : SpliceData M M')
    (hMa : ∀ v, v ∈ M.atoms) (hM'a : ∀ c, c ∈ M'.atoms) (hM : M.IsMolecule) (hM' : M'.IsMolecule) (low : ℕ → V)
    (hint : ∀ i, i < SD.q → ∀ v ∈ SD.U i, v ≠ SD.rep i → v ≠ low i → 4 ≤ M.deg v) :
    ∑ v ∈ M.atoms, (4 - M.deg v) ≤ ∑ c ∈ M'.atoms, (4 - M'.deg c) + 8 * SD.q := by
  classical
  set d : V → ℕ := fun v => 4 - M.deg v with hd
  have hdle : ∀ v, d v ≤ 4 := fun v => Nat.sub_le _ _
  set Fx := M.atoms.filter (fun v => SD.cl v = v) with hFx
  set Un := M.atoms.filter (fun v => ¬ SD.cl v = v) with hUn
  have hsplit : ∑ v ∈ M.atoms, d v = ∑ v ∈ Fx, d v + ∑ v ∈ Un, d v :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the unit atoms
  have hun : ∑ v ∈ Un, d v ≤ 4 * SD.q := by
    have hsub : Un ⊆ (Finset.range SD.q).biUnion (fun i => (SD.U i).erase (SD.rep i)) := by
      intro v hv
      obtain ⟨-, hne⟩ := Finset.mem_filter.1 hv
      have hU : ∃ i, i < SD.q ∧ v ∈ SD.U i := by
        by_contra hno; push_neg at hno; exact hne (SD.cl_free _ hno)
      obtain ⟨i, hi, hmem⟩ := hU
      refine Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, Finset.mem_erase.2 ⟨?_, hmem⟩⟩
      intro h; apply hne; rw [SD.cl_unit i hi v hmem, h]
    refine (Finset.sum_le_sum_of_subset hsub).trans ?_
    refine (sum_biUnion_le_nat _ _ _).trans ?_
    calc ∑ i ∈ Finset.range SD.q, ∑ v ∈ (SD.U i).erase (SD.rep i), d v ≤ ∑ i ∈ Finset.range SD.q, 4 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          calc ∑ v ∈ (SD.U i).erase (SD.rep i), d v ≤ ∑ v ∈ (SD.U i).erase (SD.rep i), (if v = low i then 4 else 0) := by
                refine Finset.sum_le_sum fun v hv => ?_
                obtain ⟨hv1, hv2⟩ := Finset.mem_erase.1 hv
                by_cases hvl : v = low i
                · simp [hvl, hdle]
                · have := hint i hi' v hv2 hv1 hvl
                  simp only [hd, hvl, if_false]; omega
            _ ≤ 4 := by
                rw [Finset.sum_ite_eq']; split_ifs <;> omega
      _ = 4 * SD.q := by simp [mul_comm]
  -- the fixed atoms
  have hfx : ∑ v ∈ Fx, d v ≤ ∑ c ∈ M'.atoms, (4 - M'.deg c) + 4 * SD.q := by
    have himg : Fx = M'.atoms.image SD.ob := by
      ext v
      simp only [hFx, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨-, hv⟩
        obtain ⟨c, hc⟩ := (SD.ob_range v).2 hv
        exact ⟨c, hM'a c, hc⟩
      · rintro ⟨c, -, rfl⟩
        exact ⟨hMa _, (SD.ob_range _).1 ⟨c, rfl⟩⟩
    rw [himg, Finset.sum_image (fun a _ b _ h => SD.ob_inj h)]
    set Hc := M'.atoms.filter (fun c => ∃ i, i < SD.q ∧ SD.ob c = SD.rep i) with hHc
    have hHcard : Hc.card ≤ SD.q := by
      have hsub : Hc ⊆ (Finset.range SD.q).biUnion (fun i => M'.atoms.filter (fun c => SD.ob c = SD.rep i)) := by
        intro c hc
        obtain ⟨hc1, i, hi, hci⟩ := Finset.mem_filter.1 hc
        exact Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, Finset.mem_filter.2 ⟨hc1, hci⟩⟩
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
      calc ∑ i ∈ Finset.range SD.q, (M'.atoms.filter (fun c => SD.ob c = SD.rep i)).card
          ≤ ∑ i ∈ Finset.range SD.q, 1 := by
            refine Finset.sum_le_sum fun i _ => Finset.card_le_one.2 ?_
            intro a ha b hb
            exact SD.ob_inj ((Finset.mem_filter.1 ha).2.trans (Finset.mem_filter.1 hb).2.symm)
        _ = SD.q := by simp
    calc ∑ c ∈ M'.atoms, d (SD.ob c) ≤ ∑ c ∈ M'.atoms, ((4 - M'.deg c) + (if c ∈ Hc then 4 else 0)) := by
          refine Finset.sum_le_sum fun c hc => ?_
          by_cases hh : c ∈ Hc
          · simp only [hh, if_true]; have := hdle (SD.ob c); omega
          · simp only [hh, if_false, add_zero]
            have hnh : ∀ i, i < SD.q → SD.ob c ≠ SD.rep i := by
              intro i hi he; exact hh (Finset.mem_filter.2 ⟨hc, i, hi, he⟩)
            have := deg_le_of_not_hinge SD c hnh
            simp only [hd]; omega
      _ = ∑ c ∈ M'.atoms, (4 - M'.deg c) + 4 * Hc.card := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
            Finset.inter_eq_right.2 (Finset.filter_subset _ _), Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := by have := Nat.mul_le_mul_left 4 hHcard; omega
  rw [show (∑ v ∈ M.atoms, (4 - M.deg v)) = ∑ v ∈ Fx, d v + ∑ v ∈ Un, d v from hsplit]
  omega

end splice

section garden
open WaveTurbulence.Reg.Skeleton TTree
variable {w : ℕ} {S : Garden w}

/-- **The root things are bounded by the degree deficit of the skeleton molecule.** -/
theorem rootThings_le_deficit (hS : S.IsPlain) :
    rootThings hS ≤ ∑ v ∈ S.molecule.atoms, (4 - S.molecule.deg v) := by
  classical
  let BN := univ.filter (fun c : GBranch S.tree => c.1.2 ≠ [])
  let B0 := univ.filter (fun c : GBranch S.tree => c.1.2 = [])
  let L0 := univ.filter (fun l : GLeaf S.tree => l.1.2 = [])
  let LP0 := univ.filter (fun l : GLeaf S.tree => (S.pair l).1.2 = [])
  let LE := univ.filter (fun l : GLeaf S.tree =>
    S.mark l = none ∧ l.1.2 ≠ [] ∧ (S.pair l).1.2 ≠ [])
  have hB : BN.card + B0.card = S.order := by
    have hh := (univ : Finset (GBranch S.tree)).card_filter_add_card_filter_not
      (fun c => c.1.2 ≠ [])
    simpa only [not_not, card_univ, Mole.card_gbranch, BN, B0, Garden.order] using hh
  have hroots : B0.card + L0.card = w := Mole.card_root_branches_add_leaves S.tree
  have hLP0 : LP0.card = L0.card := by
    apply Finset.card_bij (fun l _hl => S.pair l)
    · intro l hl
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hl).2⟩
    · intro l hl m hm he
      have hh := congrArg S.pair he
      simpa only [S.pair_pair] using hh
    · intro l hl
      exact ⟨S.pair l, mem_filter.mpr ⟨mem_univ _, by simpa only [S.pair_pair] using
        (mem_filter.mp hl).2⟩, S.pair_pair l⟩
  have hcomp : univ.filter (fun l : GLeaf S.tree =>
      ¬ (S.mark l = none ∧ l.1.2 ≠ [] ∧ (S.pair l).1.2 ≠ [])) = L0 ∪ LP0 := by
    ext l
    simp only [mem_filter, mem_univ, true_and, mem_union, L0, LP0, hS l, true_and, not_and_or, not_not]
    tauto
  have hL : LE.card + (L0 ∪ LP0).card = 2 * S.order + w := by
    have hh := (univ : Finset (GLeaf S.tree)).card_filter_add_card_filter_not
      (fun l => S.mark l = none ∧ l.1.2 ≠ [] ∧ (S.pair l).1.2 ≠ [])
    rw [hcomp, card_univ, Mole.card_gleaf] at hh
    exact hh
  have hD : Fintype.card (GardenDart S) = BN.card * 2 + LE.card := by
    simp only [GardenDart, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype]
    rfl
  have hE := Mole.two_mul_card_bonds S.molecule
  have hdeg := Mole.sum_degrees_eq_two_mul_bonds S.molecule
  have hsum : ∑ v ∈ S.molecule.atoms, (4 - S.molecule.deg v) = 4 * S.order - 2 * S.molecule.bonds.card := by
    rw [Finset.sum_tsub_distrib _ (fun v _ => Mole.garden_molecule_deg_le_four S v), hdeg]
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Mole.garden_card_atoms]
    rw [mul_comm]
  -- the couples with exactly one root leaf inject into the non-root leaves with a root partner
  have hc : (Finset.univ.filter (fun pr : SourcePair S => exactOne hS pr)).card ≤ (LP0 \ L0).card := by
    let φ : SourcePair S → GLeaf S.tree := fun pr =>
      if (pr.firstLeaf hS).1.2 = [] then pr.secondLeaf hS else pr.firstLeaf hS
    have hpair : ∀ pr : SourcePair S, S.pair (pr.firstLeaf hS) = pr.secondLeaf hS ∧
        S.pair (pr.secondLeaf hS) = pr.firstLeaf hS := by
      intro pr
      obtain ⟨ℓ, -, h1, h2⟩ := sourcePair_facts hS pr
      rw [h1, h2]; exact ⟨rfl, S.pair_pair ℓ⟩
    have hφ : ∀ pr ∈ Finset.univ.filter (fun pr : SourcePair S => exactOne hS pr), φ pr ∈ LP0 \ L0 := by
      intro pr hpr
      have hx : exactOne hS pr := (Finset.mem_filter.1 hpr).2
      obtain ⟨hp1, hp2⟩ := hpair pr
      simp only [LP0, L0, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [φ, if_pos h1]
        exact ⟨by rw [hp2]; exact h1, h2⟩
      · simp only [φ, if_neg h1]
        exact ⟨by rw [hp1]; exact h2, h1⟩
    refine Finset.card_le_card_of_injOn φ hφ ?_
    intro pr hpr pr' hpr' he
    have hx : exactOne hS pr := (Finset.mem_filter.1 hpr).2
    have hx' : exactOne hS pr' := (Finset.mem_filter.1 hpr').2
    have hend : ∀ q : SourcePair S, φ q = q.firstLeaf hS ∨ φ q = q.secondLeaf hS := by
      intro q; simp only [φ]; split_ifs <;> simp
    have hle : ∀ q : SourcePair S, (q : Pair w) = sourcePairAt S (φ q) := by
      intro q
      apply sourcePairs_eq_at S hS q.1 q.2 (φ q)
      rcases hend q with h | h
      · left; rw [h]; rfl
      · right; rw [h]; rfl
    exact Subtype.ext ((hle pr).trans ((congrArg (sourcePairAt S) he).trans (hle pr').symm))
  have hu : (L0 ∪ LP0).card = L0.card + (LP0 \ L0).card := by
    rw [Finset.union_comm, ← Finset.card_sdiff_add_card, add_comm]
  unfold rootThings
  rw [hsum]
  have h1 : B0.card = (Finset.univ.filter (fun b : GBranch S.tree => b.1.2 = [])).card := rfl
  omega

end garden

section inst
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Reg.Skeleton
variable {w : ℕ}

theorem degIn_le_deg {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (S : Finset V) (v : V) : M.degIn S v ≤ M.deg v := by
  classical
  unfold Molecule.degIn Molecule.deg
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- B2d: **the root things are bounded by `16 ρ̄`** at any marked set. -/
theorem rootThings_leMk (S : Garden w) (hS : S.IsPlain) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) :
    rootThings hS ≤ 16 * ((stSt S σ Mk).G.molecule.rho + (unitBlocks S σ Mk).length) := by
  classical
  have hM := Mole.garden_isMolecule S
  have hM' := Mole.garden_isMolecule (stSt S σ Mk).G
  refine (rootThings_le_deficit hS).trans ?_
  by_cases hne : Nonempty (GBranch S.tree)
  · obtain ⟨v0⟩ := hne
    set SD := spliceDataOfMk S hM σ Mk v0 with hSD
    have hint : ∀ i, i < SD.q → ∀ v ∈ SD.U i, v ≠ SD.rep i →
        v ≠ (fun i => if h : i < (unitBlocks S σ Mk).length then ((unitBlocks S σ Mk).get ⟨i, h⟩).lower else v0) i →
        4 ≤ S.molecule.deg v := by
      intro i hi v hv hvr hvl
      rw [spliceDataOf_UMk S hM σ Mk v0 hi] at hv
      rw [spliceDataOf_repMk S hM σ Mk v0 hi] at hvr
      have hvl' : v ≠ ((unitBlocks S σ Mk).get ⟨i, hi⟩).lower := by
        have hi' : i < (unitBlocks S σ Mk).length := hi
        intro h; apply hvl; show v = if h : i < (unitBlocks S σ Mk).length then _ else _
        rw [dif_pos hi']; exact h
      have hB := ((unitBlocks S σ Mk).get ⟨i, hi⟩).isBlock
      have := hB.2.2.2.2.2.2.2.2.1 v hv hvr hvl'
      exact this ▸ degIn_le_deg S.molecule _ v
    have h1 := deficit_splice_le SD (fun v => Finset.mem_univ v) (fun c => Finset.mem_univ c) hM hM' _ hint
    have h2 := sum_deficit_le (stSt S σ Mk).G.molecule hM' (ladderFamOf (stSt S σ Mk).G) (ladderFamOf_disj (stSt S σ Mk).G hM')
    have h3 := ladderFamOf_r (stSt S σ Mk).G
    have h4 : SD.q = (unitBlocks S σ Mk).length := rfl
    omega
  · have hemp : IsEmpty (GBranch S.tree) := not_nonempty_iff.1 hne
    have : ∑ v ∈ S.molecule.atoms, (4 - S.molecule.deg v) = 0 :=
      Finset.sum_eq_zero fun v _ => (hemp.false v).elim
    omega

end inst

end WaveTurbulence.ClassCount
