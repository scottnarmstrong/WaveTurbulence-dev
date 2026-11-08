/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItemsMK
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleHingeR83
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: `TripleDesignated` for `collectionChoices G σ Mk` (R37/R48 with survivors)

Every triple bond of `G_sb` has a hinge endpoint whose chosen pair consists of two bonds of the triple bond.
* `pair_in_triple_of_obj` (generic): a pair of a vine-like object at its joint lies in every triple bond at that joint
  (an object has at most three of its own darts at a joint, `joint_inGroup_card_le`; an atom has degree `≤ 4`).
  This covers the hinges that are joints of an object of `𝒞₁` (main's pair lies in the object) and the run hinges
  of marked groups (the 75-F1 pair lies in a survivor).
* A run hinge of a marked group has no triple bond to another group (`marked_crown_no_triple`).
* The whole-group hinges of unmarked groups: main's R37 argument (`whole_pair_in_tripleMk`, Mk copies of
  `tripleDarts`, `mem_tripleDarts`, `card_tripleDarts`, `core_comb`, `od_mem_tripleDarts`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.RedSplice WaveTurbulence.VineA.NormalizedSplice.Subpro
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem inGroup_of_containsDart (O : Object M) {x : D} (h : O.ContainsDart x) : M.InGroup O.atoms x := by
  unfold Object.ContainsDart at h
  split at h
  · exact h
  · exact h.2.2

/-- **At a joint of a vine-like object, at most three darts have both ends in the object** (two for a vine; for an HV
the added bond may add one). -/
theorem joint_inGroup_card_le (O : Object M) {v : V} (hj : v = O.upper ∨ v = O.lower) :
    ((M.dartsAt v).filter (fun x => M.InGroup O.atoms x)).card ≤ 3 := by
  classical
  obtain ⟨A, a, b, sh⟩ := O
  simp only at hj ⊢
  cases sh with
  | vc h =>
    have hd := block_joint_degrees M h.1
    have : M.degIn A v = 2 := by rcases hj with rfl | rfl; exact hd.1; exact hd.2
    unfold Molecule.degIn at this
    omega
  | hyper R =>
    have hB := R.adjoint.1
    have hd := block_joint_degrees _ hB
    have hdeg : (Molecule.eraseBond M R.added).degIn A v = 2 := by rcases hj with rfl | rfl; exact hd.1; exact hd.2
    unfold Molecule.degIn at hdeg
    set F := (M.dartsAt v).filter (fun x => M.InGroup A x) with hF
    have h1 : (F.filter (fun x => x ≠ R.added ∧ x ≠ M.mate R.added)).card ≤ 2 := by
      rw [← hdeg]
      refine le_trans (Finset.card_le_card (t := (((Molecule.eraseBond M R.added).dartsAt v).filter
          (fun x => (Molecule.eraseBond M R.added).InGroup A x)).image Subtype.val) ?_) Finset.card_image_le
      intro x hx
      rw [Finset.mem_filter, hF, Finset.mem_filter] at hx
      refine Finset.mem_image.mpr ⟨⟨x, hx.2⟩, ?_, rfl⟩
      rw [Finset.mem_filter, Mole.mem_dartsAt]
      exact ⟨(Mole.mem_dartsAt M v x).mp hx.1.1, hx.1.2⟩
    have hab : M.atom R.added ≠ M.atom (M.mate R.added) := by
      intro h
      have he := R.ends_eq
      unfold Molecule.ends at he
      rw [h] at he
      rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hB.2.2.2.1 (e1.symm.trans e2)
      · exact hB.2.2.2.1 (e2.symm.trans e1)
    have h2 : (F.filter (fun x => ¬ (x ≠ R.added ∧ x ≠ M.mate R.added))).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun x hx y hy => ?_
      rw [Finset.mem_filter, hF, Finset.mem_filter, Mole.mem_dartsAt] at hx hy
      have hx2 : x = R.added ∨ x = M.mate R.added := by tauto
      have hy2 : y = R.added ∨ y = M.mate R.added := by tauto
      rcases hx2 with rfl | rfl <;> rcases hy2 with rfl | rfl
      · rfl
      · exact absurd (hx.1.1.trans hy.1.1.symm) hab
      · exact absurd (hy.1.1.trans hx.1.1.symm) hab
      · rfl
    have := Finset.card_filter_add_card_filter_not (s := F) (fun x => x ≠ R.added ∧ x ≠ M.mate R.added)
    omega

/-- Two distinct darts at `c` not leading to `v` leave room for at most two bonds from `c` to `v`. -/
theorem no_triple_of_two (hM : M.IsMolecule) {c v : V} (hcv : c ≠ v) {x y : D} (hx : M.atom x = c)
    (hy : M.atom y = c) (hxy : x ≠ y) (nx : M.atom (M.mate x) ≠ v) (ny : M.atom (M.mate y) ≠ v) :
    M.bondsBetween c v ≠ 3 := by
  classical
  intro h3
  rw [Mole.bondsBetween_eq_card_darts M hcv] at h3
  set X := (M.dartsAt c).filter (fun d => M.atom (M.mate d) = v) with hX
  have hsub : insert x (insert y X) ⊆ M.dartsAt c := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_insert, hX, Finset.mem_filter] at hd
    rcases hd with rfl | rfl | hd
    · exact (Mole.mem_dartsAt M c _).mpr hx
    · exact (Mole.mem_dartsAt M c _).mpr hy
    · exact hd.1
  have hyX : y ∉ X := by rw [hX, Finset.mem_filter]; exact fun h => ny h.2
  have hxX : x ∉ insert y X := by
    rw [Finset.mem_insert, hX, Finset.mem_filter]
    rintro (h | h)
    · exact hxy h
    · exact nx h.2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxX, Finset.card_insert_of_notMem hyX, h3] at hcard
  have hcm : c ∈ M.atoms := hx ▸ M.atom_mem x
  have hdeg := deg_le_four M hM hcm
  have : M.deg c = (M.dartsAt c).card := rfl
  omega

theorem obj_joint_mem (O : Object M) {v : V} (hj : v = O.upper ∨ v = O.lower) : v ∈ O.atoms := by
  obtain ⟨A, a, b, sh⟩ := O
  simp only at hj ⊢
  cases sh with
  | vc h => rcases hj with rfl | rfl; exact h.1.2.1; exact h.1.2.2.1
  | hyper R => rcases hj with rfl | rfl; exact R.adjoint.1.2.1; exact R.adjoint.1.2.2.1

/-- **A pair of an object at its joint lies in every triple bond at that joint.** -/
theorem pair_in_triple_of_obj (hM : M.IsMolecule) (O : Object M) {v c : V} (hj : v = O.upper ∨ v = O.lower)
    (hvc : v ≠ c) (h3 : M.bondsBetween v c = 3) {x y : D} (hx : M.atom x = v) (hy : M.atom y = v) (hxy : x ≠ y)
    (gx : M.InGroup O.atoms x) (gy : M.InGroup O.atoms y) :
    M.atom (M.mate x) = c ∧ M.atom (M.mate y) = c := by
  classical
  by_contra hcon
  have hvO : v ∈ O.atoms := obj_joint_mem O hj
  by_cases hc : c ∈ O.atoms
  · have h3' := h3
    rw [Mole.bondsBetween_eq_card_darts M hvc] at h3'
    set X := (M.dartsAt v).filter (fun d => M.atom (M.mate d) = c) with hX
    obtain ⟨z, hzv, gz, hzX⟩ : ∃ z, M.atom z = v ∧ M.InGroup O.atoms z ∧ z ∉ X := by
      by_cases h1 : M.atom (M.mate x) = c
      · refine ⟨y, hy, gy, ?_⟩
        rw [hX, Finset.mem_filter]
        exact fun h => hcon ⟨h1, h.2⟩
      · refine ⟨x, hx, gx, ?_⟩
        rw [hX, Finset.mem_filter]
        exact fun h => h1 h.2
    have hsub : insert z X ⊆ (M.dartsAt v).filter (fun x => M.InGroup O.atoms x) := by
      intro d hd
      rw [Finset.mem_filter, Mole.mem_dartsAt]
      rw [Finset.mem_insert, hX, Finset.mem_filter] at hd
      rcases hd with rfl | hd
      · exact ⟨hzv, gz⟩
      · have hdv := (Mole.mem_dartsAt M v d).mp hd.1
        exact ⟨hdv, by rw [Molecule.InGroup, hdv, hd.2]; exact ⟨hvO, hc⟩⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hzX, h3'] at hcard
    have := joint_inGroup_card_le O hj
    omega
  · apply no_triple_of_two hM hvc hx hy hxy
    · intro h; exact hc (h ▸ gx.2)
    · intro h; exact hc (h ▸ gy.2)
    · exact h3

end generic

variable {w : ℕ} {G : Garden w}

/-- The original darts underlying the bonds of `G_sb` from `v` to `c`, seen at `v`. -/
@[expose] noncomputable def tripleDartsMk (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G))
    (v c : GBranch (stSt G σ Mk).G.tree) :
    Finset (GardenDart G) :=
  (((stSt G σ Mk).G.molecule.dartsAt v).filter
    (fun y => (stSt G σ Mk).G.molecule.atom ((stSt G σ Mk).G.molecule.mate y) = c)).image (stSt G σ Mk).M.od


section core
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Stage1.CLVine G)}
include hM

theorem mem_tripleDartsMk {u : CLBlock G} (hu : u ∈ unitBlocks G σ Mk) {v c : GBranch (stSt G σ Mk).G.tree}
    (hcr : (stSt G σ Mk).M.ob v = u.upper) {d : GardenDart G} :
    d ∈ tripleDartsMk G σ Mk v c ↔ G.molecule.atom d ∈ u.atoms ∧ ¬ G.molecule.InGroup u.atoms d ∧
      repC (stSt G σ Mk).cls (G.molecule.atom (G.molecule.mate d)) = (stSt G σ Mk).M.ob c := by
  unfold tripleDartsMk
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Finset.mem_filter, Mole.mem_dartsAt] at hy
    obtain ⟨hin, hn⟩ := od_extMk (Mk := Mk) hM σ hu hcr hy.1
    refine ⟨hin, hn, ?_⟩
    rw [← hy.2]
    exact (ob_atom_mateMk (Mk := Mk) hM σ y).symm
  · rintro ⟨hin, hn, hr⟩
    obtain ⟨y, hy, hyv⟩ := ext_preimageMk (Mk := Mk) hM σ hu hcr hin hn
    refine ⟨y, ?_, hy⟩
    rw [Finset.mem_filter, Mole.mem_dartsAt]
    refine ⟨hyv, ?_⟩
    apply (stSt G σ Mk).M.ob_inj
    rw [ob_atom_mateMk (Mk := Mk) hM σ, hy]
    exact hr

theorem card_tripleDartsMk {v c : GBranch (stSt G σ Mk).G.tree} (hvc : v ≠ c)
    (h3 : (stSt G σ Mk).G.molecule.bondsBetween v c = 3) : (tripleDartsMk G σ Mk v c).card = 3 := by
  unfold tripleDartsMk
  rw [Finset.card_image_of_injective _ (stSt G σ Mk).M.od_inj]
  rw [← Mole.bondsBetween_eq_card_darts _ hvc]
  exact h3

theorem core_combMk {u : CLBlock G} (hu : u ∈ unitBlocks G σ Mk) {v c : GBranch (stSt G σ Mk).G.tree}
    (hcr : (stSt G σ Mk).M.ob v = u.upper) (hvc : v ≠ c)
    (h3 : (stSt G σ Mk).G.molecule.bondsBetween v c = 3)
    {p : GardenDart G × GardenDart G} {jp : GBranch G.tree} (hjp : jp = u.upper ∨ jp = u.lower)
    (h1 : G.molecule.atom p.1 = jp) (h2 : G.molecule.atom p.2 = jp)
    (n1 : ¬ G.molecule.InGroup u.atoms p.1) (n2 : ¬ G.molecule.InGroup u.atoms p.2) (hne : p.1 ≠ p.2) :
    (p.1 ∈ tripleDartsMk G σ Mk v c ∧ p.2 ∈ tripleDartsMk G σ Mk v c) ∨
    ∃ j', (j' = u.upper ∨ j' = u.lower) ∧ j' ≠ jp ∧ extAt G u j' ⊆ tripleDartsMk G σ Mk v c ∧
      (extAt G u j').card = 2 ∧ (p.1 ∈ tripleDartsMk G σ Mk v c ∨ p.2 ∈ tripleDartsMk G σ Mk v c) ∧
      (p.1 ∉ tripleDartsMk G σ Mk v c ∨ p.2 ∉ tripleDartsMk G σ Mk v c) := by
  classical
  have hul : u.upper ≠ u.lower := u.isBlock.2.2.2.1
  obtain ⟨j', hj', hj'ne, hother⟩ : ∃ j', (j' = u.upper ∨ j' = u.lower) ∧ j' ≠ jp ∧
      ∀ z, (z = u.upper ∨ z = u.lower) → z = jp ∨ z = j' := by
    rcases hjp with rfl | rfl
    · exact ⟨u.lower, Or.inr rfl, fun h => hul h.symm, fun z hz => by
        rcases hz with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl⟩
    · exact ⟨u.upper, Or.inl rfl, hul, fun z hz => by
        rcases hz with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl⟩
  have hEsub : extAt G u jp ⊆ {p.1, p.2} := by
    have hsub : ({p.1, p.2} : Finset (GardenDart G)) ⊆ extAt G u jp := by
      intro d hd
      rw [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact mem_extAt.mpr ⟨h1, n1⟩
      · exact mem_extAt.mpr ⟨h2, n2⟩
    have hc : (extAt G u jp).card ≤ ({p.1, p.2} : Finset (GardenDart G)).card := by
      rw [Finset.card_pair hne]; exact card_extAt_le hM hjp
    rw [Finset.eq_of_subset_of_card_le hsub hc]
  have hsubX : tripleDartsMk G σ Mk v c ⊆ extAt G u jp ∪ extAt G u j' := by
    intro d hd
    obtain ⟨hin, hn, -⟩ := (mem_tripleDartsMk hM σ hu hcr).mp hd
    rcases hother _ (ext_joint hM hin hn) with h | h
    · exact Finset.mem_union_left _ (mem_extAt.mpr ⟨h, hn⟩)
    · exact Finset.mem_union_right _ (mem_extAt.mpr ⟨h, hn⟩)
  rcases comb3 _ _ _ (card_tripleDartsMk hM σ hvc h3) hsubX (card_extAt_le hM hj') p.1 p.2 hEsub with h | ⟨hc, hs, hi, ho⟩
  · exact Or.inl h
  · exact Or.inr ⟨j', hj', hj'ne, hs, hc, hi, ho⟩


/-- **A run hinge of a marked group has no triple bond to the image of an atom outside the group** (both bonds of
the 75-F1 survivor pair at the hinge lead into the survivor). -/
theorem marked_crown_no_triple {S' : Finset (GBranch G.tree)} (hS' : S' ∈ maximalGroups G.molecule)
    (hσ' : σ S' = Molecule.GapKind.SG) (hmk : markedGroup G Mk S') {u' : CLBlock G} (hu' : u' ∈ groupUnitsMk G Mk S')
    {c v : GBranch (stSt G σ Mk).G.tree} (hcr : (stSt G σ Mk).M.ob c = u'.upper) {z : GBranch G.tree}
    (hzv : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z = v) (hzS : z ∉ S') :
    (stSt G σ Mk).G.molecule.bondsBetween v c ≠ 3 := by
  classical
  intro h3
  have hu'B : u' ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S', hS', hσ', hu'⟩
  have hcv : c ≠ v := (hinge_neMk (Mk := Mk) hM σ hu'B hcr (by rw [Mole.bondsBetween_symm]; exact h3))
  obtain ⟨q, -, hT, t, ht, hjc, h1, h2⟩ := hingePair_markedHinge hM σ hS' hσ' hmk hu' hcr
  obtain ⟨St, hSt, -, hmkt, htm, htS⟩ := survivorsMk_group ht
  obtain ⟨hat, hup, hlo, -⟩ := survObj_spec ht
  have hends := RedSplice.isSomeVine_ends ((markedUnitsOfMK hmkt).surv_spec t htm).1
  -- the group of `t` is `S'`
  have hStS : St = S' := by
    have hcu := pi_of_crown hM σ hu'B hcr u'.isBlock.2.1
    rcases hjc with h | h
    · exact group_eq_of_pi_eq hM σ hSt hS' (htS hends.1) (groupUnitsMk_sub hu' u'.isBlock.2.1)
        ((hup.symm.trans h.symm).trans hcu.symm)
    · exact group_eq_of_pi_eq hM σ hSt hS' (htS hends.2.1) (groupUnitsMk_sub hu' u'.isBlock.2.1)
        ((hlo.symm.trans h.symm).trans hcu.symm)
  subst hStS
  have hvO : v ∉ (survObj ht).atoms := by
    intro hv
    rw [hat] at hv
    obtain ⟨z', hz', hz'v⟩ := Finset.mem_image.mp hv
    exact hzS (mem_group_of_repCMk (Mk := Mk) hM σ hSt (htS hz') (repC_eq_of_pi_eq hM σ (hzv.trans hz'v.symm)))
  have g1 := inGroup_of_containsDart _ h1
  have g2 := inGroup_of_containsDart _ h2
  have hxy : q.1 ≠ q.2 := fun h => hT.2.2.2 (by rw [h])
  exact no_triple_of_two (Mole.garden_isMolecule _) hcv
    hT.1 hT.2.1 hxy
    (fun h => hvO (h ▸ g1.2)) (fun h => hvO (h ▸ g2.2))
    (by rw [Mole.bondsBetween_symm]; exact h3)

/-- **R37, whole-group units.**  If the unit `u` of the hinge `v` is the whole group (no skipped vine), and `v` has a triple
bond to `c`, the `HingeBest` pair of the group consists of two bonds of that triple bond. -/
theorem whole_pair_in_tripleMk {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmkS : ¬ markedGroup G Mk S) {u : CLBlock G}
    (hmem : u ∈ (groupUnitsOf G S).units)
    (hsk : (groupUnitsOf G S).skip = none) {v c : GBranch (stSt G σ Mk).G.tree}
    (hcr : (stSt G σ Mk).M.ob v = u.upper) (hvc : v ≠ c) (h3 : (stSt G σ Mk).G.molecule.bondsBetween v c = 3)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hau : a ∈ u.atoms) (hp : HingeBest G S a p) :
    p.1 ∈ tripleDartsMk G σ Mk v c ∧ p.2 ∈ tripleDartsMk G σ Mk v c := by
  classical
  have hu : u ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S, hS, hσ, (groupUnitsMk_of_not_marked hmkS).symm ▸ hmem⟩
  obtain ⟨hspec, hT1, hT2⟩ := hp
  obtain ⟨j, hj, hT, hn1, hn2, -, hrel⟩ := hingeSpec_body hM hS hspec hmem hau
  obtain ⟨hUS, hjj⟩ := hrel hsk
  have hne : p.1 ≠ p.2 := fun h => hT.2.2.2 (by rw [h])
  rcases core_combMk hM σ hu hcr hvc h3 hjj hT.1 hT.2.1 hn1 hn2 hne with
    h | ⟨j', hj', hj'ne, hsubE, hcard, hin, hout⟩
  · exact h
  exfalso
  have hdeg : G.molecule.deg j' = 4 := deg_eq_four_of_ext hM hj' hcard
  have hj'mem : j' ∈ u.atoms := by
    rcases hj' with rfl | rfl
    · exact u.isBlock.2.1
    · exact u.isBlock.2.2.1
  obtain ⟨j2, hB⟩ : ∃ j2, G.molecule.IsBlock u.atoms j' j2 := by
    rcases hj' with rfl | rfl
    · exact ⟨_, u.isBlock⟩
    · exact ⟨_, block_swap_joints _ u.isBlock⟩
  obtain ⟨d1, d2, hd1, hd2, m1, m2, o1, o2⟩ := ext_pair_deg4 hM hB hdeg
  have hd1X := hsubE (mem_extAt.mpr ⟨hd1, m1⟩)
  have hd2X := hsubE (mem_extAt.mpr ⟨hd2, m2⟩)
  obtain ⟨-, -, r1⟩ := (mem_tripleDartsMk hM σ hu hcr).mp hd1X
  obtain ⟨-, -, r2⟩ := (mem_tripleDartsMk hM σ hu hcr).mp hd2X
  have hne' : d2 ≠ G.molecule.mate d1 := by
    intro h
    apply m1
    exact ⟨hd1 ▸ hj'mem, by rw [← h, hd2]; exact hj'mem⟩
  have hsp' : HingeSpec G S a (d1, d2) :=
    ⟨u, hmem, hau, j', hj'mem, ⟨hd1, hd2, hne', by rw [o1, o2]; simp⟩, m1, m2,
      (fun sk h => by rw [hsk] at h; cases h), (fun _ => ⟨hUS, hj'⟩)⟩
  have hjm : G.molecule.atom p.1 ∈ u.atoms := by rw [hT.1]; exact hj
  have hjm2 : G.molecule.atom p.2 ∈ u.atoms := by rw [hT.2.1]; exact hj
  have bad1 : ∀ t z : GardenDart G, t ∈ tripleDartsMk G σ Mk v c → z ∉ tripleDartsMk G σ Mk v c →
      G.molecule.atom z ∈ u.atoms → ¬ G.molecule.InGroup u.atoms z →
      G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z) → False := by
    intro t z ht hz hz1 hz2 hs
    obtain ⟨-, -, rt⟩ := (mem_tripleDartsMk hM σ hu hcr).mp ht
    exact hz ((mem_tripleDartsMk hM σ hu hcr).mpr ⟨hz1, hz2, by rw [← hs]; exact rt⟩)
  have dispatch : ∀ (P : GardenDart G → GardenDart G → Prop), (∀ t z, P t z → P z t) →
      (∀ t z, t ∈ tripleDartsMk G σ Mk v c → z ∉ tripleDartsMk G σ Mk v c → G.molecule.atom z ∈ u.atoms →
        ¬ G.molecule.InGroup u.atoms z → P t z → False) → P p.1 p.2 → False := by
    intro P hsymm hbad hP
    rcases hin with hi | hi <;> rcases hout with ho | ho
    · exact ho hi
    · exact hbad _ _ hi ho hjm2 hn2 hP
    · exact hbad _ _ hi ho hjm hn1 (hsymm _ _ hP)
    · exact ho hi
  rcases repC_classMk (Mk := Mk) hM σ (G.molecule.atom (G.molecule.mate d1)) with ⟨hn, hiff⟩ | ⟨u', hu', hn0, hiff⟩
  · have hs : G.molecule.atom (G.molecule.mate d1) = G.molecule.atom (G.molecule.mate d2) :=
      ((hiff _).mp (r2.trans r1.symm)).symm
    have hP : PairSameAtom G p := hT1 ⟨(d1, d2), hsp', hs⟩
    exact dispatch (fun t z => G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z))
      (fun _ _ h => h.symm) (fun t z ht hz hz1 hz2 hs' => bad1 t z ht hz hz1 hz2 hs') hP
  · obtain ⟨S', hS'm, hσ', hu'S'⟩ := mem_unitBlocksMk.mp hu'
    have hnm' : ¬ markedGroup G Mk S' := by
      intro hmk'
      have hcr' : (stSt G σ Mk).M.ob c = u'.upper := r1.symm.trans (stSt_repC_memMk (Mk := Mk) hM σ hu' hn0)
      have huS : u.upper ∈ S := (groupUnitsOf G S).sub u hmem u.isBlock.2.1
      have hSS : S ≠ S' := fun h => hmkS (h ▸ hmk')
      exact marked_crown_no_triple hM σ hS'm hσ' hmk' hu'S' hcr' (pi_of_crown hM σ hu hcr u.isBlock.2.1)
        (fun h => Finset.disjoint_left.mp (groups_disjoint hM hS hS'm hSS) huS h) h3
    rw [groupUnitsMk_of_not_marked hnm'] at hu'S'
    have hP' : PairSameUnit G (d1, d2) :=
      ⟨S', hS'm, u', hu'S', hn0, (hiff _).mp (r2.trans r1.symm)⟩
    have hbad2 : ∀ t z : GardenDart G, t ∈ tripleDartsMk G σ Mk v c → z ∉ tripleDartsMk G σ Mk v c →
        G.molecule.atom z ∈ u.atoms → ¬ G.molecule.InGroup u.atoms z →
        (∃ S'' ∈ maximalGroups G.molecule, ∃ u'' ∈ (groupUnitsOf G S'').units,
          G.molecule.atom (G.molecule.mate t) ∈ u''.atoms ∧ G.molecule.atom (G.molecule.mate z) ∈ u''.atoms) →
        False := by
      intro t z ht hz hz1 hz2 ⟨S'', hS''m, u'', hu''S'', hm1, hm2⟩
      obtain ⟨-, -, rt⟩ := (mem_tripleDartsMk hM σ hu hcr).mp ht
      have hmt : G.molecule.atom (G.molecule.mate t) ∈ u'.atoms := (hiff _).mp (rt.trans r1.symm)
      have huu : u'' = u' := unit_eq_any hM hS''m hS'm hu''S'' hu'S' hm1 hmt
      subst huu
      exact hz ((mem_tripleDartsMk hM σ hu hcr).mpr ⟨hz1, hz2, (hiff _).mpr hm2 |>.trans r1⟩)
    rcases hT2 ⟨(d1, d2), hsp', hP'⟩ with hP | hP
    · exact dispatch (fun t z => G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z))
        (fun _ _ h => h.symm) (fun t z ht hz hz1 hz2 hs' => bad1 t z ht hz hz1 hz2 hs') hP
    · exact dispatch (fun t z => ∃ S'' ∈ maximalGroups G.molecule, ∃ u'' ∈ (groupUnitsOf G S'').units,
          G.molecule.atom (G.molecule.mate t) ∈ u''.atoms ∧ G.molecule.atom (G.molecule.mate z) ∈ u''.atoms)
        (fun t z ⟨S'', h1, u'', h2, h3, h4⟩ => ⟨S'', h1, u'', h2, h4, h3⟩)
        (fun t z ht hz hz1 hz2 hP => hbad2 t z ht hz hz1 hz2 hP) hP

end core

theorem od_mem_tripleDartsMk (σ : Prescription G) {Mk : Set (Stage1.CLVine G)} {v c : GBranch (stSt G σ Mk).G.tree}
    {x : GardenDart (stSt G σ Mk).G} (h : (stSt G σ Mk).M.od x ∈ tripleDartsMk G σ Mk v c) :
    (stSt G σ Mk).G.molecule.atom x = v ∧ (stSt G σ Mk).G.molecule.atom ((stSt G σ Mk).G.molecule.mate x) = c := by
  unfold tripleDartsMk at h
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h
  have := (stSt G σ Mk).M.od_inj hyx
  subst this
  rw [Finset.mem_filter, Mole.mem_dartsAt] at hy
  exact hy


/-- **R37 with survivors**: if a hinge `v` of `G_sb` has a triple bond to `c`, the hinge pair of `v` consists of two
bonds of that triple bond. -/
theorem triple_in_hingePairMk {R : ℕ} {G : Garden (2 * R)} (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {Mk : Set (Stage1.CLVine G)} {v c : GBranch (stSt G σ Mk).G.tree} (hv : v ∈ (stSt G σ Mk).hinges)
    (h3 : (stSt G σ Mk).G.molecule.bondsBetween v c = 3) :
    ∃ x y, hingePair G σ v = some (x, y) ∧ TripleAt (stSt G σ Mk).G v x y ∧
      (stSt G σ Mk).G.molecule.atom ((stSt G σ Mk).G.molecule.mate x) = c ∧
      (stSt G σ Mk).G.molecule.atom ((stSt G σ Mk).G.molecule.mate y) = c := by
  classical
  have hM' := Mole.garden_isMolecule (stSt G σ Mk).G
  obtain ⟨S0, hS0, hσ0, u0, hu0, hcr0⟩ := hinge_groupMk hM σ hv
  have hu0B : u0 ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S0, hS0, hσ0, hu0⟩
  have hvc : v ≠ c := hinge_neMk (Mk := Mk) hM σ hu0B hcr0 h3
  by_cases hmk : markedGroup G Mk S0
  · obtain ⟨q, hq, hT, t, ht, hjv, h1, h2⟩ := hingePair_markedHinge hM σ hS0 hσ0 hmk hu0 hcr0
    have hxy : q.1 ≠ q.2 := fun h => hT.2.2.2 (by rw [h])
    obtain ⟨e1, e2⟩ := pair_in_triple_of_obj hM' (survObj ht) hjv hvc h3 hT.1 hT.2.1 hxy
      (inGroup_of_containsDart _ h1) (inGroup_of_containsDart _ h2)
    exact ⟨q.1, q.2, hq, hT, e1, e2⟩
  have hu0' : u0 ∈ (groupUnitsOf G S0).units := groupUnitsMk_of_not_marked hmk ▸ hu0
  obtain ⟨x, y, hp, hPP, -, hentry⟩ := hingePair_specMk hM σ hS0 hσ0 hmk hu0' hcr0
  have hT := hPP.1
  have hxy : x ≠ y := fun h => hT.2.2.2 (by rw [h])
  refine ⟨x, y, hp, hT, ?_⟩
  by_cases hobj : ∃ O ∈ objects G σ Mk, O.upper = v ∨ O.lower = v
  · obtain ⟨O, hOm, hj⟩ := hobj
    obtain ⟨hc1, hc2, -⟩ := hingePair_containedMk hM σ hv hp hOm hj
    have hj' : v = O.upper ∨ v = O.lower := by rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm
    exact pair_in_triple_of_obj hM' O hj' hvc h3 hT.1 hT.2.1 hxy (inGroup_of_containsDart _ hc1)
      (inGroup_of_containsDart _ hc2)
  rcases hsk : (groupUnitsOf G S0).skip with _ | sk
  swap
  · -- a skipped vine: its object has the joint `v`
    exfalso
    apply hobj
    obtain ⟨O, hex, hOm⟩ := objOf_isSomeMk hM σ hS0 hσ0 (Or.inr ⟨sk, hsk⟩) hmk
    obtain ⟨-, -, -, hOspec⟩ := objOf_specMk (Option.mem_def.mpr hex)
    obtain ⟨A, -, -, -, hsrc⟩ := hOspec.src
    rcases hsrc with ⟨⟨hhv, hnh⟩, -⟩ | ⟨sk', hsk', -, hup, hlo, -, -⟩
    · have := (groupUnitsOf G S0).hv_empty hhv hnh
      rw [this] at hu0'
      cases hu0'
    · rw [hsk] at hsk'
      cases hsk'
      have hsu := (groupUnitsOf G S0).skip_units sk hsk
      refine ⟨O, hOm, ?_⟩
      rcases hsu.1 u0 hu0' with ⟨hL, hl⟩ | ⟨hR, hr⟩
      · have hxu : sk.x ∈ u0.atoms := by
          rcases hl with ⟨_, h2⟩ | ⟨h2, _⟩
          · rw [← h2]; exact u0.isBlock.2.2.1
          · rw [← h2]; exact u0.isBlock.2.1
        exact Or.inl (hup.trans (pi_of_crown hM σ hu0B hcr0 hxu))
      · have hxu : sk.y ∈ u0.atoms := by
          rcases hr with ⟨h2, _⟩ | ⟨_, h2⟩
          · rw [← h2]; exact u0.isBlock.2.1
          · rw [← h2]; exact u0.isBlock.2.2.1
        exact Or.inr (hlo.trans (pi_of_crown hM σ hu0B hcr0 hxu))
  -- a whole-group unit: main's R37 argument
  obtain ⟨S, hSm, hga, hep⟩ := hentry hobj
  obtain ⟨a, ha, hav⟩ : ∃ a, groupJoint G S Mk = some a ∧ (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = v := by
    unfold groupAtom at hga
    cases hg : groupJoint G S Mk with
    | none => rw [hg] at hga; cases hga
    | some a => rw [hg] at hga; exact ⟨a, rfl, Option.some.inj hga⟩
  have hnmS := not_marked_of_groupJoint ha
  have ha' : groupJoint G S = some a := (groupJoint_of_not_marked hnmS).symm.trans ha
  have haS := (groupJoint_kind ha').1
  have hSS : S = S0 := group_eq_of_pi_eq hM σ hSm hS0 haS (groupUnitsMk_sub hu0 u0.isBlock.2.1)
    (hav.trans (pi_of_crown hM σ hu0B hcr0 u0.isBlock.2.1).symm)
  subst hSS
  have hUS := (groupUnitsOf G S).noskip_units hsk u0 hu0'
  have hau : a ∈ u0.atoms := hUS ▸ haS
  obtain ⟨p, hp1, hbest⟩ := hingeOrigPair_bestMk (Mk := Mk) ha ⟨u0, hu0', hau⟩
  unfold hingeEntryPair at hep
  rw [hp1, Option.bind_some] at hep
  obtain ⟨hq1, hq2, -⟩ := liftPair_specMk hep
  have hX := whole_pair_in_tripleMk hM σ hSm hσ0 hmk hu0' hsk hcr0 hvc h3 hau hbest
  refine ⟨(od_mem_tripleDartsMk σ (v := v) ?_).2, (od_mem_tripleDartsMk σ (v := v) ?_).2⟩
  · show (stSt G σ Mk).M.od (x, y).1 ∈ _
    rw [hq1]; exact hX.1
  · show (stSt G σ Mk).M.od (x, y).2 ∈ _
    rw [hq2]; exact hX.2

/-- **`TripleDesignated` for the marked splice** (R37/R48, o75 Theorem 7.5′(2),(5); world `SoundMKFull`). -/
theorem tripleDesignated_collectionChoicesMk {R : ℕ} {G : Garden (2 * R)} (hM : G.molecule.IsMolecule)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) (σ : Prescription G) {Mk : Set (Stage1.CLVine G)} :
    (collectionChoices G σ Mk).TripleDesignated := by
  intro a b h
  rcases (stSt G σ Mk).triple_hinge hno a b h with ha | hb
  · obtain ⟨x, y, hxy, hT, h1, h2⟩ := triple_in_hingePairMk hM σ ha h
    exact ⟨a, ha, b, x, y, Or.inl ⟨rfl, rfl⟩, by simp [collectionChoices, hxy], by simp [collectionChoices, hxy],
      hT, h1, h2⟩
  · have h' : (stSt G σ Mk).G.molecule.bondsBetween b a = 3 := by
      rw [Mole.bondsBetween_symm]; exact h
    obtain ⟨x, y, hxy, hT, h1, h2⟩ := triple_in_hingePairMk hM σ hb h'
    exact ⟨b, hb, a, x, y, Or.inr ⟨rfl, rfl⟩, by simp [collectionChoices, hxy], by simp [collectionChoices, hxy],
      hT, h1, h2⟩

end WaveTurbulence.VineA.NormalizedSplice
