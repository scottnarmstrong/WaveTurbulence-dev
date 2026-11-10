/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
-- R83 port of rs-src/RedSpliceTripleDesig.lean (FLOWER-P6 R83): successor designations, see HANDOFF

public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceGap
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R37: the chosen hinge pair lies in a triple bond at the hinge

TARGET Operation 1 (L2140) and DH23 L1775: a triple bond of `M_sb` has a hinge endpoint `v`; the unit of `v` has four external
bonds, two at each joint, so three of them leave the unit at one joint twice.  `hingeOrigPair` (`HingeBest`) is chosen so
that its pair is that external pair of the joint, independently of `σ` (tiers `PairSameAtom`, `PairSameUnit`).

* `tripleDarts G σ v c`: the original darts underlying the bonds of `G_sb` from `v` to `c`.
* `whole_pair_in_triple`, `skip_pair_in_triple`: the pair lies in them (whole-group unit / unit of a skipped vine).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

theorem card_aux {α : Type*} [DecidableEq α] (X E' : Finset α) (c : α) (hX : X.card = 3)
    (hsub : X ⊆ insert c E') (hE' : E'.card ≤ 2) : E'.card = 2 ∧ E' ⊆ X := by
  have h1 : (insert c E').card ≤ E'.card + 1 := Finset.card_insert_le _ _
  have h2 : X.card ≤ (insert c E').card := Finset.card_le_card hsub
  have hc : E'.card = 2 := by omega
  have heq : X = insert c E' := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact ⟨hc, by rw [heq]; exact Finset.subset_insert _ _⟩

theorem comb3 {α : Type*} [DecidableEq α] (X E E' : Finset α) (hX : X.card = 3) (hsub : X ⊆ E ∪ E')
    (hE' : E'.card ≤ 2) (a b : α) (hE : E ⊆ {a, b}) :
    (a ∈ X ∧ b ∈ X) ∨ (E'.card = 2 ∧ E' ⊆ X ∧ (a ∈ X ∨ b ∈ X) ∧ (a ∉ X ∨ b ∉ X)) := by
  by_cases ha : a ∈ X
  · by_cases hb : b ∈ X
    · exact Or.inl ⟨ha, hb⟩
    · right
      have hs : X ⊆ insert a E' := by
        intro x hx
        rcases Finset.mem_union.mp (hsub hx) with h | h
        · have h' := Finset.mem_insert.mp (hE h)
          rcases h' with h' | h'
          · rw [h']; exact Finset.mem_insert_self _ _
          · rw [Finset.mem_singleton] at h'; rw [h'] at hx; exact absurd hx hb
        · exact Finset.mem_insert_of_mem h
      obtain ⟨hc, hs'⟩ := card_aux X E' a hX hs hE'
      exact ⟨hc, hs', Or.inl ha, Or.inr hb⟩
  · right
    by_cases hb : b ∈ X
    · have hs : X ⊆ insert b E' := by
        intro x hx
        rcases Finset.mem_union.mp (hsub hx) with h | h
        · have h' := Finset.mem_insert.mp (hE h)
          rcases h' with h' | h'
          · rw [h'] at hx; exact absurd hx ha
          · rw [Finset.mem_singleton] at h'; rw [h']; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem h
      obtain ⟨hc, hs'⟩ := card_aux X E' b hX hs hE'
      exact ⟨hc, hs', Or.inr hb, Or.inl ha⟩
    · exfalso
      have hs : X ⊆ E' := by
        intro x hx
        rcases Finset.mem_union.mp (hsub hx) with h | h
        · have h' := Finset.mem_insert.mp (hE h)
          rcases h' with h' | h'
          · rw [h'] at hx; exact absurd hx ha
          · rw [Finset.mem_singleton] at h'; rw [h'] at hx; exact absurd hx hb
        · exact h
      have := Finset.card_le_card hs
      omega

/-- The original darts underlying the bonds of `G_sb` from `v` to `c`, seen at `v`. -/
@[expose] noncomputable def tripleDarts (G : Garden w) (σ : Prescription G) (v c : GBranch (stSt G σ).G.tree) :
    Finset (GardenDart G) :=
  (((stSt G σ).G.molecule.dartsAt v).filter
    (fun y => (stSt G σ).G.molecule.atom ((stSt G σ).G.molecule.mate y) = c)).image (stSt G σ).M.od

/-- The external darts of the block `u` at the joint `j`. -/
@[expose] noncomputable def extAt (G : Garden w) (u : CLBlock G) (j : GBranch G.tree) : Finset (GardenDart G) :=
  (G.molecule.dartsAt j).filter (fun d => ¬ G.molecule.InGroup u.atoms d)

theorem mem_extAt {u : CLBlock G} {j : GBranch G.tree} {d : GardenDart G} :
    d ∈ extAt G u j ↔ G.molecule.atom d = j ∧ ¬ G.molecule.InGroup u.atoms d := by
  unfold extAt
  rw [Finset.mem_filter, Mole.mem_dartsAt]

theorem unit_eq_any (hM : G.molecule.IsMolecule) {S S' : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hS' : S' ∈ maximalGroups G.molecule)
    {u u' : CLBlock G} (hu : u ∈ (groupUnitsOf G S).units) (hu' : u' ∈ (groupUnitsOf G S').units)
    {z : GBranch G.tree} (hz : z ∈ u.atoms) (hz' : z ∈ u'.atoms) : u = u' := by
  by_cases hSS : S = S'
  · subst hSS
    by_contra hne
    have : Std.Symm (fun u u' : CLBlock G => Disjoint u.atoms u'.atoms) := ⟨fun _ _ h => h.symm⟩
    have := (groupUnitsOf G S).disj.forall hu hu' hne
    exact Finset.disjoint_left.mp this hz hz'
  · exact absurd ((groupUnitsOf G S').sub u' hu' hz')
      (Finset.disjoint_left.mp (groups_disjoint hM hS hS' hSS) ((groupUnitsOf G S).sub u hu hz))

section core
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

/-- B1b (Mk-general form of `repC_class`). -/
theorem repC_classMk (n0 : GBranch G.tree) {Mk : Set (Stage1.CLVine _)} :
    ((stSt (Mk := Mk) G σ).cls n0 = none ∧ ∀ m, repC (stSt (Mk := Mk) G σ).cls m = repC (stSt (Mk := Mk) G σ).cls n0 ↔ m = n0) ∨
    (∃ u' ∈ unitBlocks (Mk := Mk) G σ, n0 ∈ u'.atoms ∧
      ∀ m, repC (stSt (Mk := Mk) G σ).cls m = repC (stSt (Mk := Mk) G σ).cls n0 ↔ m ∈ u'.atoms) := by
  by_cases h : ∃ u' ∈ unitBlocks (Mk := Mk) G σ, n0 ∈ u'.atoms
  · obtain ⟨u', hu', hn0⟩ := h
    right
    refine ⟨u', hu', hn0, fun m => ?_⟩
    rw [stSt_repC_memMk (Mk := Mk) hM σ hu' hn0]
    constructor
    · intro hm
      by_cases hm' : ∃ u2 ∈ unitBlocks (Mk := Mk) G σ, m ∈ u2.atoms
      · obtain ⟨u2, hu2, hmu2⟩ := hm'
        rw [stSt_repC_memMk (Mk := Mk) hM σ hu2 hmu2] at hm
        have h3 : u2.upper ∈ u'.atoms := hm ▸ u'.isBlock.2.1
        have := unit_eq_of_memMk (Mk := Mk) hM σ hu2 hu' u2.isBlock.2.1 h3
        exact this ▸ hmu2
      · push Not at hm'
        rw [stSt_repC_noneMk (Mk := Mk) hM σ hm'] at hm
        exact hm ▸ u'.isBlock.2.1
    · intro hm
      exact stSt_repC_memMk (Mk := Mk) hM σ hu' hm
  · push Not at h
    left
    refine ⟨stSt_cls_noneMk (Mk := Mk) hM σ h, fun m => ?_⟩
    rw [stSt_repC_noneMk (Mk := Mk) hM σ h]
    constructor
    · intro hm
      by_cases hm' : ∃ u2 ∈ unitBlocks (Mk := Mk) G σ, m ∈ u2.atoms
      · obtain ⟨u2, hu2, hmu2⟩ := hm'
        rw [stSt_repC_memMk (Mk := Mk) hM σ hu2 hmu2] at hm
        exact absurd (hm ▸ u2.isBlock.2.1) (h u2 hu2)
      · push Not at hm'
        rw [stSt_repC_noneMk (Mk := Mk) hM σ hm'] at hm
        exact hm
    · intro hm
      rw [hm]; exact stSt_repC_noneMk (Mk := Mk) hM σ h

theorem repC_class (n0 : GBranch G.tree) :
    ((stSt G σ).cls n0 = none ∧ ∀ m, repC (stSt G σ).cls m = repC (stSt G σ).cls n0 ↔ m = n0) ∨
    (∃ u' ∈ unitBlocks G σ, n0 ∈ u'.atoms ∧
      ∀ m, repC (stSt G σ).cls m = repC (stSt G σ).cls n0 ↔ m ∈ u'.atoms) := repC_classMk (Mk := ∅) hM σ n0

/-- B1b (Mk-general form of `mem_unit_of_repC`). -/
theorem mem_unit_of_repCMk {u : CLBlock G} {Mk : Set (Stage1.CLVine _)} (hu : u ∈ unitBlocks (Mk := Mk) G σ) {m : GBranch G.tree}
    (h : repC (stSt (Mk := Mk) G σ).cls m = u.upper) : m ∈ u.atoms := by
  have hrep : repC (stSt (Mk := Mk) G σ).cls u.upper = u.upper := stSt_repC_memMk (Mk := Mk) hM σ hu u.isBlock.2.1
  rcases repC_classMk (Mk := Mk) hM σ u.upper with ⟨hn, _⟩ | ⟨u', hu', hn0, hiff⟩
  · rw [stSt_cls_memMk (Mk := Mk) hM σ hu u.isBlock.2.1] at hn; cases hn
  · have := unit_eq_of_memMk (Mk := Mk) hM σ hu' hu hn0 u.isBlock.2.1
    subst this
    exact (hiff m).mp (h.trans hrep.symm)

/-- B1b (Mk-general form of `ob_atom_mate`). -/
theorem ob_atom_mateMk {Mk : Set (Stage1.CLVine _)} (y : GardenDart (stSt (Mk := Mk) G σ).G) :
    (stSt (Mk := Mk) G σ).M.ob ((stSt (Mk := Mk) G σ).G.molecule.atom ((stSt (Mk := Mk) G σ).G.molecule.mate y)) =
      repC (stSt (Mk := Mk) G σ).cls (G.molecule.atom (G.molecule.mate ((stSt (Mk := Mk) G σ).M.od y))) := by
  rw [(stSt (Mk := Mk) G σ).M.ob_atom, (stSt (Mk := Mk) G σ).M.od_mate]

theorem ob_atom_mate (y : GardenDart (stSt G σ).G) :
    (stSt G σ).M.ob ((stSt G σ).G.molecule.atom ((stSt G σ).G.molecule.mate y)) =
      repC (stSt G σ).cls (G.molecule.atom (G.molecule.mate ((stSt G σ).M.od y))) := ob_atom_mateMk (Mk := ∅) hM σ y

/-- B1b (Mk-general form of `od_ext`). -/
theorem od_extMk {u : CLBlock G} {Mk : Set (Stage1.CLVine _)} (hu : u ∈ unitBlocks (Mk := Mk) G σ) {v : GBranch (stSt (Mk := Mk) G σ).G.tree}
    (hcr : (stSt (Mk := Mk) G σ).M.ob v = u.upper) {y : GardenDart (stSt (Mk := Mk) G σ).G}
    (hy : (stSt (Mk := Mk) G σ).G.molecule.atom y = v) :
    G.molecule.atom ((stSt (Mk := Mk) G σ).M.od y) ∈ u.atoms ∧ ¬ G.molecule.InGroup u.atoms ((stSt (Mk := Mk) G σ).M.od y) := by
  have h1 : repC (stSt (Mk := Mk) G σ).cls (G.molecule.atom ((stSt (Mk := Mk) G σ).M.od y)) = u.upper := by
    have := (stSt (Mk := Mk) G σ).M.ob_atom y
    rw [hy, hcr] at this
    exact this.symm
  have hin := mem_unit_of_repCMk (Mk := Mk) hM σ hu h1
  refine ⟨hin, fun hg => ?_⟩
  have hr := ((stSt (Mk := Mk) G σ).M.od_range ((stSt (Mk := Mk) G σ).M.od y)).mp ⟨y, rfl⟩
  exact hr ⟨u.upper, stSt_cls_memMk (Mk := Mk) hM σ hu hg.1, stSt_cls_memMk (Mk := Mk) hM σ hu hg.2⟩

theorem od_ext {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {v : GBranch (stSt G σ).G.tree}
    (hcr : (stSt G σ).M.ob v = u.upper) {y : GardenDart (stSt G σ).G}
    (hy : (stSt G σ).G.molecule.atom y = v) :
    G.molecule.atom ((stSt G σ).M.od y) ∈ u.atoms ∧ ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od y) := od_extMk (Mk := ∅) hM σ hu hcr hy

theorem ext_joint {u : CLBlock G} {d : GardenDart G} (hd : G.molecule.atom d ∈ u.atoms)
    (hn : ¬ G.molecule.InGroup u.atoms d) : G.molecule.atom d = u.upper ∨ G.molecule.atom d = u.lower := by
  by_contra hcon
  push Not at hcon
  exact hn (allInt hM u.isBlock hd hcon.1 hcon.2 rfl)

/-- B1b (Mk-general form of `ext_preimage`). -/
theorem ext_preimageMk {u : CLBlock G} {Mk : Set (Stage1.CLVine _)} (hu : u ∈ unitBlocks (Mk := Mk) G σ) {v : GBranch (stSt (Mk := Mk) G σ).G.tree}
    (hcr : (stSt (Mk := Mk) G σ).M.ob v = u.upper) {d : GardenDart G} (hd : G.molecule.atom d ∈ u.atoms)
    (hn : ¬ G.molecule.InGroup u.atoms d) :
    ∃ y, (stSt (Mk := Mk) G σ).M.od y = d ∧ (stSt (Mk := Mk) G σ).G.molecule.atom y = v := by
  have hnint : ¬ ∃ a, (stSt (Mk := Mk) G σ).cls (G.molecule.atom d) = some a ∧
      (stSt (Mk := Mk) G σ).cls (G.molecule.atom (G.molecule.mate d)) = some a := by
    rintro ⟨a, ha, ha'⟩
    rw [stSt_cls_memMk (Mk := Mk) hM σ hu hd] at ha
    have : a = u.upper := (Option.some.inj ha).symm
    subst this
    exact hn ⟨hd, mem_of_cls_eqMk (Mk := Mk) hM σ hu ha'⟩
  obtain ⟨y, hy⟩ := ((stSt (Mk := Mk) G σ).M.od_range d).mpr hnint
  refine ⟨y, hy, ?_⟩
  apply (stSt (Mk := Mk) G σ).M.ob_inj
  rw [(stSt (Mk := Mk) G σ).M.ob_atom, hy, hcr]
  exact stSt_repC_memMk (Mk := Mk) hM σ hu hd

theorem ext_preimage {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {v : GBranch (stSt G σ).G.tree}
    (hcr : (stSt G σ).M.ob v = u.upper) {d : GardenDart G} (hd : G.molecule.atom d ∈ u.atoms)
    (hn : ¬ G.molecule.InGroup u.atoms d) :
    ∃ y, (stSt G σ).M.od y = d ∧ (stSt G σ).G.molecule.atom y = v := ext_preimageMk (Mk := ∅) hM σ hu hcr hd hn

theorem mem_tripleDarts {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {v c : GBranch (stSt G σ).G.tree}
    (hcr : (stSt G σ).M.ob v = u.upper) {d : GardenDart G} :
    d ∈ tripleDarts G σ v c ↔ G.molecule.atom d ∈ u.atoms ∧ ¬ G.molecule.InGroup u.atoms d ∧
      repC (stSt G σ).cls (G.molecule.atom (G.molecule.mate d)) = (stSt G σ).M.ob c := by
  unfold tripleDarts
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Finset.mem_filter, Mole.mem_dartsAt] at hy
    obtain ⟨hin, hn⟩ := od_ext hM σ hu hcr hy.1
    refine ⟨hin, hn, ?_⟩
    rw [← hy.2]
    exact (ob_atom_mate hM σ y).symm
  · rintro ⟨hin, hn, hr⟩
    obtain ⟨y, hy, hyv⟩ := ext_preimage hM σ hu hcr hin hn
    refine ⟨y, ?_, hy⟩
    rw [Finset.mem_filter, Mole.mem_dartsAt]
    refine ⟨hyv, ?_⟩
    apply (stSt G σ).M.ob_inj
    rw [ob_atom_mate hM σ, hy]
    exact hr

theorem card_tripleDarts {v c : GBranch (stSt G σ).G.tree} (hvc : v ≠ c)
    (h3 : (stSt G σ).G.molecule.bondsBetween v c = 3) : (tripleDarts G σ v c).card = 3 := by
  unfold tripleDarts
  rw [Finset.card_image_of_injective _ (stSt G σ).M.od_inj]
  rw [← Mole.bondsBetween_eq_card_darts _ hvc]
  exact h3

theorem card_extAt_le {u : CLBlock G} {j : GBranch G.tree} (hj : j = u.upper ∨ j = u.lower) :
    (extAt G u j).card ≤ 2 := by
  have hjm : j ∈ G.molecule.atoms := by
    rcases hj with rfl | rfl
    · exact u.isBlock.1 u.isBlock.2.1
    · exact u.isBlock.1 u.isBlock.2.2.1
  have hdeg := deg_le_four G.molecule hM hjm
  have hdi : G.molecule.degIn u.atoms j = 2 := by
    rcases hj with rfl | rfl
    · exact (block_joint_degrees G.molecule u.isBlock).1
    · exact (block_joint_degrees G.molecule u.isBlock).2
  have h : ((G.molecule.dartsAt j).filter (fun x => G.molecule.InGroup u.atoms x)).card +
      ((G.molecule.dartsAt j).filter (fun x => ¬ G.molecule.InGroup u.atoms x)).card =
      (G.molecule.dartsAt j).card := Finset.card_filter_add_card_filter_not _
  have h' : G.molecule.deg j = (G.molecule.dartsAt j).card := rfl
  have hdi' : ((G.molecule.dartsAt j).filter (fun x => G.molecule.InGroup u.atoms x)).card = 2 := hdi
  show ((G.molecule.dartsAt j).filter (fun x => ¬ G.molecule.InGroup u.atoms x)).card ≤ 2
  omega

theorem deg_eq_four_of_ext {u : CLBlock G} {j : GBranch G.tree} (hj : j = u.upper ∨ j = u.lower)
    (hc : (extAt G u j).card = 2) : G.molecule.deg j = 4 := by
  have hdi : G.molecule.degIn u.atoms j = 2 := by
    rcases hj with rfl | rfl
    · exact (block_joint_degrees G.molecule u.isBlock).1
    · exact (block_joint_degrees G.molecule u.isBlock).2
  have h : ((G.molecule.dartsAt j).filter (fun x => G.molecule.InGroup u.atoms x)).card +
      ((G.molecule.dartsAt j).filter (fun x => ¬ G.molecule.InGroup u.atoms x)).card =
      (G.molecule.dartsAt j).card := Finset.card_filter_add_card_filter_not _
  have hdi' : ((G.molecule.dartsAt j).filter (fun x => G.molecule.InGroup u.atoms x)).card = 2 := hdi
  have hc' : ((G.molecule.dartsAt j).filter (fun x => ¬ G.molecule.InGroup u.atoms x)).card = 2 := hc
  show (G.molecule.dartsAt j).card = 4
  omega

theorem core_comb {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {v c : GBranch (stSt G σ).G.tree}
    (hcr : (stSt G σ).M.ob v = u.upper) (hvc : v ≠ c)
    (h3 : (stSt G σ).G.molecule.bondsBetween v c = 3)
    {p : GardenDart G × GardenDart G} {jp : GBranch G.tree} (hjp : jp = u.upper ∨ jp = u.lower)
    (h1 : G.molecule.atom p.1 = jp) (h2 : G.molecule.atom p.2 = jp)
    (n1 : ¬ G.molecule.InGroup u.atoms p.1) (n2 : ¬ G.molecule.InGroup u.atoms p.2) (hne : p.1 ≠ p.2) :
    (p.1 ∈ tripleDarts G σ v c ∧ p.2 ∈ tripleDarts G σ v c) ∨
    ∃ j', (j' = u.upper ∨ j' = u.lower) ∧ j' ≠ jp ∧ extAt G u j' ⊆ tripleDarts G σ v c ∧
      (extAt G u j').card = 2 ∧ (p.1 ∈ tripleDarts G σ v c ∨ p.2 ∈ tripleDarts G σ v c) ∧
      (p.1 ∉ tripleDarts G σ v c ∨ p.2 ∉ tripleDarts G σ v c) := by
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
  have hsubX : tripleDarts G σ v c ⊆ extAt G u jp ∪ extAt G u j' := by
    intro d hd
    obtain ⟨hin, hn, -⟩ := (mem_tripleDarts hM σ hu hcr).mp hd
    rcases hother _ (ext_joint hM hin hn) with h | h
    · exact Finset.mem_union_left _ (mem_extAt.mpr ⟨h, hn⟩)
    · exact Finset.mem_union_right _ (mem_extAt.mpr ⟨h, hn⟩)
  rcases comb3 _ _ _ (card_tripleDarts hM σ hvc h3) hsubX (card_extAt_le hM hj') p.1 p.2 hEsub with h | ⟨hc, hs, hi, ho⟩
  · exact Or.inl h
  · exact Or.inr ⟨j', hj', hj'ne, hs, hc, hi, ho⟩

end core

theorem hingeSpec_body (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hsp : HingeSpec G S a p) {u : CLBlock G}
    (hmem : u ∈ (groupUnitsOf G S).units) (hau : a ∈ u.atoms) :
    ∃ j ∈ u.atoms, TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧ ¬ G.molecule.InGroup u.atoms p.2 ∧
      (∀ sk, (groupUnitsOf G S).skip = some sk → (j = sk.x ∨ j = sk.y) ∧
        G.molecule.atom (G.molecule.mate p.1) ∈ sk.A ∧ G.molecule.atom (G.molecule.mate p.2) ∈ sk.A ∧
        ∀ e, sk.bond = some e → p.1 ≠ e ∧ p.1 ≠ G.molecule.mate e ∧ p.2 ≠ e ∧ p.2 ≠ G.molecule.mate e) ∧
      ((groupUnitsOf G S).skip = none → u.atoms = S ∧ (j = u.upper ∨ j = u.lower)) := by
  obtain ⟨u0, hu0, hau0, j, hj, rest⟩ := hsp
  have := unit_eq_any hM hS hS hu0 hmem hau0 hau
  subst this
  exact ⟨j, hj, rest⟩

section whole
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

/-- **R37, whole-group units.**  If the unit `u` of the hinge `v` is the whole group (no skipped vine), and `v` has a triple
bond to `c`, the `HingeBest` pair of the group consists of two bonds of that triple bond. -/
theorem whole_pair_in_triple {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) {u : CLBlock G} (hmem : u ∈ (groupUnitsOf G S).units)
    (hsk : (groupUnitsOf G S).skip = none) {v c : GBranch (stSt G σ).G.tree}
    (hcr : (stSt G σ).M.ob v = u.upper) (hvc : v ≠ c) (h3 : (stSt G σ).G.molecule.bondsBetween v c = 3)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hau : a ∈ u.atoms) (hp : HingeBest G S a p) :
    p.1 ∈ tripleDarts G σ v c ∧ p.2 ∈ tripleDarts G σ v c := by
  classical
  have hu : u ∈ unitBlocks G σ := mem_unitBlocks.mpr ⟨S, hS, hσ, hmem⟩
  obtain ⟨hspec, hT1, hT2⟩ := hp
  obtain ⟨j, hj, hT, hn1, hn2, -, hrel⟩ := hingeSpec_body hM hS hspec hmem hau
  obtain ⟨hUS, hjj⟩ := hrel hsk
  have hne : p.1 ≠ p.2 := fun h => hT.2.2.2 (by rw [h])
  rcases core_comb hM σ hu hcr hvc h3 hjj hT.1 hT.2.1 hn1 hn2 hne with
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
  obtain ⟨-, -, r1⟩ := (mem_tripleDarts hM σ hu hcr).mp hd1X
  obtain ⟨-, -, r2⟩ := (mem_tripleDarts hM σ hu hcr).mp hd2X
  have hne' : d2 ≠ G.molecule.mate d1 := by
    intro h
    apply m1
    exact ⟨hd1 ▸ hj'mem, by rw [← h, hd2]; exact hj'mem⟩
  have hsp' : HingeSpec G S a (d1, d2) :=
    ⟨u, hmem, hau, j', hj'mem, ⟨hd1, hd2, hne', by rw [o1, o2]; simp⟩, m1, m2,
      (fun sk h => by rw [hsk] at h; cases h), (fun _ => ⟨hUS, hj'⟩)⟩
  have hjm : G.molecule.atom p.1 ∈ u.atoms := by rw [hT.1]; exact hj
  have hjm2 : G.molecule.atom p.2 ∈ u.atoms := by rw [hT.2.1]; exact hj
  have bad1 : ∀ t z : GardenDart G, t ∈ tripleDarts G σ v c → z ∉ tripleDarts G σ v c →
      G.molecule.atom z ∈ u.atoms → ¬ G.molecule.InGroup u.atoms z →
      G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z) → False := by
    intro t z ht hz hz1 hz2 hs
    obtain ⟨-, -, rt⟩ := (mem_tripleDarts hM σ hu hcr).mp ht
    exact hz ((mem_tripleDarts hM σ hu hcr).mpr ⟨hz1, hz2, by rw [← hs]; exact rt⟩)
  have dispatch : ∀ (P : GardenDart G → GardenDart G → Prop), (∀ t z, P t z → P z t) →
      (∀ t z, t ∈ tripleDarts G σ v c → z ∉ tripleDarts G σ v c → G.molecule.atom z ∈ u.atoms →
        ¬ G.molecule.InGroup u.atoms z → P t z → False) → P p.1 p.2 → False := by
    intro P hsymm hbad hP
    rcases hin with hi | hi <;> rcases hout with ho | ho
    · exact ho hi
    · exact hbad _ _ hi ho hjm2 hn2 hP
    · exact hbad _ _ hi ho hjm hn1 (hsymm _ _ hP)
    · exact ho hi
  rcases repC_class hM σ (G.molecule.atom (G.molecule.mate d1)) with ⟨hn, hiff⟩ | ⟨u', hu', hn0, hiff⟩
  · have hs : G.molecule.atom (G.molecule.mate d1) = G.molecule.atom (G.molecule.mate d2) :=
      ((hiff _).mp (r2.trans r1.symm)).symm
    have hP : PairSameAtom G p := hT1 ⟨(d1, d2), hsp', hs⟩
    exact dispatch (fun t z => G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z))
      (fun _ _ h => h.symm) (fun t z ht hz hz1 hz2 hs' => bad1 t z ht hz hz1 hz2 hs') hP
  · obtain ⟨S', hS'm, -, hu'S'⟩ := mem_unitBlocks.mp hu'
    have hP' : PairSameUnit G (d1, d2) :=
      ⟨S', hS'm, u', hu'S', hn0, (hiff _).mp (r2.trans r1.symm)⟩
    have hbad2 : ∀ t z : GardenDart G, t ∈ tripleDarts G σ v c → z ∉ tripleDarts G σ v c →
        G.molecule.atom z ∈ u.atoms → ¬ G.molecule.InGroup u.atoms z →
        (∃ S'' ∈ maximalGroups G.molecule, ∃ u'' ∈ (groupUnitsOf G S'').units,
          G.molecule.atom (G.molecule.mate t) ∈ u''.atoms ∧ G.molecule.atom (G.molecule.mate z) ∈ u''.atoms) →
        False := by
      intro t z ht hz hz1 hz2 ⟨S'', hS''m, u'', hu''S'', hm1, hm2⟩
      obtain ⟨-, -, rt⟩ := (mem_tripleDarts hM σ hu hcr).mp ht
      have hmt : G.molecule.atom (G.molecule.mate t) ∈ u'.atoms := (hiff _).mp (rt.trans r1.symm)
      have huu : u'' = u' := unit_eq_any hM hS''m hS'm hu''S'' hu'S' hm1 hmt
      subst huu
      exact hz ((mem_tripleDarts hM σ hu hcr).mpr ⟨hz1, hz2, (hiff _).mpr hm2 |>.trans r1⟩)
    rcases hT2 ⟨(d1, d2), hsp', hP'⟩ with hP | hP
    · exact dispatch (fun t z => G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z))
        (fun _ _ h => h.symm) (fun t z ht hz hz1 hz2 hs' => bad1 t z ht hz hz1 hz2 hs') hP
    · exact dispatch (fun t z => ∃ S'' ∈ maximalGroups G.molecule, ∃ u'' ∈ (groupUnitsOf G S'').units,
          G.molecule.atom (G.molecule.mate t) ∈ u''.atoms ∧ G.molecule.atom (G.molecule.mate z) ∈ u''.atoms)
        (fun t z ⟨S'', h1, u'', h2, h3, h4⟩ => ⟨S'', h1, u'', h2, h4, h3⟩)
        (fun t z ht hz hz1 hz2 hP => hbad2 t z ht hz hz1 hz2 hP) hP

end whole

theorem two_not_erased {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) {e0 : D} {a b : V}
    (hends : M.ends e0 = s(a, b)) (hab : a ≠ b) {j' : V} (hj' : j' = a ∨ j' = b) {e1 e2 : D} (hne : e1 ≠ e2)
    (h1 : M.atom e1 = j') (h2 : M.atom e2 = j') :
    (e1 ≠ e0 ∧ e1 ≠ M.mate e0) ∨ (e2 ≠ e0 ∧ e2 ≠ M.mate e0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c3⟩ := hcon
  unfold Molecule.ends at hends
  have key : M.atom e0 ≠ M.atom (M.mate e0) := by
    intro h
    rw [h] at hends
    rcases Sym2.eq_iff.mp hends with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · exact hab (h5.symm.trans h6)
    · exact hab (h6.symm.trans h5)
  by_cases d1 : e1 = e0
  · by_cases d2 : e2 = e0
    · exact hne (d1.trans d2.symm)
    · have d2' := c3 d2
      exact key ((congrArg M.atom d1.symm).trans (h1.trans (h2.symm.trans (congrArg M.atom d2'))))
  · have d1' := c1 d1
    by_cases d2 : e2 = e0
    · exact key ((congrArg M.atom d2.symm).trans (h2.trans (h1.symm.trans (congrArg M.atom d1'))))
    · exact hne (d1'.trans (c3 d2).symm)

theorem ext_sub_gen {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
    {X Y : Finset V} {j j1 j2 : V} (hX : N.IsBlock X j j1) (hY : N.IsBlock Y j j2) (hXY : X ⊆ Y) {d : D}
    (hd : N.atom d = j) (hg : N.InGroup Y d) : N.InGroup X d :=
  subEq hXY ((block_joint_degrees N hX).1.trans (block_joint_degrees N hY).1.symm) hd hg

/-- The darts at the group joint `j'` of a unit of a skipped vine: an internal dart of the group (not the added bond) that is
external to the unit does not exist. -/
theorem skip_ext_sub {S : Finset (GBranch G.tree)} (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {u : CLBlock G} (hmem : u ∈ (groupUnitsOf G S).units) {j j' : GBranch G.tree} (hj : j ∈ u.atoms)
    (hjxy : j = sk.x ∨ j = sk.y) (hj' : j' = u.upper ∨ j' = u.lower) (hne : j' ≠ j) :
    (j' = sk.a ∨ j' = sk.b) ∧
    (∀ d : GardenDart G, G.molecule.atom d = j' → G.molecule.InGroup S d →
      (∀ e, sk.bond = some e → d ≠ e ∧ d ≠ G.molecule.mate e) → G.molecule.InGroup u.atoms d) ∧
    (∀ e0, sk.bond = some e0 → G.molecule.ends e0 = s(sk.a, sk.b) ∧ sk.a ≠ sk.b) := by
  have hsu := (groupUnitsOf G S).skip_units sk hsk
  have hxy : sk.x ≠ sk.y := sk.vine.choose_spec.1.2.2.2.1
  have hxA := x_mem_A' sk
  have hsub : u.atoms ⊆ S := (groupUnitsOf G S).sub u hmem
  have hbond : ∀ e0, sk.bond = some e0 → G.molecule.ends e0 = s(sk.a, sk.b) ∧ sk.a ≠ sk.b := fun e0 he =>
    ⟨(sk.blockN e0 he).1, (sk.blockN e0 he).2.2.2.2.1⟩
  rcases hsu.1 u hmem with ⟨hL, hl⟩ | ⟨hR, hr⟩
  · have hjx : j = sk.x := by
      rcases hjxy with h | h
      · exact h
      · exfalso
        rw [hL] at hj
        rcases sk.left with ⟨h0, -⟩ | ⟨-, -, -, hLA⟩
        · rw [h0] at hj; simp at hj
        · have : sk.y ∈ sk.L0 ∩ sk.A := mem_inter.mpr ⟨h ▸ hj, hxA.2⟩
          rw [hLA, mem_singleton] at this
          exact hxy this.symm
    have hj'a : j' = sk.a := by
      rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hj' with h | h
      · rw [h, h1]
      · exact absurd (h.trans (h2.trans hjx.symm)) hne
      · exact absurd (h.trans (h1.trans hjx.symm)) hne
      · rw [h, h2]
    refine ⟨Or.inl hj'a, ?_, hbond⟩
    intro d hd hg hnb
    rcases hb : sk.bond with _ | e0
    · have hSB := sk.blockM hb
      rcases (sk.skelM hb).hL with ⟨h0, -⟩ | ⟨-, hLB, -⟩
      · exfalso
        have := u.isBlock.2.1
        rw [hL, h0] at this; simp at this
      · rw [← hL] at hLB
        exact ext_sub_gen hLB hSB (hL ▸ hsub) (hd.trans hj'a) hg
    · have hSB := (sk.blockN e0 hb).2
      rcases (sk.skelN e0 hb).hL with ⟨h0, -⟩ | ⟨-, hLB, -⟩
      · exfalso
        have := u.isBlock.2.1
        rw [hL, h0] at this; simp at this
      · rw [← hL] at hLB
        have hdn := hnb e0 hb
        exact ext_sub_gen hLB hSB (hL ▸ hsub) (d := ⟨d, hdn.1, hdn.2⟩) (hd.trans hj'a) hg
  · have hjy : j = sk.y := by
      rcases hjxy with h | h
      · exfalso
        rw [hR] at hj
        rcases sk.right with ⟨h0, -⟩ | ⟨-, -, -, hRA⟩
        · rw [h0] at hj; simp at hj
        · have : sk.x ∈ sk.R0 ∩ sk.A := mem_inter.mpr ⟨h ▸ hj, hxA.1⟩
          rw [hRA, mem_singleton] at this
          exact hxy this
      · exact h
    have hj'b : j' = sk.b := by
      rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hj' with h | h
      · exact absurd (h.trans (h1.trans hjy.symm)) hne
      · rw [h, h2]
      · rw [h, h1]
      · exact absurd (h.trans (h2.trans hjy.symm)) hne
    refine ⟨Or.inr hj'b, ?_, hbond⟩
    intro d hd hg hnb
    rcases hb : sk.bond with _ | e0
    · have hSB := block_swap_joints _ (sk.blockM hb)
      rcases (sk.skelM hb).hR with ⟨h0, -⟩ | ⟨-, hRB, -⟩
      · exfalso
        have := u.isBlock.2.1
        rw [hR, h0] at this; simp at this
      · rw [← hR] at hRB
        exact ext_sub_gen (block_swap_joints _ hRB) hSB (hR ▸ hsub) (hd.trans hj'b) hg
    · have hSB := block_swap_joints _ (sk.blockN e0 hb).2
      rcases (sk.skelN e0 hb).hR with ⟨h0, -⟩ | ⟨-, hRB, -⟩
      · exfalso
        have := u.isBlock.2.1
        rw [hR, h0] at this; simp at this
      · rw [← hR] at hRB
        have hdn := hnb e0 hb
        exact ext_sub_gen (block_swap_joints _ hRB) hSB (hR ▸ hsub) (d := ⟨d, hdn.1, hdn.2⟩) (hd.trans hj'b) hg

theorem skip_two_ext_false {S : Finset (GBranch G.tree)} (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {u : CLBlock G} (hmem : u ∈ (groupUnitsOf G S).units) {j j' : GBranch G.tree} (hj : j ∈ u.atoms)
    (hjxy : j = sk.x ∨ j = sk.y) (hj' : j' = u.upper ∨ j' = u.lower) (hne : j' ≠ j)
    {e1 e2 : GardenDart G} (hne12 : e1 ≠ e2) (h1 : G.molecule.atom e1 = j') (h2 : G.molecule.atom e2 = j')
    (n1 : ¬ G.molecule.InGroup u.atoms e1) (n2 : ¬ G.molecule.InGroup u.atoms e2)
    (g1 : G.molecule.InGroup S e1) (g2 : G.molecule.InGroup S e2) : False := by
  obtain ⟨hjab, P, hbond⟩ := skip_ext_sub sk hsk hmem hj hjxy hj' hne
  rcases hb : sk.bond with _ | e0
  · exact n1 (P e1 h1 g1 (fun e he => by rw [hb] at he; cases he))
  · obtain ⟨hends, hab⟩ := hbond e0 hb
    rcases two_not_erased G.molecule hends hab hjab hne12 h1 h2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact n1 (P e1 h1 g1 (fun e he => by rw [hb] at he; cases he; exact ⟨a1, a2⟩))
    · exact n2 (P e2 h2 g2 (fun e he => by rw [hb] at he; cases he; exact ⟨a1, a2⟩))

section skipcase
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

/-- B1b (Mk-general form of `mem_group_of_repC`). -/
theorem mem_group_of_repCMk {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    {n0 m : GBranch G.tree} (hn0 : n0 ∈ S) {Mk : Set (Stage1.CLVine _)} (h : repC (stSt (Mk := Mk) G σ).cls m = repC (stSt (Mk := Mk) G σ).cls n0) : m ∈ S := by
  rcases repC_classMk (Mk := Mk) hM σ n0 with ⟨-, hiff⟩ | ⟨u', hu', hn0', hiff⟩
  · rw [(hiff m).mp h]; exact hn0
  · obtain ⟨S', hS'm, -, hu'S'⟩ := (mem_unitBlocksMk (Mk := Mk)).mp hu'
    have hsub := groupUnitsMk_sub (Mk := Mk) (u := u') hu'S'
    have hSS : S = S' := by
      by_contra hne
      exact Finset.disjoint_left.mp (groups_disjoint hM hS hS'm hne) hn0 (hsub hn0')
    subst hSS
    exact groupUnitsMk_sub (Mk := Mk) (u := u') hu'S' ((hiff m).mp h)

theorem mem_group_of_repC {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    {n0 m : GBranch G.tree} (hn0 : n0 ∈ S) (h : repC (stSt G σ).cls m = repC (stSt G σ).cls n0) : m ∈ S := mem_group_of_repCMk (Mk := ∅) hM σ hS hn0 h

/-- **R37, units of a skipped vine.**  The hinge pair of the unit (the external pair at the joint `x`/`y` of the vine, a
`HingeSpec` pair) consists of two bonds of a triple bond of the hinge. -/
theorem skip_pair_in_triple {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) {u : CLBlock G} (hmem : u ∈ (groupUnitsOf G S).units)
    {sk : SkipData G S} (hsk : (groupUnitsOf G S).skip = some sk) {v c : GBranch (stSt G σ).G.tree}
    (hcr : (stSt G σ).M.ob v = u.upper) (hvc : v ≠ c) (h3 : (stSt G σ).G.molecule.bondsBetween v c = 3)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hau : a ∈ u.atoms) (hspec : HingeSpec G S a p) :
    p.1 ∈ tripleDarts G σ v c ∧ p.2 ∈ tripleDarts G σ v c := by
  classical
  have hu : u ∈ unitBlocks G σ := mem_unitBlocks.mpr ⟨S, hS, hσ, hmem⟩
  obtain ⟨j, hj, hT, hn1, hn2, hrel, -⟩ := hingeSpec_body hM hS hspec hmem hau
  obtain ⟨hjxy, hmA1, hmA2, -⟩ := hrel sk hsk
  have hjj := skip_joint sk hsk hmem hj hjxy
  have hne : p.1 ≠ p.2 := fun h => hT.2.2.2 (by rw [h])
  rcases core_comb hM σ hu hcr hvc h3 hjj hT.1 hT.2.1 hn1 hn2 hne with
    h | ⟨j', hj', hj'ne, hsubE, hcard, hin, hout⟩
  · exact h
  exfalso
  obtain ⟨e1, e2, hne12, hE⟩ := Finset.card_eq_two.mp hcard
  have he1 : e1 ∈ extAt G u j' := by rw [hE]; simp
  have he2 : e2 ∈ extAt G u j' := by rw [hE]; simp
  obtain ⟨h1, n1⟩ := mem_extAt.mp he1
  obtain ⟨h2, n2⟩ := mem_extAt.mp he2
  obtain ⟨-, -, r1⟩ := (mem_tripleDarts hM σ hu hcr).mp (hsubE he1)
  obtain ⟨-, -, r2⟩ := (mem_tripleDarts hM σ hu hcr).mp (hsubE he2)
  obtain ⟨t, hmt, rt⟩ : ∃ t : GardenDart G, G.molecule.atom (G.molecule.mate t) ∈ sk.A ∧
      repC (stSt G σ).cls (G.molecule.atom (G.molecule.mate t)) = (stSt G σ).M.ob c := by
    rcases hin with hi | hi
    · exact ⟨p.1, hmA1, ((mem_tripleDarts hM σ hu hcr).mp hi).2.2⟩
    · exact ⟨p.2, hmA2, ((mem_tripleDarts hM σ hu hcr).mp hi).2.2⟩
  have hAS : sk.A ⊆ S := by
    intro x hx
    have h : x ∈ sk.L0 ∪ sk.A ∪ sk.R0 := mem_union_left _ (mem_union_right _ hx)
    rwa [← sk.hS] at h
  have hmS : ∀ e : GardenDart G, repC (stSt G σ).cls (G.molecule.atom (G.molecule.mate e)) = (stSt G σ).M.ob c →
      G.molecule.atom (G.molecule.mate e) ∈ S := fun e re =>
    mem_group_of_repC hM σ hS (hAS hmt) (re.trans rt.symm)
  have hj'S : j' ∈ S := by
    have hj'mem : j' ∈ u.atoms := by
      rcases hj' with rfl | rfl
      · exact u.isBlock.2.1
      · exact u.isBlock.2.2.1
    exact (groupUnitsOf G S).sub u hmem hj'mem
  exact skip_two_ext_false sk hsk hmem hj hjxy hj' hj'ne hne12 h1 h2 n1 n2
    ⟨h1 ▸ hj'S, hmS e1 r1⟩ ⟨h2 ▸ hj'S, hmS e2 r2⟩

end skipcase

end WaveTurbulence.VineA.NormalizedSplice
