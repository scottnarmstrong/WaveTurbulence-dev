/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceDesig
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R28: the hinge pairs and the choice data `C_1` of `G_sb`

(R28) `hingePair G σ v`, the pair `(ℓ_1, ℓ_2)` of TARGET subpro(5) at the hinge `v` (always a `ProperPair`, i.e. the lift of an
external out/in pair of the unit with crown `v` at one of its joints):
1. if `v` is the designated atom of a group `S`: the LIFT of `hingeOrigPair` of `S` (so `Cs.first/second` is the entry pair of
   `gapSpecification` at `v`);
2. otherwise the lift of a pair `HingeSpec G S u.upper p` of the unit `u` with crown `v` (for a hinge of a skipped vine
   it lies inside the residual object);
3. otherwise a proper pair.
`collectionChoices G σ`, `structural_collectionChoices`, `hingeOutsideFirst_collectionChoices`: as before.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The designated atom of the group `S` in `G_sb`. -/
@[expose] noncomputable def groupAtom (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    (Mk : Set (CLVine G) := ∅) : Option (GBranch (stSt G σ Mk).G.tree) :=
  (groupJoint G S Mk).map ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls)

/-- The lift to `G_sb` (at the atom `v`) of a pair of darts of the original garden: darts of `G_sb` whose images
under `od` are the given darts and which form a `TripleAt` at `v`. -/
@[expose] noncomputable def liftPair (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (v : GBranch (stSt G σ Mk).G.tree)
    (p : GardenDart G × GardenDart G) : Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) := by
  classical
  exact if h : ∃ q : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G,
      (stSt G σ Mk).M.od q.1 = p.1 ∧ (stSt G σ Mk).M.od q.2 = p.2 ∧ TripleAt (stSt G σ Mk).G v q.1 q.2
  then some (Classical.choose h) else none

theorem liftPair_of_exists {σ : Prescription G} {v : GBranch (stSt G σ).G.tree} {p : GardenDart G × GardenDart G}
    (h : ∃ q : GardenDart (stSt G σ).G × GardenDart (stSt G σ).G,
      (stSt G σ).M.od q.1 = p.1 ∧ (stSt G σ).M.od q.2 = p.2 ∧ TripleAt (stSt G σ).G v q.1 q.2) :
    ∃ q, liftPair G σ v p = some q ∧ (stSt G σ).M.od q.1 = p.1 ∧ (stSt G σ).M.od q.2 = p.2 ∧
      TripleAt (stSt G σ).G v q.1 q.2 := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  unfold liftPair
  rw [dif_pos h]

theorem liftPair_spec {σ : Prescription G} {v : GBranch (stSt G σ).G.tree} {p : GardenDart G × GardenDart G}
    {q : GardenDart (stSt G σ).G × GardenDart (stSt G σ).G} (h : liftPair G σ v p = some q) :
    (stSt G σ).M.od q.1 = p.1 ∧ (stSt G σ).M.od q.2 = p.2 ∧ TripleAt (stSt G σ).G v q.1 q.2 := by
  classical
  unfold liftPair at h
  split_ifs at h with hex
  · rw [Option.some.injEq] at h
    exact h ▸ Classical.choose_spec hex

/-- The pair at a hinge designated atom: the lift of `hingeOrigPair`. -/
@[expose] noncomputable def hingeEntryPair (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVine G)} (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) :=
  (hingeOrigPair G S Mk).bind (liftPair G σ v)

/-- B1a (o75 Theorem 7.5′ clause (5)): a hinge pair of a run `u` of a marked group: an out/in pair of darts of the
original garden at an outer joint of `u`, both external to `u`.  (The 75-F1 rule, which prefers among these the
bonds of the survivor removed first, is a marked-group branch of B2c.) -/
@[expose] def HingeSpecRun (G : Garden w) (u : CLBlock G) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ j, (j = u.upper ∨ j = u.lower) ∧ TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧
    ¬ G.molecule.InGroup u.atoms p.2

/-- **The hinge pair of TARGET subpro(5)** (R28): see the module docstring.  B1a: with the marked vine set `Mk`
the units are `groupUnitsMk` (runs in a marked group, with the run pair `HingeSpecRun`). -/
@[expose] noncomputable def hingePair (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) := by
  classical
  exact if h : ∃ p : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ∃ S ∈ maximalGroups G.molecule,
      groupAtom G σ S Mk = some v ∧ hingeEntryPair G σ S v = some p ∧ ProperPair G σ v p.1 p.2
  then some (Classical.choose h)
  else if h2 : ∃ q : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ∃ S ∈ maximalGroups G.molecule,
      ∃ u ∈ groupUnitsMk G Mk S, (stSt G σ Mk).M.ob v = u.upper ∧
        ∃ p, (¬ markedGroup G Mk S → HingeSpec G S u.upper p) ∧ (markedGroup G Mk S → HingeSpecRun G u p) ∧
          liftPair G σ v p = some q ∧ ProperPair G σ v q.1 q.2
  then some (Classical.choose h2)
  else if h3 : ∃ p : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ProperPair G σ v p.1 p.2
  then some (Classical.choose h3) else none

/-- **The choice data `C_1`, hinges and hinge pairs of `G_sb`.**  B1a: trailing marked vine set `Mk` (default `∅`). -/
@[expose] noncomputable def collectionChoices (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G) := ∅) :
    SubproChoices (stSt G σ Mk).G where
  count := (objects G σ Mk).length
  collection := fun i => (objects G σ Mk).get i
  hinges := (stSt G σ Mk).hinges
  first := fun v => (hingePair G σ v).map Prod.fst
  second := fun v => (hingePair G σ v).map Prod.snd

/-- B1b (Mk-general form of `structural_collectionChoices`). -/
theorem structural_collectionChoicesMk (hM : G.molecule.IsMolecule) (σ : Prescription G)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) {Mk : Set (Stage1.CLVine _)} : (collectionChoices (Mk := Mk) G σ).Structural := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨_, _, _, _, hS⟩ := mem_objectsMk (Mk := Mk) (List.get_mem (objects (Mk := Mk) G σ) i)
    exact hS.allowed
  · intro i j hne
    have hp := List.pairwise_iff_get.mp (objects_pairwiseMk (Mk := Mk) hM σ)
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact hp i j h
    · exact (hp j i h).symm
  · intro a b hab
    exact (stSt (Mk := Mk) G σ).triple_hinge hno a b hab

theorem structural_collectionChoices (hM : G.molecule.IsMolecule) (σ : Prescription G)
    (hno : ∀ a b, G.molecule.bondsBetween a b ≠ 3) : (collectionChoices G σ).Structural := structural_collectionChoicesMk (Mk := ∅) hM σ hno

/-- B1b (Mk-general form of `hingeOutsideFirst_collectionChoices`). -/
theorem hingeOutsideFirst_collectionChoicesMk (σ : Prescription G) {Mk : Set (Stage1.CLVine _)} :
    ∀ v ∈ (collectionChoices (Mk := Mk) G σ).hinges, ∀ i, ¬ ((collectionChoices (Mk := Mk) G σ).collection i).IsInterior v := by
  intro v hv i hint
  obtain ⟨_, _, _, _, hS⟩ := mem_objectsMk (Mk := Mk) (List.get_mem (objects (Mk := Mk) G σ) i)
  have hcn : (stSt (Mk := Mk) G σ).cls ((stSt (Mk := Mk) G σ).M.ob v) ≠ none := ((stSt (Mk := Mk) G σ).mem_hinges v).mp hv
  rcases hS.hinge v hcn hint.1 with h | h
  · exact hint.2.1 h
  · exact hint.2.2 h

theorem hingeOutsideFirst_collectionChoices (σ : Prescription G) :
    ∀ v ∈ (collectionChoices G σ).hinges, ∀ i, ¬ ((collectionChoices G σ).collection i).IsInterior v := hingeOutsideFirst_collectionChoicesMk (Mk := ∅) σ


theorem properPair_congr {σ : Prescription G} {v : GBranch (stSt G σ).G.tree}
    {y1 y2 q1 q2 : GardenDart (stSt G σ).G} (h : ProperPair G σ v y1 y2)
    (h1 : (stSt G σ).M.od q1 = (stSt G σ).M.od y1) (h2 : (stSt G σ).M.od q2 = (stSt G σ).M.od y2)
    (hT : TripleAt (stSt G σ).G v q1 q2) : ProperPair G σ v q1 q2 := by
  obtain ⟨-, u, hu, hc, j, hj, e1, e2, n1, n2⟩ := h
  exact ⟨hT, u, hu, hc, j, hj, by rw [h1]; exact e1, by rw [h2]; exact e2, by rw [h1]; exact n1,
    by rw [h2]; exact n2⟩

section cases
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

/-- A hinge not at a joint of an object of `C_1` is the designated atom of a whole-group unit group, and the lift of
the `hingeOrigPair` of the group is a proper pair at it. -/
theorem hinge_entry {v : GBranch (stSt G σ).G.tree} (hv : v ∈ (stSt G σ).hinges)
    (hno : ¬ ∃ O ∈ objects G σ, O.upper = v ∨ O.lower = v) :
    ∃ p : GardenDart (stSt G σ).G × GardenDart (stSt G σ).G, ∃ S ∈ maximalGroups G.molecule,
      groupAtom G σ S = some v ∧ hingeEntryPair G σ S v = some p ∧ ProperPair G σ v p.1 p.2 := by
  classical
  have hcn := ((stSt G σ).mem_hinges v).mp hv
  by_cases h : ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob v ∈ u.atoms
  swap
  · push Not at h
    exact absurd (stSt_cls_none hM σ h) hcn
  obtain ⟨u, hu, hvu⟩ := h
  have h1 := stSt_cls_mem hM σ hu hvu
  have hcr : (stSt G σ).M.ob v = u.upper := by
    have := ((stSt G σ).M.ob_range ((stSt G σ).M.ob v)).mp ⟨v, rfl⟩
    rcases this with h3 | h3
    · rw [h1] at h3; cases h3
    · rw [h1] at h3; exact (Option.some.inj h3).symm
  obtain ⟨S, hSm, hσ, hmem⟩ := mem_unitBlocks.mp hu
  rcases hsk : (groupUnitsOf G S).skip with _ | sk
  · -- whole-group unit
    have hUS := (groupUnitsOf G S).noskip_units hsk u hmem
    obtain ⟨a0, ha0⟩ := exists_groupJoint_eq hSm
    have ha0S := (groupJoint_kind ha0).1
    have ha0u : a0 ∈ u.atoms := hUS ▸ ha0S
    obtain ⟨p, hp, hspec⟩ := hingeOrigPair_spec ha0 ⟨u, hmem, ha0u⟩
    obtain ⟨u', hu', hau', j, hj, hT, hn1, hn2, hrel⟩ := hspec
    have huu : u' = u := by
      have hu'b : u' ∈ unitBlocks G σ := mem_unitBlocks.mpr ⟨S, hSm, hσ, hu'⟩
      exact unit_eq_of_mem hM σ hu'b hu hau' ha0u
    subst huu
    obtain ⟨-, hjw⟩ := hrel.2 hsk
    have hat : (stSt G σ).M.pi (stSt G σ).hcls a0 = v := by
      apply (stSt G σ).M.ob_inj
      rw [(stSt G σ).M.ob_pi (stSt G σ).hcls a0, hcr]
      exact stSt_repC_mem hM σ hu ha0u
    obtain ⟨y1, y2, hy1, hy2, hP⟩ := ext_lift_darts hM σ hu hcr (by rcases hjw with rfl | rfl; exact u'.isBlock.2.1; exact u'.isBlock.2.2.1) hjw
      hT.1 hT.2.1 hn1 hn2 hT.2.2.2
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_exists (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hP.1⟩
    refine ⟨q, S, hSm, ?_, ?_, ?_⟩
    · unfold groupAtom; rw [ha0]; simp [hat]
    · unfold hingeEntryPair; rw [hp]; exact hq
    · exact properPair_congr hP (by rw [hq1, hy1]) (by rw [hq2, hy2]) hqT
  · -- a skipped vine: the hinge is a joint of the object of the group
    exfalso
    apply hno
    have hoS : HasObj G S := Or.inr ⟨sk, hsk⟩
    have hSg : S ∈ sgGroups G σ := mem_sgGroups.mpr ⟨hSm, hσ⟩
    have hex : objOf G σ S = some (Classical.choose (exists_obj hM σ hSm hσ hoS)) := by
      unfold objOf
      rw [dif_pos ⟨hM, hSm, hσ, hoS, not_markedGroup_empty G S, exists_obj hM σ hSm hσ hoS⟩]
    set O := Classical.choose (exists_obj hM σ hSm hσ hoS)
    have hOm : O ∈ objects G σ := List.mem_filterMap.mpr ⟨S, hSg, hex⟩
    obtain ⟨-, -, -, hOspec⟩ := objOf_spec (Option.mem_def.mpr hex)
    obtain ⟨A, -, -, -, hsrc⟩ := hOspec.src
    rcases hsrc with ⟨⟨hhv, hnh⟩, -⟩ | ⟨sk', hsk', -, hup, hlo, -, -⟩
    · have := (groupUnitsOf G S).hv_empty hhv hnh
      rw [this] at hmem
      cases hmem
    · rw [hsk] at hsk'
      cases hsk'
      have hsu := (groupUnitsOf G S).skip_units sk hsk
      refine ⟨O, hOm, ?_⟩
      rcases hsu.1 u hmem with ⟨hL, hl⟩ | ⟨hR, hr⟩
      · have hxu : sk.x ∈ u.atoms := by
          rcases hl with ⟨_, h2⟩ | ⟨h2, _⟩
          · rw [← h2]; exact u.isBlock.2.2.1
          · rw [← h2]; exact u.isBlock.2.1
        have : (stSt G σ).M.pi (stSt G σ).hcls sk.x = v := by
          apply (stSt G σ).M.ob_inj
          rw [(stSt G σ).M.ob_pi (stSt G σ).hcls sk.x, hcr]
          exact stSt_repC_mem hM σ hu hxu
        exact Or.inl (hup.trans this)
      · have hxu : sk.y ∈ u.atoms := by
          rcases hr with ⟨h2, _⟩ | ⟨_, h2⟩
          · rw [← h2]; exact u.isBlock.2.1
          · rw [← h2]; exact u.isBlock.2.2.1
        have : (stSt G σ).M.pi (stSt G σ).hcls sk.y = v := by
          apply (stSt G σ).M.ob_inj
          rw [(stSt G σ).M.ob_pi (stSt G σ).hcls sk.y, hcr]
          exact stSt_repC_mem hM σ hu hxu
        exact Or.inr (hlo.trans this)

end cases

theorem x_mem_A' {S : Finset (GBranch G.tree)} (sk : SkipData G S) : sk.x ∈ sk.A ∧ sk.y ∈ sk.A := by
  obtain ⟨X, hX⟩ := sk.vine
  exact ⟨hX.1.2.1, hX.1.2.2.1⟩

/-- A joint of a skipped vine lying in a unit of its group is a joint of the unit. -/
theorem skip_joint {S : Finset (GBranch G.tree)} (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {u : CLBlock G} (hu : u ∈ (groupUnitsOf G S).units) {j : GBranch G.tree} (hj : j ∈ u.atoms)
    (hjxy : j = sk.x ∨ j = sk.y) : j = u.upper ∨ j = u.lower := by
  have hxy : sk.x ≠ sk.y := sk.vine.choose_spec.1.2.2.2.1
  rcases ((groupUnitsOf G S).skip_units sk hsk).1 u hu with ⟨hL, hl⟩ | ⟨hR, hr⟩
  · rw [hL] at hj
    rcases hjxy with rfl | rfl
    · rcases hl with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h.symm
      · exact Or.inl h.symm
    · exfalso
      rcases sk.left with ⟨h0, -⟩ | ⟨-, -, -, hLA⟩
      · rw [h0] at hj; cases hj
      · have : sk.y ∈ sk.L0 ∩ sk.A := mem_inter.mpr ⟨hj, (x_mem_A' sk).2⟩
        rw [hLA, mem_singleton] at this
        exact hxy this.symm
  · rw [hR] at hj
    rcases hjxy with rfl | rfl
    · exfalso
      rcases sk.right with ⟨h0, -⟩ | ⟨-, -, -, hRA⟩
      · rw [h0] at hj; cases hj
      · have : sk.x ∈ sk.R0 ∩ sk.A := mem_inter.mpr ⟨hj, (x_mem_A' sk).1⟩
        rw [hRA, mem_singleton] at this
        exact hxy this
    · rcases hr with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm

section pairs
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

/-- Every hinge carries the lift of a `HingeSpec` pair of its unit, which is proper. -/
theorem hinge_unit_pair {v : GBranch (stSt G σ).G.tree} (hv : v ∈ (stSt G σ).hinges) :
    ∃ q : GardenDart (stSt G σ).G × GardenDart (stSt G σ).G, ∃ S ∈ maximalGroups G.molecule,
      ∃ u ∈ (groupUnitsOf G S).units, (stSt G σ).M.ob v = u.upper ∧
        ∃ p, HingeSpec G S u.upper p ∧ liftPair G σ v p = some q ∧ ProperPair G σ v q.1 q.2 := by
  classical
  have hcn := ((stSt G σ).mem_hinges v).mp hv
  by_cases h : ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob v ∈ u.atoms
  swap
  · push Not at h
    exact absurd (stSt_cls_none hM σ h) hcn
  obtain ⟨u, hu, hvu⟩ := h
  have h1 := stSt_cls_mem hM σ hu hvu
  have hcr : (stSt G σ).M.ob v = u.upper := by
    have := ((stSt G σ).M.ob_range ((stSt G σ).M.ob v)).mp ⟨v, rfl⟩
    rcases this with h3 | h3
    · rw [h1] at h3; cases h3
    · rw [h1] at h3; exact (Option.some.inj h3).symm
  obtain ⟨S, hSm, hσ, hmem⟩ := mem_unitBlocks.mp hu
  obtain ⟨p, hsp⟩ := exists_hingeSpec (S := S) (a := u.upper) ⟨u, hmem, u.isBlock.2.1⟩
  have hsp' := hsp
  obtain ⟨u', hu', hau', j, hj, hT, hn1, hn2, hrel⟩ := hsp'
  have huu : u' = u :=
    unit_eq_of_mem hM σ (mem_unitBlocks.mpr ⟨S, hSm, hσ, hu'⟩) hu hau' u.isBlock.2.1
  subst huu
  have hjj : j = u'.upper ∨ j = u'.lower := by
    rcases hsk : (groupUnitsOf G S).skip with _ | sk
    · exact (hrel.2 hsk).2
    · exact skip_joint sk hsk hu' hj (hrel.1 sk hsk).1
  obtain ⟨y1, y2, hy1, hy2, hP⟩ := ext_lift_darts hM σ hu hcr hj hjj hT.1 hT.2.1 hn1 hn2 hT.2.2.2
  obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_exists (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hP.1⟩
  exact ⟨q, S, hSm, u', hu', hcr, p, hsp, hq, properPair_congr hP (by rw [hq1, hy1]) (by rw [hq2, hy2]) hqT⟩

end pairs

/-- A merged first joint lies in a unit of its group. -/
theorem hinge_unit (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) {a : GBranch G.tree} (ha : groupJoint G S = some a)
    (hh : (stSt G σ).M.pi (stSt G σ).hcls a ∈ (stSt G σ).hinges) :
    σ S = Molecule.GapKind.SG ∧ ∃ u ∈ (groupUnitsOf G S).units, a ∈ u.atoms := by
  have haS := (groupJoint_kind ha).1
  have h1 := ((stSt G σ).mem_hinges _).mp hh
  rw [(stSt G σ).M.ob_pi] at h1
  by_cases h : ∃ u ∈ unitBlocks G σ, a ∈ u.atoms
  · obtain ⟨u, hu, hau⟩ := h
    obtain ⟨S'', hS''m, hσ, hmem⟩ := mem_unitBlocks.mp hu
    have hsub := (groupUnitsOf G S'').sub u hmem hau
    by_cases hSS : S = S''
    · subst hSS
      exact ⟨hσ, u, hmem, hau⟩
    · exact absurd haS (Finset.disjoint_left.mp (groups_disjoint hM hS hS''m hSS) |> fun f => fun h => f h hsub)
  · push Not at h
    have : repC (stSt G σ).cls a = a := stSt_repC_none hM σ h
    rw [this, stSt_cls_none hM σ h] at h1
    exact absurd rfl h1

/-- **The hinge pair exists at every hinge and is proper.**  It is the lift of a `HingeSpec` pair of the unit with crown
`v`, and the entry pair of the group when `v` is its designated atom; a hinge that is not a joint of an object of `C_1`
is such a designated atom (`hinge_entry`). -/
theorem hingePair_spec (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {v : GBranch (stSt G σ).G.tree} (hv : v ∈ (stSt G σ).hinges) :
    ∃ x y, hingePair G σ v = some (x, y) ∧ ProperPair G σ v x y ∧
      (∃ S ∈ maximalGroups G.molecule, ∃ u ∈ (groupUnitsOf G S).units, (stSt G σ).M.ob v = u.upper ∧
        ∃ p, HingeSpec G S u.upper p ∧ (stSt G σ).M.od x = p.1 ∧ (stSt G σ).M.od y = p.2) ∧
      ((¬ ∃ O ∈ objects G σ, O.upper = v ∨ O.lower = v) →
        ∃ S ∈ maximalGroups G.molecule, groupAtom G σ S = some v ∧ hingeEntryPair G σ S v = some (x, y)) := by
  classical
  have hunit := hinge_unit_pair hM σ hv
  have hentry : (¬ ∃ O ∈ objects G σ, O.upper = v ∨ O.lower = v) →
      ∃ p : GardenDart (stSt G σ).G × GardenDart (stSt G σ).G, ∃ S ∈ maximalGroups G.molecule,
        groupAtom G σ S = some v ∧ hingeEntryPair G σ S v = some p ∧ ProperPair G σ v p.1 p.2 :=
    fun hno => hinge_entry hM σ hv hno
  unfold hingePair
  by_cases h : ∃ p : GardenDart (stSt G σ).G × GardenDart (stSt G σ).G, ∃ S ∈ maximalGroups G.molecule,
      groupAtom G σ S = some v ∧ hingeEntryPair G σ S v = some p ∧ ProperPair G σ v p.1 p.2
  · rw [dif_pos h]
    obtain ⟨S, hS, hga, hep, hP⟩ := Classical.choose_spec h
    refine ⟨(Classical.choose h).1, (Classical.choose h).2, rfl, hP, ?_, ?_⟩
    · obtain ⟨a, ha, hav⟩ : ∃ a, groupJoint G S = some a ∧ (stSt G σ).M.pi (stSt G σ).hcls a = v := by
        unfold groupAtom at hga
        cases hg : groupJoint G S with
        | none => rw [hg] at hga; cases hga
        | some a => rw [hg] at hga; exact ⟨a, rfl, Option.some.inj hga⟩
      obtain ⟨-, u0, hu0, hau0⟩ := hinge_unit hM σ hS ha (hav ▸ hv)
      obtain ⟨p1, hp1, hs1⟩ := hingeOrigPair_spec ha ⟨u0, hu0, hau0⟩
      unfold hingeEntryPair at hep
      rw [hp1] at hep
      simp only [Option.bind_some] at hep
      obtain ⟨hq1, hq2, -⟩ := liftPair_spec hep
      obtain ⟨u, hu, hau, j, hj, hrest⟩ := hs1
      refine ⟨S, hS, u, hu, ?_, p1, ⟨u, hu, u.isBlock.2.1, j, hj, hrest⟩, hq1, hq2⟩
      have huB : u ∈ unitBlocks G σ := by
        obtain ⟨-, σS⟩ := (mem_sgGroups.mp ((mem_sgGroups (σ := σ)).mpr ⟨hS, (hinge_unit hM σ hS ha (hav ▸ hv)).1⟩))
        exact mem_unitBlocks.mpr ⟨S, hS, (hinge_unit hM σ hS ha (hav ▸ hv)).1, hu⟩
      rw [← hav, (stSt G σ).M.ob_pi, stSt_repC_mem hM σ huB hau]
    · intro _
      exact ⟨S, hS, hga, hep⟩
  · rw [dif_neg h]
    have hno : ∃ O ∈ objects G σ, O.upper = v ∨ O.lower = v := by
      by_contra hno
      exact h (hentry hno)
    obtain ⟨q, S, hS, u, hu, hob, p, hsp, hq, hP⟩ := hunit
    have h2 : ∃ q : GardenDart (stSt G σ).G × GardenDart (stSt G σ).G, ∃ S ∈ maximalGroups G.molecule,
        ∃ u ∈ groupUnitsMk G ∅ S, (stSt G σ).M.ob v = u.upper ∧
          ∃ p, (¬ markedGroup G ∅ S → HingeSpec G S u.upper p) ∧ (markedGroup G ∅ S → HingeSpecRun G u p) ∧
            liftPair G σ v p = some q ∧ ProperPair G σ v q.1 q.2 :=
      ⟨q, S, hS, u, by rwa [groupUnitsMk_empty], hob, p, fun _ => hsp,
        fun hm => (not_markedGroup_empty G S hm).elim, hq, hP⟩
    rw [dif_pos h2]
    obtain ⟨S2, hS2, u2, hu2, hob2, p2, hsp2, -, hq2, hP2⟩ := Classical.choose_spec h2
    obtain ⟨hl1, hl2, -⟩ := liftPair_spec hq2
    rw [groupUnitsMk_empty] at hu2
    exact ⟨(Classical.choose h2).1, (Classical.choose h2).2, rfl, hP2,
      ⟨S2, hS2, u2, hu2, hob2, p2, hsp2 (not_markedGroup_empty G S2), hl1, hl2⟩,
      fun hno' => absurd hno hno'⟩

end WaveTurbulence.RedSplice
