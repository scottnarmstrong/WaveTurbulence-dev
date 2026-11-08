/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineObjMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvPairMK
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the hinge pairs of `collectionChoices G σ Mk` (o75 Theorem 7.5′(5))

Every hinge of `G_sb` is the crown of a unit of an SG group (`hinge_groupMk`).
* **Unmarked group** (`¬ markedGroup G Mk S`, units `groupUnitsOf G S`): no survivor has a joint there
  (`not_survPairAt_of_unmarked`), so `hingePair` is main's choice: `hinge_unit_pairMk`, `hinge_entryMk` and
  `hingePair_specMk` are main's `hinge_unit_pair`, `hinge_entry`, `hingePair_spec` for such a hinge.
* **Marked group** (a run): a survivor has a joint in the run (`run_survivor_joint`), so `hingePair` is the 75-F1
  pair of the first survivor with a joint at the hinge (`hingePair_markedHinge`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- **A run of a marked group contains a joint of a survivor** (runs are maximal segments of unmarked-`𝒱`
members of the spine, and the group has a survivor). -/
theorem run_survivor_joint {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)} (hmk : markedGroup G Mk S)
    {u : CLBlock G} (hu : u ∈ (markedUnitsOfMK hmk).runs) :
    ∃ t ∈ (markedUnitsOfMK hmk).surv, t.2.1 ∈ u.atoms ∨ t.2.2 ∈ u.atoms := by
  classical
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hvineM, hingr, hmemb, hsub, hmem⟩ := (markedUnitsOfMK hmk).surv_spine
  obtain ⟨P, R, Q, hL, hRne, hRu, hiff, hP, hQ⟩ := (markedUnitsOfMK hmk).run_canonMK hs hvineM hingr hmemb hu
  have hsurv : ∀ s ∈ L, ¬ UnmMemMK G Mk s → s ∈ (markedUnitsOfMK hmk).surv := fun s hsL hn => (hmem s hsL).mpr hn
  rcases List.eq_nil_or_concat P with hP0 | ⟨P1, s, hPs⟩
  · subst hP0
    rcases Q with _ | ⟨s, Q1⟩
    · exfalso
      obtain ⟨t, -, ht⟩ := groupSurvMk_head hmk
      have htL : t ∈ L := hsub.subset ht
      have htR : t ∈ R := by rw [hL] at htL; simpa using htL
      exact ((hmem t htL).mp ht) (hRu t htR)
    · obtain ⟨R0, r, hRr⟩ := (List.eq_nil_or_concat R).resolve_left hRne
      rw [List.concat_eq_append] at hRr
      subst hRr
      have hs' : Spine N ((R0 ++ [r]) ++ s :: Q1) S a b := by rw [hL] at hs; simpa using hs
      obtain ⟨U1, U2, p, hs1, hs2, -, -⟩ := hs'.split_appMK (by simp) (by simp)
      have e1 : r.2.2 = p := hs1.last_sndMK
      have e2 : s.2.1 = p := hs2.cons_fstMK
      have hrL : r ∈ L := by rw [hL]; simp
      have hsL : s ∈ L := by rw [hL]; simp
      have hr2 : r.2.2 ∈ u.atoms := (hiff _).mpr ⟨r, by simp, (RedSplice.isSomeVine_ends (hvineM r hrL)).2.1⟩
      exact ⟨s, hsurv s hsL (hQ s Q1 rfl), Or.inl (by rw [e2, ← e1]; exact hr2)⟩
  · rw [List.concat_eq_append] at hPs
    obtain ⟨r, R', rfl⟩ := List.exists_cons_of_ne_nil hRne
    have hs' : Spine N ((P1 ++ [s]) ++ r :: (R' ++ Q)) S a b := by rw [hL, hPs] at hs; simpa using hs
    obtain ⟨U1, U2, p, hs1, hs2, -, -⟩ := hs'.split_appMK (by simp) (by simp)
    have e1 : s.2.2 = p := hs1.last_sndMK
    have e2 : r.2.1 = p := hs2.cons_fstMK
    have hrL : r ∈ L := by rw [hL]; simp
    have hsL : s ∈ L := by rw [hL, hPs]; simp
    have hr1 : r.2.1 ∈ u.atoms := (hiff _).mpr ⟨r, by simp, (RedSplice.isSomeVine_ends (hvineM r hrL)).1⟩
    exact ⟨s, hsurv s hsL (hP P1 s hPs), Or.inr (by rw [e1, ← e2]; exact hr1)⟩

/-- A group with a designated atom is unmarked. -/
theorem not_marked_of_groupJoint {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (ha : groupJoint G S Mk = some a) : ¬ markedGroup G Mk S := by
  intro hm
  rw [groupJoint_of_marked hm] at ha
  cases ha

section main
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
include hM

/-- The atoms of a unit map to its crown. -/
theorem pi_of_crown {u : CLBlock G} (hu : u ∈ unitBlocks G σ Mk) {v : GBranch (stSt G σ Mk).G.tree}
    (hcr : (stSt G σ Mk).M.ob v = u.upper) {z : GBranch G.tree} (hz : z ∈ u.atoms) :
    (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z = v := by
  apply (stSt G σ Mk).M.ob_inj
  rw [(stSt G σ Mk).M.ob_pi, stSt_repC_memMk (Mk := Mk) hM σ hu hz, hcr]

/-- **Every hinge is the crown of a unit of an SG group.** -/
theorem hinge_groupMk {v : GBranch (stSt G σ Mk).G.tree} (hv : v ∈ (stSt G σ Mk).hinges) :
    ∃ S, S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧
      ∃ u ∈ groupUnitsMk G Mk S, (stSt G σ Mk).M.ob v = u.upper := by
  classical
  have hcn := ((stSt G σ Mk).mem_hinges v).mp hv
  by_cases h : ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob v ∈ u.atoms
  swap
  · push Not at h
    exact absurd (stSt_cls_noneMk (Mk := Mk) hM σ h) hcn
  obtain ⟨u, hu, hvu⟩ := h
  have h1 := stSt_cls_memMk (Mk := Mk) hM σ hu hvu
  have hcr : (stSt G σ Mk).M.ob v = u.upper := by
    have := ((stSt G σ Mk).M.ob_range ((stSt G σ Mk).M.ob v)).mp ⟨v, rfl⟩
    rcases this with h3 | h3
    · rw [h1] at h3; cases h3
    · rw [h1] at h3; exact (Option.some.inj h3).symm
  obtain ⟨S, hSm, hσ, hmem⟩ := mem_unitBlocksMk.mp hu
  exact ⟨S, hSm, hσ, u, hmem, hcr⟩

/-- **No survivor has a joint at a hinge of an unmarked group** (survivors lie in marked groups). -/
theorem not_survPairAt_of_unmarked {S : Finset (GBranch G.tree)} (hSm : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hnm : ¬ markedGroup G Mk S) {u : CLBlock G} (hu : u ∈ groupUnitsMk G Mk S)
    {v : GBranch (stSt G σ Mk).G.tree} (hcr : (stSt G σ Mk).M.ob v = u.upper) :
    ¬ ∃ q, survPairAt G σ v = some q := by
  classical
  rintro ⟨q, hq⟩
  unfold survPairAt at hq
  obtain ⟨Tj, hTj, -⟩ := Option.bind_eq_some_iff.mp hq
  unfold survJointAt at hTj
  obtain ⟨t, ht, -⟩ := Option.map_eq_some_iff.mp hTj
  have htm := List.mem_of_find?_eq_some ht
  have hp := List.find?_some ht
  obtain ⟨S', hS', -, hmk, htS, htsub⟩ := survivorsMk_group htm
  have hends := RedSplice.isSomeVine_ends ((markedUnitsOfMK hmk).surv_spec t htS).1
  have huB : u ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S, hSm, hσ, hu⟩
  have hvu := pi_of_crown hM σ huB hcr u.isBlock.2.1
  have huS : u.upper ∈ S := groupUnitsMk_sub hu u.isBlock.2.1
  have hvj : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 = v := by simpa using hp
  rcases hvj with h | h
  · have := group_eq_of_pi_eq hM σ hS' hSm (htsub hends.2.1) huS (h.trans hvu.symm)
    subst this
    exact hnm hmk
  · have := group_eq_of_pi_eq hM σ hS' hSm (htsub hends.1) huS (h.trans hvu.symm)
    subst this
    exact hnm hmk

/-- Main's `hinge_unit_pair` at a hinge of an unmarked group. -/
theorem hinge_unit_pairMk {S : Finset (GBranch G.tree)} (hSm : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hnm : ¬ markedGroup G Mk S) {u : CLBlock G}
    (hu : u ∈ (groupUnitsOf G S).units) {v : GBranch (stSt G σ Mk).G.tree}
    (hcr : (stSt G σ Mk).M.ob v = u.upper) :
    ∃ q : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ∃ p, HingeSpec G S u.upper p ∧
      liftPair G σ v p = some q ∧ ProperPair G σ v q.1 q.2 := by
  classical
  have huB : u ∈ unitBlocks G σ Mk :=
    mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩
  obtain ⟨p, hsp⟩ := exists_hingeSpec (S := S) (a := u.upper) ⟨u, hu, u.isBlock.2.1⟩
  have hsp' := hsp
  obtain ⟨u', hu', hau', j, hj, hT, hn1, hn2, hrel⟩ := hsp'
  have huu : u' = u := unit_eq_of_memMk (Mk := Mk) hM σ
    (mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hnm).symm ▸ hu'⟩) huB hau' u.isBlock.2.1
  subst huu
  have hjj : j = u'.upper ∨ j = u'.lower := by
    rcases hsk : (groupUnitsOf G S).skip with _ | sk
    · exact (hrel.2 hsk).2
    · exact skip_joint sk hsk hu' hj (hrel.1 sk hsk).1
  obtain ⟨y1, y2, hy1, hy2, hP⟩ := ext_lift_dartsMk (Mk := Mk) hM σ huB hcr hj hjj hT.1 hT.2.1 hn1 hn2 hT.2.2.2
  obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_existsMk (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hP.1⟩
  exact ⟨q, p, hsp, hq, properPair_congrMk hP (by rw [hq1, hy1]) (by rw [hq2, hy2]) hqT⟩

/-- Main's `hinge_entry` at a hinge of an unmarked group: a hinge that is not a joint of an object of `𝒞₁` is the
designated atom of its group, with the lifted `hingeOrigPair` a proper pair. -/
theorem hinge_entryMk {S : Finset (GBranch G.tree)} (hSm : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hnm : ¬ markedGroup G Mk S) {u : CLBlock G}
    (hmem : u ∈ (groupUnitsOf G S).units) {v : GBranch (stSt G σ Mk).G.tree}
    (hcr : (stSt G σ Mk).M.ob v = u.upper) (hno : ¬ ∃ O ∈ objects G σ Mk, O.upper = v ∨ O.lower = v) :
    ∃ p : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G,
      groupAtom G σ S Mk = some v ∧ hingeEntryPair G σ S v = some p ∧ ProperPair G σ v p.1 p.2 := by
  classical
  have hu : u ∈ unitBlocks G σ Mk :=
    mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hnm).symm ▸ hmem⟩
  rcases hsk : (groupUnitsOf G S).skip with _ | sk
  · -- whole-group unit
    have hUS := (groupUnitsOf G S).noskip_units hsk u hmem
    obtain ⟨a0, ha0⟩ := exists_groupJoint_eq hSm
    have ha0' : groupJoint G S Mk = some a0 := (groupJoint_of_not_marked hnm).trans ha0
    have ha0S := (groupJoint_kind ha0).1
    have ha0u : a0 ∈ u.atoms := hUS ▸ ha0S
    obtain ⟨p, hp, hspec⟩ := hingeOrigPair_specMk (Mk := Mk) ha0' ⟨u, hmem, ha0u⟩
    obtain ⟨u', hu', hau', j, hj, hT, hn1, hn2, hrel⟩ := hspec
    have huu : u' = u := by
      have hu'b : u' ∈ unitBlocks G σ Mk :=
        mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hnm).symm ▸ hu'⟩
      exact unit_eq_of_memMk (Mk := Mk) hM σ hu'b hu hau' ha0u
    subst huu
    obtain ⟨-, hjw⟩ := hrel.2 hsk
    have hat : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a0 = v := pi_of_crown hM σ hu hcr ha0u
    obtain ⟨y1, y2, hy1, hy2, hP⟩ := ext_lift_dartsMk (Mk := Mk) hM σ hu hcr
      (by rcases hjw with rfl | rfl; exact u'.isBlock.2.1; exact u'.isBlock.2.2.1) hjw
      hT.1 hT.2.1 hn1 hn2 hT.2.2.2
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_existsMk (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hP.1⟩
    refine ⟨q, ?_, ?_, ?_⟩
    · unfold groupAtom; rw [ha0']; simp [hat]
    · unfold hingeEntryPair; rw [hp]; exact hq
    · exact properPair_congrMk hP (by rw [hq1, hy1]) (by rw [hq2, hy2]) hqT
  · -- a skipped vine: the hinge is a joint of the object of the group
    exfalso
    apply hno
    obtain ⟨O, hex, hOm⟩ := objOf_isSomeMk hM σ hSm hσ (Or.inr ⟨sk, hsk⟩) hnm
    obtain ⟨-, -, -, hOspec⟩ := objOf_specMk (Option.mem_def.mpr hex)
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
        exact Or.inl (hup.trans (pi_of_crown hM σ hu hcr hxu))
      · have hxu : sk.y ∈ u.atoms := by
          rcases hr with ⟨h2, _⟩ | ⟨_, h2⟩
          · rw [← h2]; exact u.isBlock.2.1
          · rw [← h2]; exact u.isBlock.2.2.1
        exact Or.inr (hlo.trans (pi_of_crown hM σ hu hcr hxu))

/-- **Main's `hingePair_spec` at a hinge of an unmarked group** (the survivor branch of `hingePair` is void there). -/
theorem hingePair_specMk {S0 : Finset (GBranch G.tree)} (hS0 : S0 ∈ maximalGroups G.molecule)
    (hσ0 : σ S0 = Molecule.GapKind.SG) (hnm0 : ¬ markedGroup G Mk S0) {u0 : CLBlock G}
    (hu0 : u0 ∈ (groupUnitsOf G S0).units) {v : GBranch (stSt G σ Mk).G.tree}
    (hcr0 : (stSt G σ Mk).M.ob v = u0.upper) :
    ∃ x y, hingePair G σ v = some (x, y) ∧ ProperPair G σ v x y ∧
      (∃ S ∈ maximalGroups G.molecule, ¬ markedGroup G Mk S ∧ ∃ u ∈ (groupUnitsOf G S).units,
        (stSt G σ Mk).M.ob v = u.upper ∧
        ∃ p, HingeSpec G S u.upper p ∧ (stSt G σ Mk).M.od x = p.1 ∧ (stSt G σ Mk).M.od y = p.2) ∧
      ((¬ ∃ O ∈ objects G σ Mk, O.upper = v ∨ O.lower = v) →
        ∃ S ∈ maximalGroups G.molecule, groupAtom G σ S Mk = some v ∧ hingeEntryPair G σ S v = some (x, y)) := by
  classical
  have hu0' : u0 ∈ groupUnitsMk G Mk S0 := (groupUnitsMk_of_not_marked hnm0).symm ▸ hu0
  have hu0B : u0 ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S0, hS0, hσ0, hu0'⟩
  -- every unit with crown `v` belongs to `S0`
  have hgrp : ∀ S, S ∈ maximalGroups G.molecule → ∀ u ∈ groupUnitsMk G Mk S,
      (stSt G σ Mk).M.ob v = u.upper → S = S0 := by
    intro S hS u hu hcr
    by_contra hne
    exact Finset.disjoint_left.mp (groups_disjoint hM hS hS0 hne) (groupUnitsMk_sub hu u.isBlock.2.1)
      (hcr.symm.trans hcr0 ▸ groupUnitsMk_sub hu0' u0.isBlock.2.1)
  obtain ⟨q0, p0, hsp0, hq0, hP0⟩ := hinge_unit_pairMk hM σ hS0 hσ0 hnm0 hu0 hcr0
  unfold hingePair
  rw [dite_eq_right (not_survPairAt_of_unmarked hM σ hS0 hσ0 hnm0 hu0' hcr0)]
  by_cases h : ∃ p : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ∃ S ∈ maximalGroups G.molecule,
      groupAtom G σ S Mk = some v ∧ hingeEntryPair G σ S v = some p ∧ ProperPair G σ v p.1 p.2
  · rw [dite_eq_left h]
    obtain ⟨S, hS, hga, hep, hP⟩ := Classical.choose_spec h
    refine ⟨(Classical.choose h).1, (Classical.choose h).2, rfl, hP, ?_, ?_⟩
    · obtain ⟨a, ha, hav⟩ : ∃ a, groupJoint G S Mk = some a ∧ (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = v := by
        unfold groupAtom at hga
        cases hg : groupJoint G S Mk with
        | none => rw [hg] at hga; cases hga
        | some a => rw [hg] at hga; exact ⟨a, rfl, Option.some.inj hga⟩
      have hnmS := not_marked_of_groupJoint ha
      have ha' : groupJoint G S = some a := (groupJoint_of_not_marked hnmS).symm.trans ha
      obtain ⟨hσS, u, hu, hau⟩ := hinge_unitMk hM σ hS hnmS ha' (hav ▸ ((stSt G σ Mk).mem_hinges v).mpr
        (by rw [hcr0, stSt_cls_memMk (Mk := Mk) hM σ hu0B u0.isBlock.2.1]; simp))
      obtain ⟨p1, hp1, hs1⟩ := hingeOrigPair_specMk (Mk := Mk) ha ⟨u, hu, hau⟩
      unfold hingeEntryPair at hep
      rw [hp1] at hep
      simp only [Option.bind_some] at hep
      obtain ⟨hq1, hq2, -⟩ := liftPair_specMk hep
      obtain ⟨u1, hu1, hau1, j, hj, hrest⟩ := hs1
      have hu1B : u1 ∈ unitBlocks G σ Mk :=
        mem_unitBlocksMk.mpr ⟨S, hS, hσS, (groupUnitsMk_of_not_marked hnmS).symm ▸ hu1⟩
      refine ⟨S, hS, hnmS, u1, hu1, ?_, p1, ⟨u1, hu1, u1.isBlock.2.1, j, hj, hrest⟩, hq1, hq2⟩
      rw [← hav, (stSt G σ Mk).M.ob_pi, stSt_repC_memMk (Mk := Mk) hM σ hu1B hau1]
    · intro _
      exact ⟨S, hS, hga, hep⟩
  · rw [dite_eq_right h]
    have hno : ∃ O ∈ objects G σ Mk, O.upper = v ∨ O.lower = v := by
      by_contra hno
      obtain ⟨p, hga, hep, hP⟩ := hinge_entryMk hM σ hS0 hσ0 hnm0 hu0 hcr0 hno
      exact h ⟨p, S0, hS0, hga, hep, hP⟩
    have h2 : ∃ q : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G, ∃ S ∈ maximalGroups G.molecule,
        ∃ u ∈ groupUnitsMk G Mk S, (stSt G σ Mk).M.ob v = u.upper ∧
          ∃ p, (¬ markedGroup G Mk S → HingeSpec G S u.upper p) ∧ (markedGroup G Mk S → HingeSpecRun G u p) ∧
            liftPair G σ v p = some q ∧ ProperPair G σ v q.1 q.2 :=
      ⟨q0, S0, hS0, u0, hu0', hcr0, p0, fun _ => hsp0, fun hm => (hnm0 hm).elim, hq0, hP0⟩
    rw [dite_eq_left h2]
    obtain ⟨S2, hS2, u2, hu2, hob2, p2, hsp2, -, hq2, hP2⟩ := Classical.choose_spec h2
    obtain ⟨hl1, hl2, -⟩ := liftPair_specMk hq2
    have hSS := hgrp S2 hS2 u2 hu2 hob2
    subst hSS
    rw [groupUnitsMk_of_not_marked hnm0] at hu2
    exact ⟨(Classical.choose h2).1, (Classical.choose h2).2, rfl, hP2,
      ⟨S2, hS2, hnm0, u2, hu2, hob2, p2, hsp2 hnm0, hl1, hl2⟩, fun hno' => absurd hno hno'⟩

/-- **The hinge pair at a run hinge of a marked group** (o75 Theorem 7.5′(5), 75-F1): the pair of the first
survivor with a joint at the hinge, a pair of bonds of that survivor at its joint. -/
theorem hingePair_markedHinge {S : Finset (GBranch G.tree)} (hSm : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmk : markedGroup G Mk S) {u : CLBlock G} (hu : u ∈ groupUnitsMk G Mk S)
    {v : GBranch (stSt G σ Mk).G.tree} (hcr : (stSt G σ Mk).M.ob v = u.upper) :
    ∃ q, hingePair G σ v = some q ∧ TripleAt (stSt G σ Mk).G v q.1 q.2 ∧
      ∃ t, ∃ ht : t ∈ survivorsMk G σ Mk, (v = (survObj ht).upper ∨ v = (survObj ht).lower) ∧
        (survObj ht).ContainsDart q.1 ∧ (survObj ht).ContainsDart q.2 := by
  classical
  have huB : u ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S, hSm, hσ, hu⟩
  have hu' : u ∈ (markedUnitsOfMK hmk).runs := groupUnitsMk_of_markedMK hmk ▸ hu
  obtain ⟨t, ht, hj⟩ := run_survivor_joint hmk hu'
  have htm : t ∈ survivorsMk G σ Mk := mem_survivorsMk_iffMK.mpr ⟨S, hSm, hσ, hmk, ht⟩
  have hex : ∃ i, ∃ hi : i < (survivorsMk G σ Mk).length,
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.1 = v ∨
        (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.2 = v := by
    obtain ⟨i, hi, hti⟩ := List.getElem_of_mem htm
    refine ⟨i, hi, ?_⟩
    rw [hti]
    rcases hj with h | h
    · exact Or.inl (pi_of_crown hM σ huB hcr h)
    · exact Or.inr (pi_of_crown hM σ huB hcr h)
  obtain ⟨hi0, hv0⟩ := Nat.find_spec hex
  have hfirst : ∀ j (hj : j < Nat.find hex),
      ¬ ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.1 = v ∨
        (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.2 = v) :=
    fun j hj hc => Nat.find_min hex hj ⟨by omega, hc⟩
  obtain ⟨q, hq, hqT, h1, h2⟩ := hingePair_survFirst hM σ hi0 hv0 hfirst
  have ht0 : (survivorsMk G σ Mk)[Nat.find hex] ∈ survivorsMk G σ Mk := List.getElem_mem hi0
  obtain ⟨-, hup, hlo, -⟩ := survObj_spec ht0
  refine ⟨q, hq, hqT, _, ht0, ?_, survObj_containsDart hM σ ht0 h1, survObj_containsDart hM σ ht0 h2⟩
  rw [hup, hlo]
  exact hv0.imp Eq.symm Eq.symm

end main

end WaveTurbulence.VineA.NormalizedSplice
