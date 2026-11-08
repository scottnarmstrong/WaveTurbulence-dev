/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK2
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO (ruling R171): the gap entries of `gapSpecificationMk`

Mk-general versions (marked vine set `Mk`) of main's gap-entry lemmas:

* unmarked groups (`¬ markedGroup G Mk S`): `groupAtom_injMk`, `hinge_unitMk`, `gapSpecificationMk_of`,
  `gapSpecificationMk_group`, `gapSpecificationMk_indicator_iff` (main's `groupAtom_inj`, `hinge_unit`,
  `gapSpecification_of`, `gapSpecification_group`, `gapSpecification_indicator_iff`, whose proofs are followed);
* marked groups: `gapSpecificationMk_marked` (every survivor has an entry at the image of its upper joint, of kind
  `σ S`, with a lifted survivor pair) and `gapSpecificationMk_marked_indicator_iff`;
* `gapSpecificationMk_isSome`: every entry belongs to a group.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

theorem hingeOrigPair_of_not_marked {S : Finset (GBranch G.tree)} {Mk : Set (CLVine G)} (h : ¬ markedGroup G Mk S) :
    hingeOrigPair G S Mk = hingeOrigPair G S := by
  unfold hingeOrigPair
  rw [groupJoint_of_not_marked h]

theorem choose_eq_of_eq {α : Sort*} {p q : α → Prop} (hpq : p = q) (hp : ∃ x, p x) (hq : ∃ x, q x) :
    Classical.choose hp = Classical.choose hq := by
  subst hpq; rfl

theorem designatedObject_of_not_marked {S : Finset (GBranch G.tree)} {Mk : Set (CLVine G)}
    (h : ¬ markedGroup G Mk S) : designatedObject G S Mk = designatedObject G S := by
  classical
  unfold designatedObject
  by_cases h1 : ∃ a, groupJoint G S = some a ∧ ∃ O, IsDesig G S a O
  · have h0 : ∃ a, groupJoint G S Mk = some a ∧ ∃ O, IsDesig G S a O := by
      rw [groupJoint_of_not_marked h]; exact h1
    rw [dite_eq_left h0, dite_eq_left h1]
    have ha : h0.choose = h1.choose := by
      have e0 : groupJoint G S = some h0.choose := (groupJoint_of_not_marked h).symm.trans h0.choose_spec.1
      exact Option.some.inj (e0.symm.trans h1.choose_spec.1)
    exact congrArg some (choose_eq_of_eq (by rw [ha]) _ _)
  · have h0 : ¬ ∃ a, groupJoint G S Mk = some a ∧ ∃ O, IsDesig G S a O := by
      rw [groupJoint_of_not_marked h]; exact h1
    rw [dite_eq_right h0, dite_eq_right h1]

theorem intPairOrig_of_not_marked {S : Finset (GBranch G.tree)} {Mk : Set (CLVine G)} (h : ¬ markedGroup G Mk S) :
    intPairOrig G S Mk = intPairOrig G S := by
  classical
  have hspec : (fun p => IntSpec G S p Mk) = (fun p => IntSpec G S p) := by
    funext p
    unfold IntSpec
    rw [groupJoint_of_not_marked h, designatedObject_of_not_marked h]
  unfold intPairOrig
  by_cases h1 : ∃ p, IntSpec G S p
  · have h0 : ∃ p, IntSpec G S p Mk := by
      obtain ⟨p, hp⟩ := h1; exact ⟨p, (congrFun hspec p).mpr hp⟩
    rw [dite_eq_left h0, dite_eq_left h1]
    exact congrArg some (choose_eq_of_eq hspec _ _)
  · have h0 : ¬ ∃ p, IntSpec G S p Mk := fun ⟨p, hp⟩ => h1 ⟨p, (congrFun hspec p).mp hp⟩
    rw [dite_eq_right h0, dite_eq_right h1]

section main
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
include hM

/-- An atom carrying a group's designated atom lies, through `repC`, in the group. -/
theorem groupAtom_mem {T : Finset (GBranch G.tree)} {v : GBranch (stSt G σ Mk).G.tree}
    (hT : groupAtom G σ T Mk = some v) :
    ¬ markedGroup G Mk T ∧ ∃ a, groupJoint G T = some a ∧ a ∈ T ∧ (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = v := by
  unfold groupAtom at hT
  by_cases hm : markedGroup G Mk T
  · rw [groupJoint_of_marked hm] at hT; cases hT
  · rw [groupJoint_of_not_marked hm] at hT
    cases hg : groupJoint G T with
    | none => rw [hg] at hT; cases hT
    | some a =>
      rw [hg] at hT
      exact ⟨hm, a, rfl, (groupJoint_kind hg).1, Option.some.inj hT⟩

/-- A survivor carrying a marked entry is a survivor of a marked group, and its upper joint lies in the group. -/
theorem markedEntryAt_mem {T : Finset (GBranch G.tree)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} {v : GBranch (stSt G σ Mk).G.tree}
    (hT : MarkedEntryAt G σ T t v) :
    ∃ hmk : markedGroup G Mk T, t ∈ (markedUnitsOfMK hmk).surv ∧ t.2.1 ∈ T := by
  obtain ⟨ht, -⟩ := hT
  by_cases hm : markedGroup G Mk T
  · rw [groupSurvMk_of_marked hm (exists_markedGroupUnits hm)] at ht
    obtain ⟨⟨X, hX⟩, hI, -⟩ := (markedUnitsOfMK hm).surv_spec t ht
    exact ⟨hm, ht, isIngredient_subset hI hX.1.2.1⟩
  · rw [groupSurvMk_of_not_marked hm] at ht; cases ht

theorem repC_eq_of_pi_eq {a a' : GBranch G.tree}
    (h : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a') :
    repC (stSt G σ Mk).cls a = repC (stSt G σ Mk).cls a' := by
  rw [← (stSt G σ Mk).M.ob_pi (stSt G σ Mk).hcls a, ← (stSt G σ Mk).M.ob_pi (stSt G σ Mk).hcls a', h]

/-- Atoms of `G_sb` that are images of atoms of two groups determine the group. -/
theorem group_eq_of_pi_eq {S S' : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hS' : S' ∈ maximalGroups G.molecule) {a a' : GBranch G.tree} (ha : a ∈ S) (ha' : a' ∈ S')
    (h : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a') : S = S' := by
  by_contra hne
  have e := repC_eq_of_pi_eq hM σ h
  exact Finset.disjoint_left.mp (groups_disjoint hM hS hS' hne) (repC_mem_groupMk hM σ hS ha)
    (e ▸ repC_mem_groupMk hM σ hS' ha')

theorem groupAtom_injMk {S S' : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hS' : S' ∈ maximalGroups G.molecule) {v : GBranch (stSt G σ Mk).G.tree}
    (h : groupAtom G σ S Mk = some v) (h' : groupAtom G σ S' Mk = some v) : S = S' := by
  obtain ⟨-, a, -, haS, hav⟩ := groupAtom_mem hM σ h
  obtain ⟨-, a', -, haS', hav'⟩ := groupAtom_mem hM σ h'
  exact group_eq_of_pi_eq hM σ hS hS' haS haS' (hav.trans hav'.symm)

theorem markedEntryAt_group_eq {S S' : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hS' : S' ∈ maximalGroups G.molecule) {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    {v : GBranch (stSt G σ Mk).G.tree} (h : MarkedEntryAt G σ S t v) (h' : MarkedEntryAt G σ S' t' v) : S = S' := by
  obtain ⟨-, -, htS⟩ := markedEntryAt_mem hM σ h
  obtain ⟨-, -, htS'⟩ := markedEntryAt_mem hM σ h'
  exact group_eq_of_pi_eq hM σ hS hS' htS htS' (h.2.trans h'.2.symm)

theorem not_groupAtom_of_markedEntryAt {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} {v : GBranch (stSt G σ Mk).G.tree}
    (h : MarkedEntryAt G σ S t v) :
    ¬ ∃ S' ∈ maximalGroups G.molecule, groupAtom G σ S' Mk = some v := by
  rintro ⟨S', hS', h'⟩
  obtain ⟨hmk, -, htS⟩ := markedEntryAt_mem hM σ h
  obtain ⟨hnm, a, -, haS, hav⟩ := groupAtom_mem hM σ h'
  have hSS := group_eq_of_pi_eq hM σ hS hS' htS haS (h.2.trans hav.symm)
  subst hSS
  exact hnm hmk

/-- Main's `hinge_unit` for an unmarked group. -/
theorem hinge_unitMk {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (hnm : ¬ markedGroup G Mk S)
    {a : GBranch G.tree} (ha : groupJoint G S = some a)
    (hh : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∈ (stSt G σ Mk).hinges) :
    σ S = Molecule.GapKind.SG ∧ ∃ u ∈ (groupUnitsOf G S).units, a ∈ u.atoms := by
  have haS := (groupJoint_kind ha).1
  have h1 := ((stSt G σ Mk).mem_hinges _).mp hh
  rw [(stSt G σ Mk).M.ob_pi] at h1
  by_cases h : ∃ u ∈ unitBlocks G σ Mk, a ∈ u.atoms
  · obtain ⟨u, hu, hau⟩ := h
    obtain ⟨S'', hS''m, hσ, hmem⟩ := (mem_unitBlocksMk (Mk := Mk)).mp hu
    have hsub := groupUnitsMk_sub hmem hau
    by_cases hSS : S = S''
    · subst hSS
      rw [groupUnitsMk_of_not_marked hnm] at hmem
      exact ⟨hσ, u, hmem, hau⟩
    · exact absurd haS (fun h => Finset.disjoint_left.mp (groups_disjoint hM hS hS''m hSS) h hsub)
  · push Not at h
    have : repC (stSt G σ Mk).cls a = a := stSt_repC_noneMk hM σ h
    rw [this, stSt_cls_noneMk hM σ Mk h] at h1
    exact absurd rfl h1

/-- Main's `gapSpecification_of` with `Mk`. -/
theorem gapSpecificationMk_of {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    {v : GBranch (stSt G σ Mk).G.tree} (hv : groupAtom G σ S Mk = some v)
    {x y : GardenDart (stSt G σ Mk).G} (hp : gapPair G σ S v = some (x, y))
    (hT : TripleAt (stSt G σ Mk).G v x y) :
    gapSpecificationMk G σ Mk v = some ⟨x, y, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, σ S⟩ := by
  classical
  have h : ∃ S' ∈ maximalGroups G.molecule, groupAtom G σ S' Mk = some v := ⟨S, hS, hv⟩
  have hc : h.choose = S := groupAtom_injMk hM σ h.choose_spec.1 hS h.choose_spec.2 hv
  unfold gapSpecificationMk
  rw [dite_eq_left h]
  simp only [hc, hp, dite_eq_left hT]

/-- **Main's `gapSpecification_group` for an unmarked group.** -/
theorem gapSpecificationMk_group {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hnm : ¬ markedGroup G Mk S) :
    ∃ a, groupJoint G S = some a ∧
      ∃ e : LocalGapSpecification (stSt G σ Mk).G ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a),
      gapSpecificationMk G σ Mk ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) = some e ∧ e.kind = σ S ∧
      ∃ p, (stSt G σ Mk).M.od e.first = p.1 ∧ (stSt G σ Mk).M.od e.second = p.2 ∧
        (((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∈ (stSt G σ Mk).hinges →
            hingeOrigPair G S = some p ∧ HingeSpec G S a p) ∧
          ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∉ (stSt G σ Mk).hinges →
            intPairOrig G S = some p ∧ IntSpec G S p)) := by
  classical
  obtain ⟨a, ha⟩ := exists_groupJoint_eq hS
  have hatom : groupAtom G σ S Mk = some ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) := by
    unfold groupAtom; rw [groupJoint_of_not_marked hnm, ha]; rfl
  refine ⟨a, ha, ?_⟩
  by_cases hh : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∈ (stSt G σ Mk).hinges
  · obtain ⟨hσ, u0, hu0, hau0⟩ := hinge_unitMk hM σ hS hnm ha hh
    obtain ⟨p, hp, hsp⟩ := hingeOrigPair_spec ha ⟨u0, hu0, hau0⟩
    have hsp' := hsp
    unfold HingeSpec at hsp'
    obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, -⟩ := hsp'
    have huB : u ∈ unitBlocks G σ Mk :=
      (mem_unitBlocksMk (Mk := Mk)).mpr ⟨S, hS, hσ, by rw [groupUnitsMk_of_not_marked hnm]; exact hu⟩
    have hrepj : repC (stSt G σ Mk).cls j = u.upper := stSt_repC_memMk hM σ huB hj
    have hrepc : repC (stSt G σ Mk).cls (G.molecule.atom p.1) =
        (stSt G σ Mk).M.ob ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) := by
      rw [(stSt G σ Mk).M.ob_pi, stSt_repC_memMk hM σ huB hau, hT.1, hrepj]
    have hrepc2 : repC (stSt G σ Mk).cls (G.molecule.atom p.2) =
        (stSt G σ Mk).M.ob ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) := by
      rw [(stSt G σ Mk).M.ob_pi, stSt_repC_memMk hM σ huB hau, hT.2.1, hrepj]
    have hnint : ∀ d : GardenDart G, G.molecule.atom d = j → ¬ G.molecule.InGroup u.atoms d →
        ¬ ∃ a', (stSt G σ Mk).cls (G.molecule.atom d) = some a' ∧
          (stSt G σ Mk).cls (G.molecule.atom (G.molecule.mate d)) = some a' := by
      intro d hd hnd ⟨a', ha', ha''⟩
      rw [hd, stSt_cls_memMk hM σ Mk huB hj] at ha'
      have : a' = u.upper := (Option.some.inj ha').symm
      subst this
      exact hnd ⟨hd ▸ hj, mem_of_cls_eqMk hM σ huB ha''⟩
    obtain ⟨y1, y2, hy1, hy2, hT'⟩ := (stSt G σ Mk).M.tripleAt_of_lift
      (c := (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) (d1 := p.1) (d2 := p.2) hrepc hrepc2
      (hnint p.1 hT.1 hn1) (hnint p.2 hT.2.1 hn2) hT.2.2.2 hT.2.2.1
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_existsMk (σ := σ)
      (v := (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) (p := p) ⟨(y1, y2), hy1, hy2, hT'⟩
    have hgp : gapPair G σ S ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) = some q := by
      unfold gapPair; rw [ite_eq_left hh]; unfold hingeEntryPair
      rw [hingeOrigPair_of_not_marked hnm, hp, Option.bind_some]; exact hq
    exact ⟨_, gapSpecificationMk_of hM σ hS hatom hgp hqT, rfl, p, hq1, hq2, ⟨fun _ => ⟨hp, hsp⟩,
      fun h => absurd hh h⟩⟩
  · have hcls : (stSt G σ Mk).cls a = none := by
      have h1 := ((stSt G σ Mk).mem_hinges ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a)).not.mp hh
      rw [not_not, (stSt G σ Mk).M.ob_pi (stSt G σ Mk).hcls] at h1
      rcases hc : (stSt G σ Mk).cls a with _ | r
      · rfl
      · exfalso
        have hr : repC (stSt G σ Mk).cls a = r := by simp [repC, hc]
        rw [hr] at h1
        rw [(stSt G σ Mk).hcls a r hc] at h1
        cases h1
    have hrep : repC (stSt G σ Mk).cls a = a := by simp [repC, hcls]
    obtain ⟨p, hp, hsp⟩ := intPairOrig_spec hS
    have hsp' := hsp
    unfold IntSpec at hsp'
    obtain ⟨a1, O, ha1, hO, hOj, hT0, hx0, hy0⟩ := hsp'
    rw [ha] at ha1
    cases ha1
    obtain ⟨y1, y2, hy1, hy2, hT⟩ := (stSt G σ Mk).M.tripleAt_of_lift
      (c := (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) (d1 := p.1) (d2 := p.2)
      (by rw [hT0.1, (stSt G σ Mk).M.ob_pi, hrep]) (by rw [hT0.2.1, (stSt G σ Mk).M.ob_pi, hrep])
      (by rw [hT0.1, hcls]; simp) (by rw [hT0.2.1, hcls]; simp) hT0.2.2.2 hT0.2.2.1
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_existsMk (σ := σ)
      (v := (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) (p := p) ⟨(y1, y2), hy1, hy2, hT⟩
    have hgp : gapPair G σ S ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) = some q := by
      unfold gapPair; rw [ite_eq_right hh]; unfold internalPair
      rw [intPairOrig_of_not_marked hnm, hp, Option.bind_some]; exact hq
    exact ⟨_, gapSpecificationMk_of hM σ hS hatom hgp hqT, rfl, p, hq1, hq2, ⟨fun h => absurd h hh,
      fun _ => ⟨hp, hsp⟩⟩⟩

/-- **Main's `gapSpecification_indicator_iff` for an unmarked group.** -/
theorem gapSpecificationMk_indicator_iff {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hnm : ¬ markedGroup G Mk S) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (κsb : GardenDart (stSt G σ Mk).G → (Fin d → ℤ)) (hlab : ∀ y, κsb y = κ ((stSt G σ Mk).M.od y)) :
    ∃ a O, groupJoint G S = some a ∧ designatedObject G S = some O ∧
      ∃ e : LocalGapSpecification (stSt G σ Mk).G ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a),
        gapSpecificationMk G σ Mk ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) = some e ∧
        ∀ k, O.HasGapKind L γ η w κ k →
          (Molecule.gapKind L γ η ((w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second))) = e.kind
            ↔ k = σ S) := by
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecificationMk_group hM σ hS hnm
  obtain ⟨a', O, ha', hO, hd⟩ := designatedObject_spec hS
  rw [ha] at ha'
  cases ha'
  refine ⟨a, O, ha, hO, e, he, fun k hOk => ?_⟩
  have hgap : (w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second)) =
      Molecule.gapAt L w κ p.1 p.2 := by
    simp only [Molecule.gapAt, Molecule.kvec, hlab, h1, h2]
  rw [hgap, hk]
  have hkind : Molecule.gapKind L γ η (Molecule.gapAt L w κ p.1 p.2) = k := by
    by_cases hh : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∈ (stSt G σ Mk).hinges
    · obtain ⟨_, hsp⟩ := hnh.1 hh
      exact hingeOrig_gapKind hM L γ η w c κ hκ hc0 hsp hd hOk
    · obtain ⟨hp, hsp⟩ := hnh.2 hh
      unfold IntSpec at hsp
      obtain ⟨a1, O1, ha1, hO1, hOj, hT, hx, hy⟩ := hsp
      rw [hO] at hO1; cases hO1
      rw [ha] at ha1; cases ha1
      exact obj_pair_gapKind G.molecule hM L γ η w c κ hκ hc0 O hOk hOj hT.1 hT.2.1 hx hy hT.2.2.2
  rw [hkind]

/-- **The gap entry of a survivor** (ruling R171, o75 (2.3)): every survivor `t` of a marked group `S` has an entry
at the image of its upper joint, of kind `σ S`, whose darts are the lifts of a pair of a survivor `t'` of `S` at its
upper joint, with the same image. -/
theorem gapSpecificationMk_marked {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hmk : markedGroup G Mk S) {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ (markedUnitsOfMK hmk).surv) :
    ∃ t' p, t' ∈ (markedUnitsOfMK hmk).surv ∧
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t'.2.1 = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 ∧
      SurvPairSpec G t'.1 t'.2.1 p ∧
      ∃ e : LocalGapSpecification (stSt G σ Mk).G ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1),
        gapSpecificationMk G σ Mk ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) = some e ∧ e.kind = σ S ∧
        (stSt G σ Mk).M.od e.first = p.1 ∧ (stSt G σ Mk).M.od e.second = p.2 := by
  classical
  have hg : groupSurvMk G Mk S = (markedUnitsOfMK hmk).surv :=
    groupSurvMk_of_marked hmk (exists_markedGroupUnits hmk)
  have hEt : MarkedEntryAt G σ S t ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) := ⟨by rw [hg]; exact ht, rfl⟩
  have h' : ∃ St : Finset (GBranch G.tree) × (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      St.1 ∈ maximalGroups G.molecule ∧
        MarkedEntryAt G σ St.1 St.2 ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) := ⟨(S, t), hS, hEt⟩
  obtain ⟨hS1, hE1⟩ := h'.choose_spec
  have hc : h'.choose.1 = S := markedEntryAt_group_eq hM σ hS1 hS hE1 hEt
  have ht' : h'.choose.2 ∈ (markedUnitsOfMK hmk).surv := by
    have := hE1.1
    rw [hc, hg] at this
    exact this
  obtain ⟨hvine, -, -⟩ := (markedUnitsOfMK hmk).surv_spec _ ht'
  obtain ⟨p, hp, hsp⟩ := survOrigPair_isSome (exists_survPairSpec hvine)
  have hv := hE1.2
  obtain ⟨⟨hpx, hpy, hpne, hpout⟩, hgx, hgy⟩ := hsp
  have hrep : ∀ z : GardenDart G, G.molecule.atom z = h'.choose.2.2.1 →
      repC (stSt G σ Mk).cls (G.molecule.atom z) =
        (stSt G σ Mk).M.ob ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) := by
    intro z hz
    rw [hz]
    exact ((stSt G σ Mk).M.ob_pi (stSt G σ Mk).hcls _).symm.trans (congrArg _ hv)
  obtain ⟨y1, y2, hy1, hy2, hT'⟩ := (stSt G σ Mk).M.tripleAt_of_lift
    (c := (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) (d1 := p.1) (d2 := p.2)
    (hrep p.1 hpx) (hrep p.2 hpy) (survDart_not_internal hM σ hS hmk ht' hgx (Or.inl hpx))
    (survDart_not_internal hM σ hS hmk ht' hgy (Or.inl hpy)) hpout hpne
  obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_existsMk (σ := σ)
    (v := (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) (p := p) ⟨(y1, y2), hy1, hy2, hT'⟩
  have hmep : markedEntryPair G σ h'.choose.2 ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) = some q := by
    unfold markedEntryPair; rw [hp, Option.bind_some]; exact hq
  have hno := not_groupAtom_of_markedEntryAt hM σ hS hEt
  refine ⟨h'.choose.2, p, ht', hv, ⟨⟨hpx, hpy, hpne, hpout⟩, hgx, hgy⟩,
    ⟨q.1, q.2, hqT.1, hqT.2.1, hqT.2.2.1, hqT.2.2.2, σ S⟩, ?_, rfl, hq1, hq2⟩
  unfold gapSpecificationMk
  rw [dite_eq_right hno, dite_eq_left h']
  simp only [hmep, hc, dite_eq_left hqT]

/-- **The indicator factor of a survivor**: the gap kind of its specified pair equals the kind of the entry exactly
when the designated object of the group has the prescribed kind `σ S`. -/
theorem gapSpecificationMk_marked_indicator_iff {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hmk : markedGroup G Mk S) {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ (markedUnitsOfMK hmk).surv) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (κsb : GardenDart (stSt G σ Mk).G → (Fin d → ℤ)) (hlab : ∀ y, κsb y = κ ((stSt G σ Mk).M.od y)) :
    ∃ O, designatedObject G S = some O ∧
      ∃ e : LocalGapSpecification (stSt G σ Mk).G ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1),
        gapSpecificationMk G σ Mk ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1) = some e ∧
        ∀ k, O.HasGapKind L γ η w κ k →
          (Molecule.gapKind L γ η ((w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second))) = e.kind
            ↔ k = σ S) := by
  obtain ⟨t', p, ht', -, hsp, e, he, hk, h1, h2⟩ := gapSpecificationMk_marked hM σ hS hmk ht
  obtain ⟨a', O, -, hO, -⟩ := designatedObject_spec hS
  obtain ⟨hvine, hI, -⟩ := (markedUnitsOfMK hmk).surv_spec t' ht'
  refine ⟨O, hO, e, he, fun k hOk => ?_⟩
  have hgap : (w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second)) =
      Molecule.gapAt L w κ p.1 p.2 := by
    simp only [Molecule.gapAt, Molecule.kvec, hlab, h1, h2]
  rw [hgap, hk, ingredient_pair_gapKind hM L γ η w c κ hκ hc0 hS hI hvine hsp hO hOk]

/-- Every entry of `gapSpecificationMk` belongs to a group: an unmarked group's designated atom or the upper joint of
a survivor. -/
theorem gapSpecificationMk_isSome {v : GBranch (stSt G σ Mk).G.tree} (h : (gapSpecificationMk G σ Mk v).isSome) :
    (∃ S ∈ maximalGroups G.molecule, groupAtom G σ S Mk = some v) ∨
      ∃ S t, S ∈ maximalGroups G.molecule ∧ MarkedEntryAt G σ S t v := by
  classical
  by_contra hne
  push Not at hne
  unfold gapSpecificationMk at h
  rw [dite_eq_right (fun ⟨S, hS, h1⟩ => hne.1 S hS h1),
    dite_eq_right (fun ⟨St, hS, h1⟩ => hne.2 St.1 St.2 hS h1)] at h
  simp at h

end main

end WaveTurbulence.VineA.NormalizedSplice
