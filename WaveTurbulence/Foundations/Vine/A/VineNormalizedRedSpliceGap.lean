/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
import Mathlib.Tactic

/-!
R83 successor copy of pinned/r83-RedSpliceGap.lean (original SHA in COPIED-SHA256SUMS).

# REDSPLICE-DEF (S2a): the gap specification of `G_sb` (TARGET L1956, L1963; the factor `Z`)

(R25) Each group `S` of `𝒞` carries one entry at its designated atom `π a` (`a = groupJoint G S`), of kind `σ S`.
The pair of darts of the entry is the lift to `G_sb` of a pair of darts of the ORIGINAL garden that was chosen once,
independently of `σ` (`RedSpliceDesig`):
* if `π a` is not a hinge: `intPairOrig G S`, a pair inside the designated object `designatedObject G S` at its joint;
* if `π a` is a hinge (`a` lies in a spliced unit): `hingeOrigPair G S`, a pair of the skipped vine at its joint, or the
  external pair at a degree-four joint of the whole-group unit.
`gapSpecification` is the resulting `Option`-valued function on the atoms of `G_sb`.  The theorems
`gapSpecification_group`, `gapSpecification_pair_of_object` and `gapSpecification_hinge_kind` show that every group has
its entry, of kind `σ S`, whose darts are (images of) the chosen original pair; hinge entries are SG.
The hinge pair `hingePair` of `collectionChoices` (the `C_1` data of subpro(5)) is separate and unchanged.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The internal pair at a non-hinge designated atom: the lift of `intPairOrig`. -/
@[expose] noncomputable def internalPair (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVine G)} (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) :=
  (intPairOrig G S Mk).bind (liftPair G σ v)

/-- The pair of darts of the entry of the group `S` at `v`. -/
@[expose] noncomputable def gapPair (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVine G)} (v : GBranch (stSt G σ Mk).G.tree) :
    Option (GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G) := by
  classical exact if v ∈ (stSt G σ Mk).hinges then hingeEntryPair G σ S v else internalPair G σ S v

/-- **The gap specification of `G_sb`** (the indicator `Z` of TARGET L1956, L1963), for the marked vine set `Mk`
(B1a).  B2c (ruling R171, o75 (2.3)): every survivor `t` of a marked group `S` has an entry at the image of its upper
joint (`MarkedEntryAt`), with the lift of the chosen pair of `t` there and the kind `σ S`. -/
@[expose] noncomputable def gapSpecificationMk (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G))
    (v : GBranch (stSt G σ Mk).G.tree) : Option (LocalGapSpecification (stSt G σ Mk).G v) := by
  classical
  exact if h : ∃ S ∈ maximalGroups G.molecule, groupAtom G σ S Mk = some v then
    (match gapPair G σ h.choose v with
      | some p => if hp : TripleAt (stSt G σ Mk).G v p.1 p.2 then
          some ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, σ h.choose⟩ else none
      | none => none)
  else if h' : ∃ St : Finset (GBranch G.tree) × (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      St.1 ∈ maximalGroups G.molecule ∧ MarkedEntryAt G σ St.1 St.2 v then
    (match markedEntryPair G σ h'.choose.2 v with
      | some p => if hp : TripleAt (stSt G σ Mk).G v p.1 p.2 then
          some ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, σ h'.choose.1⟩ else none
      | none => none)
  else none

/-- **The gap specification of `G_sb`** at the default marked set `∅` (main's).  B1a: the Mk-general function is
`gapSpecificationMk` (it is used unapplied in statements, so the default cannot be an argument here). -/
@[expose] noncomputable def gapSpecification (G : Garden w) (σ : Prescription G) :
    (v : GBranch (stSt G σ).G.tree) → Option (LocalGapSpecification (stSt G σ).G v) :=
  gapSpecificationMk G σ ∅

/-- The designated atoms of distinct groups differ. -/
theorem groupAtom_inj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S S' : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hS' : S' ∈ maximalGroups G.molecule)
    {v : GBranch (stSt G σ).G.tree} (h : groupAtom G σ S = some v) (h' : groupAtom G σ S' = some v) : S = S' := by
  by_contra hne
  obtain ⟨a, ha⟩ := exists_groupJoint_eq hS
  obtain ⟨a', ha'⟩ := exists_groupJoint_eq hS'
  have haS := (groupJoint_kind ha).1
  have haS' := (groupJoint_kind ha').1
  unfold groupAtom at h h'
  rw [ha] at h
  rw [ha'] at h'
  simp only [Option.map_some, Option.some.injEq] at h h'
  have e : repC (stSt G σ).cls a = repC (stSt G σ).cls a' := by
    rw [← (stSt G σ).M.ob_pi (stSt G σ).hcls a, ← (stSt G σ).M.ob_pi (stSt G σ).hcls a', h, h']
  exact Finset.disjoint_left.mp (groups_disjoint hM hS hS' hne) (repC_mem_group hM σ hS haS)
    (e ▸ repC_mem_group hM σ hS' haS')

/-- The entry of the group `S`, once its pair is known. -/
theorem gapSpecification_of (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) {v : GBranch (stSt G σ).G.tree} (hv : groupAtom G σ S = some v)
    {x y : GardenDart (stSt G σ).G} (hp : gapPair G σ S v = some (x, y))
    (hT : TripleAt (stSt G σ).G v x y) :
    gapSpecification G σ v = some ⟨x, y, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, σ S⟩ := by
  classical
  have h : ∃ S' ∈ maximalGroups G.molecule, groupAtom G σ S' = some v := ⟨S, hS, hv⟩
  have hc : h.choose = S := groupAtom_inj hM σ h.choose_spec.1 hS h.choose_spec.2 hv
  unfold gapSpecification gapSpecificationMk
  rw [dite_eq_left h]
  simp only [hc, hp, dite_eq_left hT]

/-- **Every group of `𝒞` has its entry in `gapSpecification`**, of kind `σ S`, whose darts are the lifts of the
chosen original pair: `intPairOrig` at a non-hinge joint, `hingeOrigPair` at a hinge. -/
theorem gapSpecification_group (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) :
    ∃ a, groupJoint G S = some a ∧ ∃ e : LocalGapSpecification (stSt G σ).G ((stSt G σ).M.pi (stSt G σ).hcls a),
      gapSpecification G σ ((stSt G σ).M.pi (stSt G σ).hcls a) = some e ∧ e.kind = σ S ∧
      ∃ p, (stSt G σ).M.od e.first = p.1 ∧ (stSt G σ).M.od e.second = p.2 ∧
        (((stSt G σ).M.pi (stSt G σ).hcls a ∈ (stSt G σ).hinges →
            hingeOrigPair G S = some p ∧ HingeSpec G S a p) ∧
          ((stSt G σ).M.pi (stSt G σ).hcls a ∉ (stSt G σ).hinges → intPairOrig G S = some p ∧ IntSpec G S p)) := by
  classical
  obtain ⟨a, ha⟩ := exists_groupJoint_eq hS
  have hatom : groupAtom G σ S = some ((stSt G σ).M.pi (stSt G σ).hcls a) := by
    unfold groupAtom; rw [ha]; rfl
  refine ⟨a, ha, ?_⟩
  by_cases hh : (stSt G σ).M.pi (stSt G σ).hcls a ∈ (stSt G σ).hinges
  · obtain ⟨hσ, u0, hu0, hau0⟩ := hinge_unit hM σ hS ha hh
    obtain ⟨p, hp, hsp⟩ := hingeOrigPair_spec ha ⟨u0, hu0, hau0⟩
    have hsp' := hsp
    unfold HingeSpec at hsp'
    obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩ := hsp'
    have huB : u ∈ unitBlocks G σ := mem_unitBlocks.mpr ⟨S, hS, hσ, hu⟩
    have hrepj : repC (stSt G σ).cls j = u.upper := stSt_repC_mem hM σ huB hj
    have hrepc : repC (stSt G σ).cls (G.molecule.atom p.1) = (stSt G σ).M.ob ((stSt G σ).M.pi (stSt G σ).hcls a) := by
      rw [(stSt G σ).M.ob_pi, stSt_repC_mem hM σ huB hau, hT.1, hrepj]
    have hrepc2 : repC (stSt G σ).cls (G.molecule.atom p.2) = (stSt G σ).M.ob ((stSt G σ).M.pi (stSt G σ).hcls a) := by
      rw [(stSt G σ).M.ob_pi, stSt_repC_mem hM σ huB hau, hT.2.1, hrepj]
    have hnint : ∀ d : GardenDart G, G.molecule.atom d = j → ¬ G.molecule.InGroup u.atoms d →
        ¬ ∃ a', (stSt G σ).cls (G.molecule.atom d) = some a' ∧
          (stSt G σ).cls (G.molecule.atom (G.molecule.mate d)) = some a' := by
      intro d hd hnd ⟨a', ha', ha''⟩
      rw [hd, stSt_cls_mem hM σ huB hj] at ha'
      have : a' = u.upper := (Option.some.inj ha').symm
      subst this
      exact hnd ⟨hd ▸ hj, mem_of_cls_eq hM σ huB ha''⟩
    obtain ⟨y1, y2, hy1, hy2, hT'⟩ := (stSt G σ).M.tripleAt_of_lift
      (c := (stSt G σ).M.pi (stSt G σ).hcls a) (d1 := p.1) (d2 := p.2) hrepc hrepc2
      (hnint p.1 hT.1 hn1) (hnint p.2 hT.2.1 hn2) hT.2.2.2 hT.2.2.1
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_exists (σ := σ)
      (v := (stSt G σ).M.pi (stSt G σ).hcls a) (p := p) ⟨(y1, y2), hy1, hy2, hT'⟩
    have hgp : gapPair G σ S ((stSt G σ).M.pi (stSt G σ).hcls a) = some q := by
      unfold gapPair; rw [ite_eq_left hh]; unfold hingeEntryPair; rw [hp, Option.bind_some]; exact hq
    refine ⟨_, gapSpecification_of hM σ hS hatom hgp hqT, rfl, p, hq1, hq2, ⟨fun _ => ⟨hp, u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩,
      fun h => absurd hh h⟩⟩
  · -- the joint is not merged
    have hcls : (stSt G σ).cls a = none := by
      have h1 := ((stSt G σ).mem_hinges ((stSt G σ).M.pi (stSt G σ).hcls a)).not.mp hh
      rw [not_not, (stSt G σ).M.ob_pi (stSt G σ).hcls] at h1
      rcases hc : (stSt G σ).cls a with _ | r
      · rfl
      · exfalso
        have hr : repC (stSt G σ).cls a = r := by simp [repC, hc]
        rw [hr] at h1
        rw [(stSt G σ).hcls a r hc] at h1
        cases h1
    have hrep : repC (stSt G σ).cls a = a := by simp [repC, hcls]
    obtain ⟨p, hp, hsp⟩ := intPairOrig_spec hS
    have hsp' := hsp
    unfold IntSpec at hsp'
    obtain ⟨a1, O, ha1, hO, hOj, hT0, hx0, hy0⟩ := hsp'
    rw [ha] at ha1
    cases ha1
    obtain ⟨y1, y2, hy1, hy2, hT⟩ := (stSt G σ).M.tripleAt_of_lift (c := (stSt G σ).M.pi (stSt G σ).hcls a)
      (d1 := p.1) (d2 := p.2) (by rw [hT0.1, (stSt G σ).M.ob_pi, hrep]) (by rw [hT0.2.1, (stSt G σ).M.ob_pi, hrep])
      (by rw [hT0.1, hcls]; simp) (by rw [hT0.2.1, hcls]; simp) hT0.2.2.2 hT0.2.2.1
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_exists (σ := σ)
      (v := (stSt G σ).M.pi (stSt G σ).hcls a) (p := p) ⟨(y1, y2), hy1, hy2, hT⟩
    have hgp : gapPair G σ S ((stSt G σ).M.pi (stSt G σ).hcls a) = some q := by
      unfold gapPair; rw [ite_eq_right hh]; unfold internalPair; rw [hp, Option.bind_some]; exact hq
    refine ⟨_, gapSpecification_of hM σ hS hatom hgp hqT, rfl, p, hq1, hq2, ⟨fun h => absurd h hh,
      fun _ => ⟨hp, a, O, ha, hO, hOj, hT0, hx0, hy0⟩⟩⟩

/-- **The bridge to the designated object.**  For each group the specified pair is, at a non-hinge joint, an internal
pair of the designated object (the images under `od` of its darts are darts of the object); at a hinge it is the
hinge pair `HingeSpec` of the original garden. -/
theorem gapSpecification_pair_of_object (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) :
    ∃ a O, groupJoint G S = some a ∧ designatedObject G S = some O ∧
      ∃ e : LocalGapSpecification (stSt G σ).G ((stSt G σ).M.pi (stSt G σ).hcls a),
        gapSpecification G σ ((stSt G σ).M.pi (stSt G σ).hcls a) = some e ∧ e.kind = σ S ∧
        (((stSt G σ).M.pi (stSt G σ).hcls a ∉ (stSt G σ).hinges →
          (a = O.upper ∨ a = O.lower) ∧ O.ContainsDart ((stSt G σ).M.od e.first) ∧
            O.ContainsDart ((stSt G σ).M.od e.second)) ∧
        ((stSt G σ).M.pi (stSt G σ).hcls a ∈ (stSt G σ).hinges →
          HingeSpec G S a ((stSt G σ).M.od e.first, (stSt G σ).M.od e.second))) := by
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecification_group hM σ hS
  obtain ⟨a', O, ha', hO, hd⟩ := designatedObject_spec hS
  rw [ha] at ha'
  cases ha'
  refine ⟨a, O, ha, hO, e, he, hk, fun h => ?_, fun h => ?_⟩
  · obtain ⟨hp, hsp⟩ := hnh.2 h
    unfold IntSpec at hsp
    obtain ⟨a1, O1, ha1, hO1, hOj, hT, hx, hy⟩ := hsp
    rw [ha] at ha1; cases ha1
    rw [hO] at hO1; cases hO1
    rw [h1, h2]
    exact ⟨hOj, hx, hy⟩
  · obtain ⟨hp, hsp⟩ := hnh.1 h
    rw [h1, h2]
    exact hsp

/-- B1b (Mk-general form of `gapSpecification_hinge_kind`). -/
theorem gapSpecification_hinge_kindMk (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) {a : GBranch G.tree} (haS : a ∈ S)
    {Mk : Set (Stage1.CLVine _)} (hh : (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls a ∈ (stSt (Mk := Mk) G σ).hinges) : σ S = Molecule.GapKind.SG := by
  have h1 := ((stSt (Mk := Mk) G σ).mem_hinges _).mp hh
  rw [(stSt (Mk := Mk) G σ).M.ob_pi] at h1
  by_cases h : ∃ u ∈ unitBlocks (Mk := Mk) G σ, a ∈ u.atoms
  · obtain ⟨u, hu, hau⟩ := h
    obtain ⟨S'', hS''m, hσ, hmem⟩ := (mem_unitBlocksMk (Mk := Mk)).mp hu
    have hsub := groupUnitsMk_sub hmem hau
    by_cases hSS : S = S''
    · rw [hSS]; exact hσ
    · exact absurd haS (Finset.disjoint_left.mp (groups_disjoint hM hS hS''m hSS) |> fun f => fun h => f h hsub)
  · push Not at h
    have : repC (stSt (Mk := Mk) G σ).cls a = a := stSt_repC_noneMk (Mk := Mk) hM σ h
    rw [this, stSt_cls_noneMk (Mk := Mk) hM σ h] at h1
    exact absurd rfl h1

/-- **Hinge entries are SG** (TARGET `subpro` (5): the triple at a hinge always has SG). -/
theorem gapSpecification_hinge_kind (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) {a : GBranch G.tree} (haS : a ∈ S)
    (hh : (stSt G σ).M.pi (stSt G σ).hcls a ∈ (stSt G σ).hinges) : σ S = Molecule.GapKind.SG := gapSpecification_hinge_kindMk (Mk := ∅) hM σ hS haS hh

end WaveTurbulence.VineA.NormalizedSplice
