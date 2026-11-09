/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceGap` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGap


/-!
# REDSPLICE-DEF (S2a): the gap specification of `G_sb` (TARGET L1956, L1963; the factor `Z`)

(R25) Each group `S` of `𝒞` carries one entry at its designated atom `π a` (`a = groupJoint γ G S`), of kind `σ S`.
The pair of darts of the entry is the lift to `G_sb` of a pair of darts of the ORIGINAL garden that was chosen once,
independently of `σ` (`RedSpliceDesig`):
* if `π a` is not a hinge: `intPairOrig γ G S`, a pair inside the designated object `designatedObject γ G S` at its joint;
* if `π a` is a hinge (`a` lies in a spliced unit): `hingeOrigPair γ G S`, a pair of the skipped vine at its joint, or the
  external pair at a degree-four joint of the whole-group unit.
`gapSpecification` is the resulting `Option`-valued function on the atoms of `G_sb`.  The theorems
`gapSpecification_group`, `gapSpecification_pair_of_object` and `gapSpecification_hinge_kind` show that every group has
its entry, of kind `σ S`, whose darts are (images of) the chosen original pair; hinge entries are SG.
The hinge pair `hingePair` of `collectionChoices` (the `C_1` data of subpro(5)) is separate and unchanged.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The internal pair at a non-hinge designated atom: the lift of `intPairOrig`. -/
@[expose] noncomputable def internalPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVineG γ G)} (v : GBranch (stSt γ G σ Mk).G.tree) :
    Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) :=
  (intPairOrig γ G S Mk).bind (liftPair γ G σ v)

/-- The pair of darts of the entry of the group `S` at `v`. -/
@[expose] noncomputable def gapPair (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    {Mk : Set (CLVineG γ G)} (v : GBranch (stSt γ G σ Mk).G.tree) :
    Option (GardenDart (stSt γ G σ Mk).G × GardenDart (stSt γ G σ Mk).G) := by
  classical exact if v ∈ (stSt γ G σ Mk).hinges then hingeEntryPair γ G σ S v else internalPair γ G σ S v

/-- **The gap specification of `G_sb`** (the indicator `Z` of TARGET L1956, L1963), for the marked vine set `Mk`
(B1a).  B2c (ruling R171, o75 (2.3)): every survivor `t` of a marked group `S` has an entry at the image of its upper
joint (`MarkedEntryAt`), with the lift of the chosen pair of `t` there and the kind `σ S`. -/
@[expose] noncomputable def gapSpecificationMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G))
    (v : GBranch (stSt γ G σ Mk).G.tree) : Option (LocalGapSpecification (stSt γ G σ Mk).G v) := by
  classical
  exact if h : ∃ S ∈ maximalGroupsG γ G.molecule, groupAtom γ G σ S Mk = some v then
    (match gapPair γ G σ h.choose v with
      | some p => if hp : TripleAt (stSt γ G σ Mk).G v p.1 p.2 then
          some ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, σ h.choose⟩ else none
      | none => none)
  else if h' : ∃ St : Finset (GBranch G.tree) × (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      St.1 ∈ maximalGroupsG γ G.molecule ∧ MarkedEntryAt γ G σ St.1 St.2 v then
    (match markedEntryPair γ G σ h'.choose.2 v with
      | some p => if hp : TripleAt (stSt γ G σ Mk).G v p.1 p.2 then
          some ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, σ h'.choose.1⟩ else none
      | none => none)
  else none

/-- **The gap specification of `G_sb`** at the default marked set `∅` (main's).  B1a: the Mk-general function is
`gapSpecificationMk` (it is used unapplied in statements, so the default cannot be an argument here). -/
@[expose] noncomputable def gapSpecification (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) :
    (v : GBranch (stSt γ G σ).G.tree) → Option (LocalGapSpecification (stSt γ G σ).G v) :=
  gapSpecificationMk γ G σ ∅

/-- The designated atoms of distinct groups differ. -/
theorem groupAtom_inj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S S' : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroupsG γ G.molecule) (hS' : S' ∈ maximalGroupsG γ G.molecule)
    {v : GBranch (stSt γ G σ).G.tree} (h : groupAtom γ G σ S = some v) (h' : groupAtom γ G σ S' = some v) : S = S' := by
  by_contra hne
  obtain ⟨a, ha⟩ := exists_groupJoint_eq hS
  obtain ⟨a', ha'⟩ := exists_groupJoint_eq hS'
  have haS := (groupJoint_kind ha).1
  have haS' := (groupJoint_kind ha').1
  unfold groupAtom at h h'
  rw [ha] at h
  rw [ha'] at h'
  simp only [Option.map_some, Option.some.injEq] at h h'
  have e : repC (stSt γ G σ).cls a = repC (stSt γ G σ).cls a' := by
    rw [← (stSt γ G σ).M.ob_pi (stSt γ G σ).hcls a, ← (stSt γ G σ).M.ob_pi (stSt γ G σ).hcls a', h, h']
  exact Finset.disjoint_left.mp (groups_disjoint hM hS hS' hne) (repC_mem_group hM σ hS haS)
    (e ▸ repC_mem_group hM σ hS' haS')

/-- The entry of the group `S`, once its pair is known. -/
theorem gapSpecification_of (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroupsG γ G.molecule) {v : GBranch (stSt γ G σ).G.tree} (hv : groupAtom γ G σ S = some v)
    {x y : GardenDart (stSt γ G σ).G} (hp : gapPair γ G σ S v = some (x, y))
    (hT : TripleAt (stSt γ G σ).G v x y) :
    gapSpecification γ G σ v = some ⟨x, y, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, σ S⟩ := by
  classical
  have h : ∃ S' ∈ maximalGroupsG γ G.molecule, groupAtom γ G σ S' = some v := ⟨S, hS, hv⟩
  have hc : h.choose = S := groupAtom_inj hM σ h.choose_spec.1 hS h.choose_spec.2 hv
  unfold gapSpecification gapSpecificationMk
  rw [dif_pos h]
  simp only [hc, hp, dif_pos hT]

/-- **Every group of `𝒞` has its entry in `gapSpecification`**, of kind `σ S`, whose darts are the lifts of the
chosen original pair: `intPairOrig` at a non-hinge joint, `hingeOrigPair` at a hinge. -/
theorem gapSpecification_group (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroupsG γ G.molecule) :
    ∃ a, groupJoint γ G S = some a ∧ ∃ e : LocalGapSpecification (stSt γ G σ).G ((stSt γ G σ).M.pi (stSt γ G σ).hcls a),
      gapSpecification γ G σ ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) = some e ∧ e.kind = σ S ∧
      ∃ p, (stSt γ G σ).M.od e.first = p.1 ∧ (stSt γ G σ).M.od e.second = p.2 ∧
        (((stSt γ G σ).M.pi (stSt γ G σ).hcls a ∈ (stSt γ G σ).hinges →
            hingeOrigPair γ G S = some p ∧ HingeSpec γ G S a p) ∧
          ((stSt γ G σ).M.pi (stSt γ G σ).hcls a ∉ (stSt γ G σ).hinges → intPairOrig γ G S = some p ∧ IntSpec γ G S p)) := by
  classical
  obtain ⟨a, ha⟩ := exists_groupJoint_eq hS
  have hatom : groupAtom γ G σ S = some ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) := by
    unfold groupAtom; rw [ha]; rfl
  refine ⟨a, ha, ?_⟩
  by_cases hh : (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∈ (stSt γ G σ).hinges
  · obtain ⟨hσ, u0, hu0, hau0⟩ := hinge_unit hM σ hS ha hh
    obtain ⟨p, hp, hsp⟩ := hingeOrigPair_spec ha ⟨u0, hu0, hau0⟩
    have hsp' := hsp
    unfold HingeSpec at hsp'
    obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩ := hsp'
    have huB : u ∈ unitBlocks γ G σ := mem_unitBlocks.mpr ⟨S, hS, hσ, hu⟩
    have hrepj : repC (stSt γ G σ).cls j = u.upper := stSt_repC_mem hM σ huB hj
    have hrepc : repC (stSt γ G σ).cls (G.molecule.atom p.1) = (stSt γ G σ).M.ob ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) := by
      rw [(stSt γ G σ).M.ob_pi, stSt_repC_mem hM σ huB hau, hT.1, hrepj]
    have hrepc2 : repC (stSt γ G σ).cls (G.molecule.atom p.2) = (stSt γ G σ).M.ob ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) := by
      rw [(stSt γ G σ).M.ob_pi, stSt_repC_mem hM σ huB hau, hT.2.1, hrepj]
    have hnint : ∀ d : GardenDart G, G.molecule.atom d = j → ¬ G.molecule.InGroup u.atoms d →
        ¬ ∃ a', (stSt γ G σ).cls (G.molecule.atom d) = some a' ∧
          (stSt γ G σ).cls (G.molecule.atom (G.molecule.mate d)) = some a' := by
      intro d hd hnd ⟨a', ha', ha''⟩
      rw [hd, stSt_cls_mem hM σ huB hj] at ha'
      have : a' = u.upper := (Option.some.inj ha').symm
      subst this
      exact hnd ⟨hd ▸ hj, mem_of_cls_eq hM σ huB ha''⟩
    obtain ⟨y1, y2, hy1, hy2, hT'⟩ := (stSt γ G σ).M.tripleAt_of_lift
      (c := (stSt γ G σ).M.pi (stSt γ G σ).hcls a) (d1 := p.1) (d2 := p.2) hrepc hrepc2
      (hnint p.1 hT.1 hn1) (hnint p.2 hT.2.1 hn2) hT.2.2.2 hT.2.2.1
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_exists (σ := σ)
      (v := (stSt γ G σ).M.pi (stSt γ G σ).hcls a) (p := p) ⟨(y1, y2), hy1, hy2, hT'⟩
    have hgp : gapPair γ G σ S ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) = some q := by
      unfold gapPair; rw [if_pos hh]; unfold hingeEntryPair; rw [hp, Option.bind_some]; exact hq
    refine ⟨_, gapSpecification_of hM σ hS hatom hgp hqT, rfl, p, hq1, hq2, ⟨fun _ => ⟨hp, u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩,
      fun h => absurd hh h⟩⟩
  · -- the joint is not merged
    have hcls : (stSt γ G σ).cls a = none := by
      have h1 := ((stSt γ G σ).mem_hinges ((stSt γ G σ).M.pi (stSt γ G σ).hcls a)).not.mp hh
      rw [not_not, (stSt γ G σ).M.ob_pi (stSt γ G σ).hcls] at h1
      rcases hc : (stSt γ G σ).cls a with _ | r
      · rfl
      · exfalso
        have hr : repC (stSt γ G σ).cls a = r := by simp [repC, hc]
        rw [hr] at h1
        rw [(stSt γ G σ).hcls a r hc] at h1
        cases h1
    have hrep : repC (stSt γ G σ).cls a = a := by simp [repC, hcls]
    obtain ⟨p, hp, hsp⟩ := intPairOrig_spec hS
    have hsp' := hsp
    unfold IntSpec at hsp'
    obtain ⟨a1, O, ha1, hO, hOj, hT0, hx0, hy0⟩ := hsp'
    rw [ha] at ha1
    cases ha1
    obtain ⟨y1, y2, hy1, hy2, hT⟩ := (stSt γ G σ).M.tripleAt_of_lift (c := (stSt γ G σ).M.pi (stSt γ G σ).hcls a)
      (d1 := p.1) (d2 := p.2) (by rw [hT0.1, (stSt γ G σ).M.ob_pi, hrep]) (by rw [hT0.2.1, (stSt γ G σ).M.ob_pi, hrep])
      (by rw [hT0.1, hcls]; simp) (by rw [hT0.2.1, hcls]; simp) hT0.2.2.2 hT0.2.2.1
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_exists (σ := σ)
      (v := (stSt γ G σ).M.pi (stSt γ G σ).hcls a) (p := p) ⟨(y1, y2), hy1, hy2, hT⟩
    have hgp : gapPair γ G σ S ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) = some q := by
      unfold gapPair; rw [if_neg hh]; unfold internalPair; rw [hp, Option.bind_some]; exact hq
    refine ⟨_, gapSpecification_of hM σ hS hatom hgp hqT, rfl, p, hq1, hq2, ⟨fun h => absurd h hh,
      fun _ => ⟨hp, a, O, ha, hO, hOj, hT0, hx0, hy0⟩⟩⟩

/-- **The bridge to the designated object.**  For each group the specified pair is, at a non-hinge joint, an internal
pair of the designated object (the images under `od` of its darts are darts of the object); at a hinge it is the
hinge pair `HingeSpec` of the original garden. -/
theorem gapSpecification_pair_of_object (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) :
    ∃ a O, groupJoint γ G S = some a ∧ designatedObject γ G S = some O ∧
      ∃ e : LocalGapSpecification (stSt γ G σ).G ((stSt γ G σ).M.pi (stSt γ G σ).hcls a),
        gapSpecification γ G σ ((stSt γ G σ).M.pi (stSt γ G σ).hcls a) = some e ∧ e.kind = σ S ∧
        (((stSt γ G σ).M.pi (stSt γ G σ).hcls a ∉ (stSt γ G σ).hinges →
          (a = O.upper ∨ a = O.lower) ∧ O.ContainsDart ((stSt γ G σ).M.od e.first) ∧
            O.ContainsDart ((stSt γ G σ).M.od e.second)) ∧
        ((stSt γ G σ).M.pi (stSt γ G σ).hcls a ∈ (stSt γ G σ).hinges →
          HingeSpec γ G S a ((stSt γ G σ).M.od e.first, (stSt γ G σ).M.od e.second))) := by
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

/-- **Hinge entries are SG** (TARGET `subpro` (5): the triple at a hinge always has SG). -/
theorem gapSpecification_hinge_kind (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) {a : GBranch G.tree} (haS : a ∈ S)
    (hh : (stSt γ G σ).M.pi (stSt γ G σ).hcls a ∈ (stSt γ G σ).hinges) : σ S = Molecule.GapKind.SG := by
  have h1 := ((stSt γ G σ).mem_hinges _).mp hh
  rw [(stSt γ G σ).M.ob_pi] at h1
  by_cases h : ∃ u ∈ unitBlocks γ G σ, a ∈ u.atoms
  · obtain ⟨u, hu, hau⟩ := h
    obtain ⟨S'', hS''m, hσ, hmem⟩ := mem_unitBlocks.mp hu
    have hsub := (groupUnitsOf γ G S'').sub u hmem hau
    by_cases hSS : S = S''
    · rw [hSS]; exact hσ
    · exact absurd haS (Finset.disjoint_left.mp (groups_disjoint hM hS hS''m hSS) |> fun f => fun h => f h hsub)
  · push Not at h
    have : repC (stSt γ G σ).cls a = a := stSt_repC_none hM σ h
    rw [this, stSt_cls_none hM σ h] at h1
    exact absurd rfl h1

end WaveTurbulence.GammaLow.Fama
