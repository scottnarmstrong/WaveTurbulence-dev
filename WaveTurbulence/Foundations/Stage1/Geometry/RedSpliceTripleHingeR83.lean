/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
-- R83 port of rs-src/RedSpliceTripleHinge.lean (FLOWER-P6 R83): successor designations, see HANDOFF

public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigR83
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R37: `hingePair` lies in every triple bond at its hinge

`triple_in_hingePair`: if a hinge `v` of `G_sb` has a triple bond to `c`, then `hingePair G σ v = some (x, y)` and the two
bonds `x`, `y` (a `TripleAt` pair at `v`) both lead to `c`.  The whole-group case uses the `HingeBest` choice of
`hingeOrigPair` (`whole_pair_in_triple`); the case of a unit of a skipped vine uses that the `HingeSpec` pair is forced
(`skip_pair_in_triple`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

theorem group_eq_of_mem (hM : G.molecule.IsMolecule) {S S' : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hS' : S' ∈ maximalGroups G.molecule) {u u' : CLBlock G}
    (hu : u ∈ (groupUnitsOf G S).units) (hu' : u' ∈ (groupUnitsOf G S').units) {z : GBranch G.tree}
    (hz : z ∈ u.atoms) (hz' : z ∈ u'.atoms) : S = S' := by
  by_contra hne
  exact Finset.disjoint_left.mp (groups_disjoint hM hS hS' hne) ((groupUnitsOf G S).sub u hu hz)
    ((groupUnitsOf G S').sub u' hu' hz')

theorem od_mem_tripleDarts (σ : Prescription G) {v c : GBranch (stSt G σ).G.tree}
    {x : GardenDart (stSt G σ).G} (h : (stSt G σ).M.od x ∈ tripleDarts G σ v c) :
    (stSt G σ).G.molecule.atom x = v ∧ (stSt G σ).G.molecule.atom ((stSt G σ).G.molecule.mate x) = c := by
  unfold tripleDarts at h
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h
  have := (stSt G σ).M.od_inj hyx
  subst this
  rw [Finset.mem_filter, Mole.mem_dartsAt] at hy
  exact hy

section glue
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

/-- B1b (Mk-general form of `hinge_crown`). -/
theorem hinge_crownMk {Mk : Set (Stage1.CLVine _)} {v : GBranch (stSt (Mk := Mk) G σ).G.tree} (hv : v ∈ (stSt (Mk := Mk) G σ).hinges) :
    ∃ u ∈ unitBlocks (Mk := Mk) G σ, (stSt (Mk := Mk) G σ).M.ob v = u.upper := by
  have hcn := ((stSt (Mk := Mk) G σ).mem_hinges v).mp hv
  by_cases h : ∃ u ∈ unitBlocks (Mk := Mk) G σ, (stSt (Mk := Mk) G σ).M.ob v ∈ u.atoms
  swap
  · push Not at h
    exact absurd (stSt_cls_noneMk (Mk := Mk) hM σ h) hcn
  obtain ⟨u, hu, hvu⟩ := h
  have h1 := stSt_cls_memMk (Mk := Mk) hM σ hu hvu
  refine ⟨u, hu, ?_⟩
  have := ((stSt (Mk := Mk) G σ).M.ob_range ((stSt (Mk := Mk) G σ).M.ob v)).mp ⟨v, rfl⟩
  rcases this with h3 | h3
  · rw [h1] at h3; cases h3
  · rw [h1] at h3; exact (Option.some.inj h3).symm

/-- A hinge is the crown of a spliced unit. -/
theorem hinge_crown {v : GBranch (stSt G σ).G.tree} (hv : v ∈ (stSt G σ).hinges) :
    ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob v = u.upper := hinge_crownMk (Mk := ∅) hM σ hv

/-- B1b (Mk-general form of `hinge_ne`). -/
theorem hinge_neMk {u : CLBlock G} {Mk : Set (Stage1.CLVine _)} (hu : u ∈ unitBlocks (Mk := Mk) G σ) {v c : GBranch (stSt (Mk := Mk) G σ).G.tree}
    (hcr : (stSt (Mk := Mk) G σ).M.ob v = u.upper) (h3 : (stSt (Mk := Mk) G σ).G.molecule.bondsBetween v c = 3) : v ≠ c := by
  intro hvc
  subst hvc
  have hpos : 0 < (stSt (Mk := Mk) G σ).G.molecule.bondsBetween v v := by rw [h3]; norm_num
  unfold Molecule.bondsBetween at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hx
  have h2 := hx.2
  unfold Molecule.ends at h2
  have hx1 : (stSt (Mk := Mk) G σ).G.molecule.atom x = v ∧ (stSt (Mk := Mk) G σ).G.molecule.atom ((stSt (Mk := Mk) G σ).G.molecule.mate x) = v := by
    rcases Sym2.eq_iff.mp h2 with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨a, b⟩
    · exact ⟨a, b⟩
  obtain ⟨hin, hn⟩ := od_extMk (Mk := Mk) hM σ hu hcr hx1.1
  obtain ⟨hin2, -⟩ := od_extMk (Mk := Mk) hM σ hu hcr hx1.2
  apply hn
  refine ⟨hin, ?_⟩
  rw [← (stSt (Mk := Mk) G σ).M.od_mate]
  exact hin2

/-- No bond of `G_sb` joins a hinge to itself. -/
theorem hinge_ne {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {v c : GBranch (stSt G σ).G.tree}
    (hcr : (stSt G σ).M.ob v = u.upper) (h3 : (stSt G σ).G.molecule.bondsBetween v c = 3) : v ≠ c := hinge_neMk (Mk := ∅) hM σ hu hcr h3

/-- **R37 (S2a).**  If a hinge `v` of `G_sb` has a triple bond to `c`, the hinge pair `(ℓ_1, ℓ_2)` of `v` (TARGET subpro (5);
`hingePair`) consists of two bonds of that triple bond. -/
theorem triple_in_hingePair {v c : GBranch (stSt G σ).G.tree} (hv : v ∈ (stSt G σ).hinges)
    (h3 : (stSt G σ).G.molecule.bondsBetween v c = 3) :
    ∃ x y, hingePair G σ v = some (x, y) ∧ TripleAt (stSt G σ).G v x y ∧
      (stSt G σ).G.molecule.atom ((stSt G σ).G.molecule.mate x) = c ∧
      (stSt G σ).G.molecule.atom ((stSt G σ).G.molecule.mate y) = c := by
  classical
  obtain ⟨u, hu, hcr⟩ := hinge_crown hM σ hv
  obtain ⟨S, hSm, hσ, hmem⟩ := mem_unitBlocks.mp hu
  have hvc := hinge_ne hM σ hu hcr h3
  rcases hsk : (groupUnitsOf G S).skip with _ | sk
  · -- a whole-group unit
    have hUS := (groupUnitsOf G S).noskip_units hsk u hmem
    obtain ⟨a0, ha0⟩ := exists_groupJoint_eq hSm
    have ha0u : a0 ∈ u.atoms := hUS ▸ (groupJoint_kind ha0).1
    obtain ⟨p, hp, hbest⟩ := hingeOrigPair_best ha0 ⟨u, hmem, ha0u⟩
    obtain ⟨j, hj, hT, hn1, hn2, -, hrel⟩ := hingeSpec_body hM hSm hbest.1 hmem ha0u
    obtain ⟨-, hjw⟩ := hrel hsk
    obtain ⟨y1, y2, hy1, hy2, hP⟩ := ext_lift_darts hM σ hu hcr hj hjw hT.1 hT.2.1 hn1 hn2 hT.2.2.2
    obtain ⟨q, hq, hq1, hq2, hqT⟩ :=
      liftPair_of_exists (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hP.1⟩
    have hat : (stSt G σ).M.pi (stSt G σ).hcls a0 = v := by
      apply (stSt G σ).M.ob_inj
      rw [(stSt G σ).M.ob_pi (stSt G σ).hcls a0, hcr]
      exact stSt_repC_mem hM σ hu ha0u
    have hga : groupAtom G σ S = some v := by
      unfold groupAtom; rw [ha0]; simp [hat]
    have hentry : hingeEntryPair G σ S v = some q := by
      unfold hingeEntryPair; rw [hp]; exact hq
    have hPP : ProperPair G σ v q.1 q.2 :=
      properPair_congr hP (by rw [hq1, hy1]) (by rw [hq2, hy2]) hqT
    have hex : ∃ p' : GardenDart (stSt G σ).G × GardenDart (stSt G σ).G, ∃ S' ∈ maximalGroups G.molecule,
        groupAtom G σ S' = some v ∧ hingeEntryPair G σ S' v = some p' ∧ ProperPair G σ v p'.1 p'.2 :=
      ⟨q, S, hSm, hga, hentry, hPP⟩
    have hdef : hingePair G σ v = some (Classical.choose hex) := by
      unfold hingePair; rw [dif_pos hex]
    obtain ⟨S'', hS''m, hga'', hent'', hP''⟩ := Classical.choose_spec hex
    have hSS : S = S'' := groupAtom_inj hM σ hSm hS''m hga hga''
    subst hSS
    rw [hentry] at hent''
    have hqq : q = Classical.choose hex := Option.some.inj hent''
    have hX := whole_pair_in_triple hM σ hSm hσ hmem hsk hcr hvc h3 ha0u hbest
    have e1 := od_mem_tripleDarts σ (hq1 ▸ hX.1)
    have e2 := od_mem_tripleDarts σ (hq2 ▸ hX.2)
    refine ⟨(Classical.choose hex).1, (Classical.choose hex).2, hdef, hP''.1, ?_, ?_⟩
    · rw [← hqq]; exact e1.2
    · rw [← hqq]; exact e2.2
  · -- a unit of a skipped vine
    obtain ⟨x, y, hxy, hPP, ⟨S', hS', u', hu', hob', p, hsp, hox, hoy⟩, -⟩ := hingePair_spec hM σ hv
    have hz : u.upper ∈ u'.atoms := by
      have : u.upper = u'.upper := hcr.symm.trans hob'
      rw [this]; exact u'.isBlock.2.1
    obtain rfl := group_eq_of_mem hM hSm hS' hmem hu' u.isBlock.2.1 hz
    obtain rfl := unit_eq_any hM hSm hSm hmem hu' u.isBlock.2.1 hz
    have hX := skip_pair_in_triple hM σ hSm hσ hmem hsk hcr hvc h3 u.isBlock.2.1 hsp
    have e1 := od_mem_tripleDarts σ (hox ▸ hX.1)
    have e2 := od_mem_tripleDarts σ (hoy ▸ hX.2)
    exact ⟨x, y, hxy, hPP.1, e1.2, e2.2⟩

end glue

end WaveTurbulence.VineA.NormalizedSplice
