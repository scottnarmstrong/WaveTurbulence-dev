/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceExt
import Mathlib.Tactic

/-!
# R83 successor copy (source pinned/r83-RedSplicePairs.lean; SHA in COPIED-SHA256SUMS).
# REDSPLICE-DEF (S2a): existence of the hinge pairs (TARGET `subpro` (5))

* `SpMap.tripleAt_of_lift`: two darts of the skeleton at one class, external to it and of opposite orientations,
  lift to a `TripleAt` pair at the crown.
* `hinge_tripleAt`: every hinge of `G_sb` carries a `TripleAt` pair (the external out/in pair of the unit).
* `objectJoint_pair`: at a joint of an object a `TripleAt` pair inside the object exists.
* `hingePair_spec`: `hingePair` is `some` at every hinge, and lies inside the object of `C_1` at a joint of it.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}


section units
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

/-- B1b (Mk-general form of `unit_eq_of_mem`). -/
theorem unit_eq_of_memMk {u u' : CLBlock G} {Mk : Set (Stage1.CLVine _)} (hu : u ∈ unitBlocks (Mk := Mk) G σ) (hu' : u' ∈ unitBlocks (Mk := Mk) G σ)
    {z : GBranch G.tree} (hz : z ∈ u.atoms) (hz' : z ∈ u'.atoms) : u = u' := by
  by_contra hne
  have : Std.Symm (fun u u' : CLBlock G => Disjoint u.atoms u'.atoms) := ⟨fun _ _ h => h.symm⟩
  have := (unitBlocks_pairwiseMk (Mk := Mk) hM σ).forall hu hu' hne
  exact Finset.disjoint_left.mp this hz hz'

theorem unit_eq_of_mem {u u' : CLBlock G} (hu : u ∈ unitBlocks G σ) (hu' : u' ∈ unitBlocks G σ)
    {z : GBranch G.tree} (hz : z ∈ u.atoms) (hz' : z ∈ u'.atoms) : u = u' := by apply unit_eq_of_memMk (Mk := ∅) <;> assumption

/-- B1b (Mk-general form of `mem_of_cls_eq`). -/
theorem mem_of_cls_eqMk {u : CLBlock G} {Mk : Set (Stage1.CLVine _)} (hu : u ∈ unitBlocks (Mk := Mk) G σ) {z : GBranch G.tree}
    (hz : (stSt (Mk := Mk) G σ).cls z = some u.upper) : z ∈ u.atoms := by
  by_cases h : ∃ u' ∈ unitBlocks (Mk := Mk) G σ, z ∈ u'.atoms
  · obtain ⟨u', hu', hzu'⟩ := h
    have h1 := stSt_cls_memMk (Mk := Mk) hM σ hu' hzu'
    rw [hz] at h1
    have h2 : u'.upper = u.upper := (Option.some.inj h1).symm
    have h3 : u'.upper ∈ u.atoms := h2 ▸ u.isBlock.2.1
    have := unit_eq_of_memMk (Mk := Mk) hM σ hu' hu u'.isBlock.2.1 h3
    exact this ▸ hzu'
  · push Not at h
    have := stSt_cls_noneMk (Mk := Mk) hM σ h
    rw [this] at hz
    cases hz

theorem mem_of_cls_eq {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {z : GBranch G.tree}
    (hz : (stSt G σ).cls z = some u.upper) : z ∈ u.atoms := by apply mem_of_cls_eqMk (Mk := ∅) <;> assumption

/-- B1b (Mk-general form of `ext_lift_darts`). -/
theorem ext_lift_dartsMk {u : CLBlock G} {Mk : Set (Stage1.CLVine _)} (hu : u ∈ unitBlocks (Mk := Mk) G σ) {c : GBranch (stSt (Mk := Mk) G σ).G.tree}
    (hc : (stSt (Mk := Mk) G σ).M.ob c = u.upper) {j : GBranch G.tree} (hj : j ∈ u.atoms) (hjj : j = u.upper ∨ j = u.lower)
    {d1 d2 : GardenDart G} (h1 : G.molecule.atom d1 = j) (h2 : G.molecule.atom d2 = j)
    (n1 : ¬ G.molecule.InGroup u.atoms d1) (n2 : ¬ G.molecule.InGroup u.atoms d2)
    (hout : G.molecule.out d1 ≠ G.molecule.out d2) :
    ∃ y1 y2, (stSt (Mk := Mk) G σ).M.od y1 = d1 ∧ (stSt (Mk := Mk) G σ).M.od y2 = d2 ∧ ProperPair G σ c y1 y2 := by
  have hnint : ∀ d : GardenDart G, G.molecule.atom d = j → ¬ G.molecule.InGroup u.atoms d →
      ¬ ∃ a, (stSt (Mk := Mk) G σ).cls (G.molecule.atom d) = some a ∧
        (stSt (Mk := Mk) G σ).cls (G.molecule.atom (G.molecule.mate d)) = some a := by
    intro d hd hnd ⟨a, ha, ha'⟩
    rw [hd, stSt_cls_memMk (Mk := Mk) hM σ hu hj] at ha
    have : a = u.upper := (Option.some.inj ha).symm
    subst this
    exact hnd ⟨hd ▸ hj, mem_of_cls_eqMk (Mk := Mk) hM σ hu ha'⟩
  have hrep : ∀ d : GardenDart G, G.molecule.atom d = j →
      repC (stSt (Mk := Mk) G σ).cls (G.molecule.atom d) = (stSt (Mk := Mk) G σ).M.ob c := by
    intro d hd
    rw [hd, stSt_repC_memMk (Mk := Mk) hM σ hu hj, hc]
  obtain ⟨y1, y2, hy1, hy2, hT⟩ := (stSt (Mk := Mk) G σ).M.tripleAt_of_lift (c := c) (hrep d1 h1) (hrep d2 h2)
    (hnint d1 h1 n1) (hnint d2 h2 n2) hout (by
      intro h
      apply n1
      exact ⟨h1 ▸ hj, by rw [← h, h2]; exact hj⟩)
  refine ⟨y1, y2, hy1, hy2, hT, u, hu, hc, j, hjj, by rw [hy1]; exact h1, by rw [hy2]; exact h2,
    by rw [hy1]; exact n1, by rw [hy2]; exact n2⟩

/-- The crown of a unit carries a proper pair lifting two GIVEN external out/in darts of the unit at one of its
joints (`od y1 = d1`, `od y2 = d2`). -/
theorem ext_lift_darts {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {c : GBranch (stSt G σ).G.tree}
    (hc : (stSt G σ).M.ob c = u.upper) {j : GBranch G.tree} (hj : j ∈ u.atoms) (hjj : j = u.upper ∨ j = u.lower)
    {d1 d2 : GardenDart G} (h1 : G.molecule.atom d1 = j) (h2 : G.molecule.atom d2 = j)
    (n1 : ¬ G.molecule.InGroup u.atoms d1) (n2 : ¬ G.molecule.InGroup u.atoms d2)
    (hout : G.molecule.out d1 ≠ G.molecule.out d2) :
    ∃ y1 y2, (stSt G σ).M.od y1 = d1 ∧ (stSt G σ).M.od y2 = d2 ∧ ProperPair G σ c y1 y2 := by apply ext_lift_dartsMk (Mk := ∅) <;> assumption

end units


/-- **A pair inside an object at its joint** (TARGET `subpro` (5), second sentence): at a joint of a vine-like
object a `TripleAt` pair of darts of the object (of its adjoint, for a hyper-object) exists. -/
theorem objectJoint_pair {G' : Garden w} (O : Object G'.molecule) {v : GBranch G'.tree}
    (hv : v = O.upper ∨ v = O.lower) :
    ∃ x y, TripleAt G' v x y ∧ O.ContainsDart x ∧ O.ContainsDart y := by
  obtain ⟨A, a, b, sh⟩ := O
  simp only at hv
  cases sh with
  | vc h =>
    have hB : G'.molecule.IsBlock A a b := h.1
    rcases hv with rfl | rfl
    · obtain ⟨x, y, hx, hy, hxA, hyA, hxo, hyo, hne⟩ := block_pair hB
      refine ⟨x, y, ⟨hx, hy, hne, by rw [hxo, hyo]; simp⟩, ?_, ?_⟩
      · exact hxA
      · exact hyA
    · obtain ⟨x, y, hx, hy, hxA, hyA, hxo, hyo, hne⟩ := block_pair (block_swap_joints _ hB)
      refine ⟨x, y, ⟨hx, hy, hne, by rw [hxo, hyo]; simp⟩, ?_, ?_⟩
      · exact hxA
      · exact hyA
  | hyper R =>
    have hB : (eraseBond G'.molecule R.added).IsBlock A a b := R.adjoint.1
    have key : ∀ (j j' : GBranch G'.tree), (eraseBond G'.molecule R.added).IsBlock A j j' →
        ∃ x y, TripleAt G' j x y ∧ (R.added ≠ x ∧ G'.molecule.mate R.added ≠ x ∧ G'.molecule.InGroup A x) ∧
          (R.added ≠ y ∧ G'.molecule.mate R.added ≠ y ∧ G'.molecule.InGroup A y) := by
      intro j j' hBj
      obtain ⟨x, y, hx, hy, hxA, hyA, hxo, hyo, hne⟩ := block_pair hBj
      refine ⟨x.1, y.1, ⟨hx, hy, fun h => hne (Subtype.ext h), by
        have a1 : G'.molecule.out x.1 = true := hxo
        have a2 : G'.molecule.out y.1 = false := hyo
        rw [a1, a2]; simp⟩, ⟨fun h => x.2.1 h.symm, fun h => x.2.2 h.symm, hxA⟩,
        ⟨fun h => y.2.1 h.symm, fun h => y.2.2 h.symm, hyA⟩⟩
    rcases hv with rfl | rfl
    · obtain ⟨x, y, hT, hx, hy⟩ := key _ _ hB
      exact ⟨x, y, hT, ⟨fun h => hx.1 h.symm, fun h => hx.2.1 h.symm, hx.2.2⟩,
        ⟨fun h => hy.1 h.symm, fun h => hy.2.1 h.symm, hy.2.2⟩⟩
    · obtain ⟨x, y, hT, hx, hy⟩ := key _ _ (block_swap_joints _ hB)
      exact ⟨x, y, hT, ⟨fun h => hx.1 h.symm, fun h => hx.2.1 h.symm, hx.2.2⟩,
        ⟨fun h => hy.1 h.symm, fun h => hy.2.1 h.symm, hy.2.2⟩⟩


theorem Object.upper_mem {G' : Garden w} (O : Object G'.molecule) : O.upper ∈ O.atoms := by
  obtain ⟨A, a, b, sh⟩ := O
  cases sh with
  | vc h => exact h.1.2.1
  | hyper R => exact R.adjoint.1.2.1

theorem Object.lower_mem {G' : Garden w} (O : Object G'.molecule) : O.lower ∈ O.atoms := by
  obtain ⟨A, a, b, sh⟩ := O
  cases sh with
  | vc h => exact h.1.2.2.1
  | hyper R => exact R.adjoint.1.2.2.1

end WaveTurbulence.VineA.NormalizedSplice
