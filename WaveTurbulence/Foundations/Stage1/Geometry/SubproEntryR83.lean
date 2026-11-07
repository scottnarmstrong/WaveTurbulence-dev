/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
-- R83 port of sp-src/SubproEntry.lean (FLOWER-P6 R83): successor designations, see HANDOFF

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedR83
import Mathlib.Tactic

/-!
# SUBPRO (S4): the entry of a group of `𝒞` lies inside the `C_1` object of the group

For a group `S` with an SG object `O` of `C_1`, the gap-specification entry at `π a` (`a = groupJoint G S`) is a pair of
darts inside `O` at one of its joints (HV: the designated object and `O` share the canonical triple `hvGroupPick`; skipped
vine: `HingeSpec` at a hinge, or `L0 = ∅` and the darts of the block at `x` are the darts of the vine).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)}

/-- B1b (Mk-general form of `atom_eq_pi`). -/
theorem atom_eq_piMk (σ : Prescription G) {Mk : Set (Stage1.CLVine _)} (f : GardenDart (stSt (Mk := Mk) G σ).G) :
    (stSt (Mk := Mk) G σ).G.molecule.atom f = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls (G.molecule.atom ((stSt (Mk := Mk) G σ).M.od f)) ∧
    (stSt (Mk := Mk) G σ).G.molecule.atom ((stSt (Mk := Mk) G σ).G.molecule.mate f) =
      (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls (G.molecule.atom (G.molecule.mate ((stSt (Mk := Mk) G σ).M.od f))) := by
  constructor
  · apply (stSt (Mk := Mk) G σ).M.ob_inj
    rw [(stSt (Mk := Mk) G σ).M.ob_pi, (stSt (Mk := Mk) G σ).M.ob_atom]
  · apply (stSt (Mk := Mk) G σ).M.ob_inj
    rw [(stSt (Mk := Mk) G σ).M.ob_pi, (stSt (Mk := Mk) G σ).M.ob_atom, (stSt (Mk := Mk) G σ).M.od_mate]

theorem atom_eq_pi (σ : Prescription G) (f : GardenDart (stSt G σ).G) :
    (stSt G σ).G.molecule.atom f = (stSt G σ).M.pi (stSt G σ).hcls (G.molecule.atom ((stSt G σ).M.od f)) ∧
    (stSt G σ).G.molecule.atom ((stSt G σ).G.molecule.mate f) =
      (stSt G σ).M.pi (stSt G σ).hcls (G.molecule.atom (G.molecule.mate ((stSt G σ).M.od f))) := atom_eq_piMk (Mk := ∅) σ f

/-- B1b (Mk-general form of `containsDart_of_orig`). -/
theorem containsDart_of_origMk (σ : Prescription G) {Mk : Set (Stage1.CLVine _)} {O : Object (stSt (Mk := Mk) G σ).G.molecule} {A : Finset (GBranch G.tree)}
    (hOa : O.atoms = A.image ((stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls)) {f : GardenDart (stSt (Mk := Mk) G σ).G}
    (hf : G.molecule.InGroup A ((stSt (Mk := Mk) G σ).M.od f))
    (hsh : ∀ R, O.shape = VineLikeObject.hyper R →
      (stSt (Mk := Mk) G σ).M.od f ≠ (stSt (Mk := Mk) G σ).M.od R.added ∧
        (stSt (Mk := Mk) G σ).M.od f ≠ G.molecule.mate ((stSt (Mk := Mk) G σ).M.od R.added)) : O.ContainsDart f := by
  have hg : (stSt (Mk := Mk) G σ).G.molecule.InGroup O.atoms f := by
    obtain ⟨h1, h2⟩ := atom_eq_piMk (Mk := Mk) σ f
    rw [hOa]
    exact ⟨by rw [h1]; exact Finset.mem_image_of_mem _ hf.1, by rw [h2]; exact Finset.mem_image_of_mem _ hf.2⟩
  unfold Object.ContainsDart
  cases hs : O.shape with
  | vc _ => exact hg
  | hyper R' =>
    obtain ⟨n1, n2⟩ := hsh R' hs
    refine ⟨fun h => n1 (by rw [h]), fun h => n2 ?_, hg⟩
    rw [← (stSt (Mk := Mk) G σ).M.od_mate, h]

/-- A dart of `G_sb` whose original dart lies in `A` is inside the object with atoms `π''A`. -/
theorem containsDart_of_orig (σ : Prescription G) {O : Object (stSt G σ).G.molecule} {A : Finset (GBranch G.tree)}
    (hOa : O.atoms = A.image ((stSt G σ).M.pi (stSt G σ).hcls)) {f : GardenDart (stSt G σ).G}
    (hf : G.molecule.InGroup A ((stSt G σ).M.od f))
    (hsh : ∀ R, O.shape = VineLikeObject.hyper R →
      (stSt G σ).M.od f ≠ (stSt G σ).M.od R.added ∧
        (stSt G σ).M.od f ≠ G.molecule.mate ((stSt G σ).M.od R.added)) : O.ContainsDart f := containsDart_of_origMk (Mk := ∅) σ hOa hf hsh

theorem inGroup_of_degIn_eq {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
    {A S : Finset V} (hAS : A ⊆ S) {v : V} (h : N.degIn A v = N.degIn S v) {d : D} (hd : N.atom d = v)
    (hS : N.InGroup S d) : N.InGroup A d := by
  classical
  unfold Molecule.degIn at h
  have hsub : (N.dartsAt v).filter (fun x => N.InGroup A x) ⊆ (N.dartsAt v).filter (fun x => N.InGroup S x) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, ⟨hAS hx.2.1, hAS hx.2.2⟩⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
  have hmem : d ∈ (N.dartsAt v).filter (fun x => N.InGroup S x) :=
    Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt N v d).mpr hd, hS⟩
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- With `L0 = ∅` and `x = a`, the darts of the block `S` at `a` are darts of the vine `A`. -/
theorem skel_darts_in_A {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
    {S A L0 R0 : Finset V} {a b x y : V} (H : SkelDecomp N S A L0 R0 a b x y) (hx : x = a) {d : D}
    (hd : N.atom d = a) (hS : N.InGroup S d) : N.InGroup A d := by
  have hAS : A ⊆ S := by
    rw [H.hS]
    exact fun z hz => Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  have h1 := (Mole.block_joint_degrees N H.hA).1
  have h2 := (Mole.block_joint_degrees N H.hSB).1
  subst hx
  exact inGroup_of_degIn_eq hAS (h1.trans h2.symm) hd hS

end WaveTurbulence.VineA.NormalizedSplice.Subpro
