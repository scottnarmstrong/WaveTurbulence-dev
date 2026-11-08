/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: an object inside a marked group and off `H ∪ B` lies in one survivor (o75 §4.5(d))

`obj_in_survivor`: let `g` be a marked SG group and `P` an object of `G_sb` whose atoms are images of atoms of `g`,
that avoids the hinges and contains no joint of a survivor.  Then `P` lies in one survivor.  Its atoms are unmerged
atoms of `g` off the survivor joints, i.e. interior atoms of survivors, all of whose bonds stay in their survivor;
`P` is connected (`obj_connected`), so it cannot leave the survivor of one of its atoms.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- **A vine-like object is connected through its own bonds.** -/
theorem obj_connected (O : Object M) :
    ∀ u ∈ O.atoms, ∀ v ∈ O.atoms,
      Relation.EqvGen (fun a b => ∃ x, M.InGroup O.atoms x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) u v := by
  obtain ⟨A, a, b, sh⟩ := O
  simp only
  cases sh with
  | vc h => exact h.1.2.2.2.2.2.2.2.2.2
  | hyper R =>
    intro u hu v hv
    have hc := R.adjoint.1.2.2.2.2.2.2.2.2.2 u hu v hv
    clear hu hv
    induction hc with
    | rel p q hr =>
      obtain ⟨x, hx, h1, h2⟩ := hr
      exact Relation.EqvGen.rel _ _ ⟨x.1, hx, h1, h2⟩
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans p q r _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- At an atom of in-degree four inside `S` (and degree `≤ 4`), every dart stays in `S`. -/
theorem inGroup_of_degIn_four (hM : M.IsMolecule) {S : Finset V} {v : V} (hv : v ∈ M.atoms)
    (h4 : M.degIn S v = 4) {x : D} (hx : M.atom x = v) : M.InGroup S x := by
  classical
  have hdeg := deg_le_four M hM hv
  have hle : ((M.dartsAt v).filter fun y => M.InGroup S y).card ≤ (M.dartsAt v).card :=
    Finset.card_filter_le _ _
  have heq : ((M.dartsAt v).filter fun y => M.InGroup S y).card = (M.dartsAt v).card := by
    have : M.deg v = (M.dartsAt v).card := rfl
    unfold Molecule.degIn at h4
    omega
  exact Finset.filter_card_eq heq x ((Mole.mem_dartsAt M v x).mpr hx)

end generic

variable {w : ℕ} {G : Garden w}

section main
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
include hM

/-- A merged atom has a merged representative: an atom of `G_sb` whose preimage is merged is a hinge. -/
theorem unmerged_of_not_hinge {z : GBranch G.tree}
    (h : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z ∉ (stSt G σ Mk).hinges) : (stSt G σ Mk).cls z = none := by
  by_contra hz
  obtain ⟨u, hu, hzu⟩ := unit_of_cls hM σ hz
  apply h
  rw [(stSt G σ Mk).mem_hinges, (stSt G σ Mk).M.ob_pi, stSt_repC_memMk (Mk := Mk) hM σ hu hzu,
    stSt_cls_memMk (Mk := Mk) hM σ hu u.isBlock.2.1]
  simp

/-- The preimage of an unmerged atom: `π w = π z` with `z` unmerged forces `w = z`. -/
theorem eq_of_pi_eq_unmerged {z w : GBranch G.tree} (hz : (stSt G σ Mk).cls z = none)
    (h : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls w = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z) : w = z := by
  have hr := repC_eq_of_pi_eq hM σ h
  have hz' : repC (stSt G σ Mk).cls z = z := by simp [repC, hz]
  rw [hz'] at hr
  by_cases hw : (stSt G σ Mk).cls w = none
  · simpa [repC, hw] using hr
  · obtain ⟨u, hu, hwu⟩ := unit_of_cls hM σ hw
    rw [stSt_repC_memMk (Mk := Mk) hM σ hu hwu] at hr
    have := stSt_cls_memMk (Mk := Mk) hM σ hu u.isBlock.2.1
    rw [hr, hz] at this
    cases this

/-- **One step inside a survivor**: from an unmerged atom of a survivor image off its joints, every bond of `G_sb`
leads back into the survivor image. -/
theorem survObj_step {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ survivorsMk G σ Mk) {p : GBranch (stSt G σ Mk).G.tree} (hp : p ∈ (survObj ht).atoms)
    (hpH : p ∉ (stSt G σ Mk).hinges) (hpu : p ≠ (survObj ht).upper) (hpl : p ≠ (survObj ht).lower)
    {y : GardenDart (stSt G σ Mk).G} (hy : (stSt G σ Mk).G.molecule.atom y = p) :
    (stSt G σ Mk).G.molecule.atom ((stSt G σ Mk).G.molecule.mate y) ∈ (survObj ht).atoms := by
  obtain ⟨hat, hup, hlo, -⟩ := survObj_spec ht
  obtain ⟨S, -, -, hmk, htm, -⟩ := survivorsMk_group ht
  obtain ⟨hvine, -, -⟩ := (markedUnitsOfMK hmk).surv_spec t htm
  obtain ⟨X, hX⟩ := hvine
  have hB := hX.1
  rw [hat] at hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
  have hzn := unmerged_of_not_hinge hM σ hpH
  have hz1 : z ≠ t.2.1 := fun h => hpu (by rw [hup, h])
  have hz2 : z ≠ t.2.2 := fun h => hpl (by rw [hlo, h])
  have h4 := hB.2.2.2.2.2.2.2.2.1 z hz hz1 hz2
  have hod : G.molecule.atom ((stSt G σ Mk).M.od y) = z :=
    eq_of_pi_eq_unmerged hM σ hzn ((atom_lift hM σ).symm.trans hy)
  have hg := inGroup_of_degIn_four hM (hB.1 hz) h4 hod
  rw [atom_lift hM σ, (stSt G σ Mk).M.od_mate, hat]
  exact Finset.mem_image_of_mem _ hg.2

/-- **o75 §4.5(d)**: an object of `G_sb` made of images of atoms of a marked SG group, avoiding the hinges and the
survivor joints, lies in one survivor. -/
theorem obj_in_survivor {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmk : markedGroup G Mk S) (P : Object (stSt G σ Mk).G.molecule)
    (hPS : ∀ p ∈ P.atoms, ∃ z ∈ S, p = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z)
    (hH : Disjoint P.atoms (stSt G σ Mk).hinges)
    (hJ : ∀ t (ht : t ∈ survivorsMk G σ Mk), (survObj ht).upper ∉ P.atoms ∧ (survObj ht).lower ∉ P.atoms) :
    ∃ t, ∃ ht : t ∈ survivorsMk G σ Mk, P.atoms ⊆ (survObj ht).atoms := by
  classical
  have hp0 : P.upper ∈ P.atoms := obj_joint_mem P (Or.inl rfl)
  obtain ⟨z0, hz0S, hz0⟩ := hPS _ hp0
  have hz0n : (stSt G σ Mk).cls z0 = none :=
    unmerged_of_not_hinge hM σ (hz0 ▸ Finset.disjoint_left.mp hH hp0)
  rcases (markedUnitsOfMK hmk).partition z0 hz0S with ⟨u, hu, hz0u⟩ | ⟨t, htm, hz0t⟩
  · exfalso
    have huB : u ∈ unitBlocks G σ Mk :=
      mem_unitBlocksMk.mpr ⟨S, hS, hσ, (groupUnitsMk_of_markedMK hmk).symm ▸ hu⟩
    rw [stSt_cls_memMk (Mk := Mk) hM σ huB hz0u] at hz0n
    cases hz0n
  have ht : t ∈ survivorsMk G σ Mk := mem_survivorsMk_iffMK.mpr ⟨S, hS, hσ, hmk, htm⟩
  refine ⟨t, ht, ?_⟩
  obtain ⟨hat, -⟩ := survObj_spec ht
  have hp0T : P.upper ∈ (survObj ht).atoms := by rw [hat, hz0]; exact Finset.mem_image_of_mem _ hz0t
  -- one step of `P` stays in the survivor
  have step : ∀ a b, a ∈ P.atoms → a ∈ (survObj ht).atoms → ∀ x : GardenDart (stSt G σ Mk).G,
      (stSt G σ Mk).G.molecule.atom x = a → (stSt G σ Mk).G.molecule.atom ((stSt G σ Mk).G.molecule.mate x) = b →
      b ∈ (survObj ht).atoms := by
    intro a b haP haT x hx hxb
    rw [← hxb]
    exact survObj_step hM σ ht haT (Finset.disjoint_left.mp hH haP)
      (fun h => (hJ t ht).1 (h ▸ haP)) (fun h => (hJ t ht).2 (h ▸ haP)) hx
  have key : ∀ a b, Relation.EqvGen (fun a b => ∃ x, (stSt G σ Mk).G.molecule.InGroup P.atoms x ∧
      (stSt G σ Mk).G.molecule.atom x = a ∧ (stSt G σ Mk).G.molecule.atom ((stSt G σ Mk).G.molecule.mate x) = b)
      a b → (a ∈ (survObj ht).atoms ↔ b ∈ (survObj ht).atoms) := by
    intro a b h
    induction h with
    | rel a b hr =>
      obtain ⟨x, hx, h1, h2⟩ := hr
      constructor
      · intro haT
        exact step a b (h1 ▸ hx.1) haT x h1 h2
      · intro hbT
        refine step b a (h2 ▸ hx.2) hbT ((stSt G σ Mk).G.molecule.mate x) h2 ?_
        rw [(stSt G σ Mk).G.molecule.mate_mate]; exact h1
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  intro q hq
  exact (key _ _ (obj_connected P _ hp0 q hq)).mp hp0T

end main

end WaveTurbulence.VineA.NormalizedSplice
