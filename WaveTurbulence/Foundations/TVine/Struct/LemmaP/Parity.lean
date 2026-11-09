/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Statement
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-!
# Lemma P, part 1: cuts of even-degree dart sets are even (packet L3-LP)

Source: N3 Lemma P (`research-gamma-half-3/NOTES.txt` L500–L511), the last step: "every V-degree is even (2 or 4), so
every cut of V is even". Here a "graph" is a mate-closed set of darts `P` of a molecule; its cut at `X` is the set of
darts of `P` leaving `X` (`leaving`). If every atom of `X` carries an even number of darts of `P`, the cut is even
(`even_card_leaving`). The two instances used by Lemma P:
* the atomic group of a block (joint degree 2, interior degree 4; `even_degIn_of_isBlock`);
* the bonds `E(U°)` of a vine-like object `U` (`Src.Object.ContainsDart`): its block, or for a hyper object the
  adjoint block (the designated bond removed) (`containsDart_mate_iff`, `even_card_containsDart`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.LemmaP

open Finset GammaLow.FinalCount

variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The darts of the mate-closed dart set `P` leaving the atom set `X` (the cut of `P` at `X`, one dart per bond). -/
def leaving (M : Molecule V D) (P : D → Prop) [DecidablePred P] (X : Finset V) : Finset D :=
  univ.filter fun x => P x ∧ M.atom x ∈ X ∧ M.atom (M.mate x) ∉ X

theorem mem_leaving {M : Molecule V D} {P : D → Prop} [DecidablePred P] {X : Finset V} {x : D} :
    x ∈ leaving M P X ↔ P x ∧ M.atom x ∈ X ∧ M.atom (M.mate x) ∉ X := by
  simp [leaving]

/-- **Even cuts.** If `P` is closed under `mate` and every atom of `X` carries an even number of darts of `P`, then an
even number of darts of `P` leave `X`. (The darts of `P` at `X` are those leaving `X` and the internal ones, which
pair off under `mate`.) -/
theorem even_card_leaving (M : Molecule V D) (P : D → Prop) [DecidablePred P] (hP : ∀ x, P (M.mate x) ↔ P x)
    (X : Finset V) (hdeg : ∀ v ∈ X, Even ((M.dartsAt v).filter P).card) : Even (leaving M P X).card := by
  set A : Finset D := univ.filter fun x => P x ∧ M.atom x ∈ X with hA
  -- the darts of `P` at `X`: an even number
  have hAeven : Even A.card := by
    have hmaps : (A : Set D).MapsTo M.atom X := by
      intro x hx
      exact ((mem_filter.mp (mem_coe.mp hx)).2).2
    rw [card_eq_sum_card_fiberwise hmaps]
    refine Finset.even_sum _ fun v hv => ?_
    have hfib : A.filter (fun a => M.atom a = v) = (M.dartsAt v).filter P := by
      ext x
      simp only [hA, mem_filter, mem_univ, true_and, Mole.mem_dartsAt]
      constructor
      · rintro ⟨⟨hp, -⟩, hx⟩
        exact ⟨hx, hp⟩
      · rintro ⟨hx, hp⟩
        exact ⟨⟨hp, hx ▸ hv⟩, hx⟩
    rw [hfib]
    exact hdeg v hv
  -- the internal darts: an even number (the mate of an outgoing one is incoming)
  set I : Finset D := A.filter fun x => M.atom (M.mate x) ∈ X with hI
  have hIeven : Even I.card := by
    have hsplit := card_filter_add_card_filter_not (s := I) (fun x => M.out x = true)
    have hbij : (I.filter fun x => ¬ M.out x = true).card = (I.filter fun x => M.out x = true).card := by
      refine card_nbij' M.mate M.mate ?_ ?_ ?_ ?_
      · intro x hx
        simp only [hI, hA, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
        obtain ⟨⟨⟨hp, hxX⟩, hmX⟩, hout⟩ := hx
        refine ⟨⟨⟨(hP x).mpr hp, hmX⟩, by rw [M.mate_mate]; exact hxX⟩, ?_⟩
        rw [M.out_mate]
        simpa using hout
      · intro x hx
        simp only [hI, hA, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
        obtain ⟨⟨⟨hp, hxX⟩, hmX⟩, hout⟩ := hx
        refine ⟨⟨⟨(hP x).mpr hp, hmX⟩, by rw [M.mate_mate]; exact hxX⟩, ?_⟩
        rw [M.out_mate, hout]
        decide
      · intro x _
        exact M.mate_mate x
      · intro x _
        exact M.mate_mate x
    rw [← hsplit, hbij]
    exact ⟨_, rfl⟩
  -- the darts leaving `X` are the rest
  have hL : leaving M P X = A.filter fun x => ¬ M.atom (M.mate x) ∈ X := by
    ext x
    simp [leaving, hA, and_assoc]
  have hsplit := card_filter_add_card_filter_not (s := A) (fun x => M.atom (M.mate x) ∈ X)
  rw [hL]
  rw [← hsplit] at hAeven
  exact (Nat.even_add.mp hAeven).mp hIeven

/-- Every atom has even degree in the atomic group of a block (joints `2`, interior atoms `4`, others `0`). -/
theorem even_degIn_of_isBlock {D' : Type*} [Fintype D'] [DecidableEq D'] {M : Molecule V D'} {T : Finset V}
    {a b : V} (hB : M.IsBlock T a b) (v : V) : Even (M.degIn T v) := by
  have hj := Mole.block_joint_degrees M hB
  obtain ⟨-, -, -, -, -, -, -, -, hint, -⟩ := hB
  by_cases hv : v ∈ T
  · by_cases ha : v = a
    · subst ha
      rw [hj.1]
      exact even_two
    · by_cases hb : v = b
      · subst hb
        rw [hj.2]
        exact even_two
      · rw [hint v hv ha hb]
        exact ⟨2, rfl⟩
  · have h0 : M.degIn T v = 0 := by
      unfold Molecule.degIn
      rw [card_eq_zero, filter_eq_empty_iff]
      intro x hx hg
      exact hv ((Mole.mem_dartsAt M v x).mp hx ▸ hg.1)
    rw [h0]
    exact ⟨0, rfl⟩

/-- The atomic group of `T` is closed under `mate`. -/
theorem inGroup_mate_iff (M : Molecule V D) (T : Finset V) (x : D) : M.InGroup T (M.mate x) ↔ M.InGroup T x := by
  unfold Molecule.InGroup
  rw [M.mate_mate, and_comm]

/-- The bonds `E(U°)` of a vine-like object are closed under `mate`. -/
theorem containsDart_mate_iff {γ : ℝ} {M : Molecule V D} (C : Src.Object γ M) (x : D) :
    C.ContainsDart (M.mate x) ↔ C.ContainsDart x := by
  obtain ⟨A, a, b, sh⟩ := C
  cases sh with
  | vc _ => exact inGroup_mate_iff M A x
  | hyper R =>
    change (M.mate x ≠ R.added ∧ M.mate x ≠ M.mate R.added ∧ M.InGroup A (M.mate x)) ↔
      (x ≠ R.added ∧ x ≠ M.mate R.added ∧ M.InGroup A x)
    rw [inGroup_mate_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun h => h2 (by rw [h]), fun h => h1 (by rw [h, M.mate_mate]), h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun h => h2 (by rw [← h, M.mate_mate]), fun h => h1 ?_, h3⟩
      have := congrArg M.mate h
      rwa [M.mate_mate, M.mate_mate] at this

/-- Degrees after removing the bond of `e` (`Molecule.eraseBond`), counted by darts of `M`. -/
theorem degIn_eraseBond (M : Molecule V D) (e : D) (T : Finset V) (v : V) :
    (M.eraseBond e).degIn T v = ((M.dartsAt v).filter fun x => x ≠ e ∧ x ≠ M.mate e ∧ M.InGroup T x).card := by
  unfold Molecule.degIn
  refine card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    rw [mem_filter, Mole.mem_dartsAt] at hx
    rw [mem_filter, Mole.mem_dartsAt]
    exact ⟨hx.1, x.2.1, x.2.2, hx.2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro y hy
    rw [mem_filter, Mole.mem_dartsAt] at hy
    obtain ⟨hyv, hye, hym, hyg⟩ := hy
    refine ⟨⟨y, hye, hym⟩, ?_, rfl⟩
    rw [mem_filter, Mole.mem_dartsAt]
    exact ⟨hyv, hyg⟩

/-- A dart of `E(U°)` is a dart of the atomic group of `U`. -/
theorem inGroup_of_containsDart {γ : ℝ} {M : Molecule V D} (C : Src.Object γ M) {x : D} (h : C.ContainsDart x) :
    M.InGroup C.atoms x := by
  obtain ⟨A, a, b, sh⟩ := C
  cases sh with
  | vc _ => exact h
  | hyper _ => exact h.2.2

/-- Every atom carries an even number of darts of `E(U°)`: they are the darts of the block of `U` (or, for a hyper
object, of its adjoint block) at that atom. -/
theorem even_card_containsDart {γ : ℝ} {M : Molecule V D} (C : Src.Object γ M) [DecidablePred C.ContainsDart]
    (v : V) : Even ((M.dartsAt v).filter C.ContainsDart).card := by
  obtain ⟨A, a, b, sh⟩ := C
  cases sh with
  | vc h =>
    have hE := even_degIn_of_isBlock h.1 v
    unfold Molecule.degIn at hE
    convert hE using 2
    ext x
    simp only [mem_filter]
    exact Iff.rfl
  | hyper R =>
    have hE := even_degIn_of_isBlock R.adjoint.1 v
    rw [degIn_eraseBond] at hE
    convert hE using 2
    ext x
    simp only [mem_filter]
    exact Iff.rfl

end WaveTurbulence.TVine.Struct.LemmaP
