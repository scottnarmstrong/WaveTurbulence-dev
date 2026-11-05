/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # Orientation counts in groups and under deletion of an external bond -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

theorem outIn_mono {A B : Finset V} (hAB : A ⊆ B) (v : V) : M.outIn A v ≤ M.outIn B v := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxv,⟨hxa,hxm⟩,hxo⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxv,⟨hAB hxa,hAB hxm⟩,hxo⟩

theorem inIn_mono {A B : Finset V} (hAB : A ⊆ B) (v : V) : M.inIn A v ≤ M.inIn B v := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxv,⟨hxa,hxm⟩,hxo⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxv,⟨hAB hxa,hAB hxm⟩,hxo⟩

variable [DecidableEq D]

/-- Deleting a bond outside a group preserves every orientation count
inside that group; both mates are excluded together. -/
theorem eraseBond_orientedIn (e : D) (S : Finset V) (v : V) (b : Bool)
    (hne : ¬ M.InGroup S e) :
    (((eraseBond M e).dartsAt v).filter (fun x => (eraseBond M e).InGroup S x ∧ (eraseBond M e).out x = b)).card =
      ((M.dartsAt v).filter (fun x => M.InGroup S x ∧ M.out x = b)).card := by
  apply Finset.card_bij (fun x _hx => x.1)
  · intro x hx
    obtain ⟨hxv,hxg,hxo⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(mem_dartsAt M v x.1).mpr ((mem_dartsAt (eraseBond M e) v x).mp hxv),hxg,hxo⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hxv,hxg,hxo⟩ := Finset.mem_filter.mp hx
    have h1 : x ≠ e := by intro he; exact hne (he ▸ hxg)
    have h2 : x ≠ M.mate e := by
      intro he
      have hh : M.InGroup S (M.mate e) := he ▸ hxg
      exact hne ⟨by simpa only [M.mate_mate] using hh.2,hh.1⟩
    refine ⟨⟨x,h1,h2⟩,Finset.mem_filter.mpr ⟨?_,hxg,hxo⟩,rfl⟩
    exact (mem_dartsAt (eraseBond M e) v ⟨x,h1,h2⟩).mpr ((mem_dartsAt M v x).mp hxv)

/-- A designated joint-to-joint bond removes one incidence at either joint,
independently of its orientation. -/
theorem eraseBond_joint_degrees (e : D) {S : Finset V} {a b : V}
    (he : M.ends e = s(a,b)) (hne : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) :
    (eraseBond M e).degIn S a+1 = M.degIn S a ∧
      (eraseBond M e).degIn S b+1 = M.degIn S b := by
  have hend : (M.atom e = a ∧ M.atom (M.mate e) = b) ∨
      (M.atom e = b ∧ M.atom (M.mate e) = a) := Sym2.eq_iff.mp he
  rcases hend with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · refine ⟨eraseBond_degIn_endpoint M e h1 h2 hne ha hb,?_⟩
    have hh := eraseBond_degIn_endpoint M (M.mate e) h2 (by rw [M.mate_mate]; exact h1) (Ne.symm hne) hb ha
    rw [eraseBond_mate_degIn] at hh
    exact hh
  · refine ⟨?_,eraseBond_degIn_endpoint M e h1 h2 (Ne.symm hne) hb ha⟩
    have hh := eraseBond_degIn_endpoint M (M.mate e) h2 (by rw [M.mate_mate]; exact h1) hne ha hb
    rw [eraseBond_mate_degIn] at hh
    exact hh

end WaveTurbulence.Mole
