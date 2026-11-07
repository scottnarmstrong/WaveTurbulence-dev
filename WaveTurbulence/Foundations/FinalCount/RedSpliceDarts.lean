/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceMol
public import WaveTurbulence.Foundations.Molecule.MoleculeConnectedBlocks
public import WaveTurbulence.Foundations.Molecule.VineRealizationPaths
public import WaveTurbulence.Foundations.Spine.MoleculeCommonJointDegree
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): dart counting at the atoms of a decomposed block

Local lemmas on the darts at an atom of a block: an interior atom has all its darts internal; a joint whose
internal degree is unchanged in a bigger group has the same internal darts; an atom that is a joint of two
sub-blocks of internal degree `2` and has total degree `4` has every dart in one of them.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}

theorem allInt (hN : N.IsMolecule) {X : Finset V} {j1 j2 v : V} (hX : N.IsBlock X j1 j2) (hv : v ∈ X)
    (h1 : v ≠ j1) (h2 : v ≠ j2) {d : D} (hd : N.atom d = v) : N.InGroup X d := by
  have h4 : N.degIn X v = 4 := hX.2.2.2.2.2.2.2.2.1 v hv h1 h2
  have hle : N.deg v ≤ 4 := deg_le_four N hN (hX.1 hv)
  have hsub : (N.dartsAt v).filter (N.InGroup X) ⊆ N.dartsAt v := Finset.filter_subset _ _
  have h4' : ((N.dartsAt v).filter (N.InGroup X)).card = 4 := h4
  have hle' : (N.dartsAt v).card ≤ 4 := hle
  have heq : (N.dartsAt v).filter (N.InGroup X) = N.dartsAt v :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : d ∈ N.dartsAt v := by
    simp [Molecule.dartsAt, hd]
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2

theorem subEq {X Y : Finset V} (hXY : X ⊆ Y) {v : V} (h : N.degIn X v = N.degIn Y v) {d : D}
    (hd : N.atom d = v) (hY : N.InGroup Y d) : N.InGroup X d := by
  have hsub : (N.dartsAt v).filter (N.InGroup X) ⊆ (N.dartsAt v).filter (N.InGroup Y) := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨h1, ⟨hXY h2.1, hXY h2.2⟩⟩
  have h' : ((N.dartsAt v).filter (N.InGroup X)).card = ((N.dartsAt v).filter (N.InGroup Y)).card := h
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : d ∈ (N.dartsAt v).filter (N.InGroup Y) :=
    Finset.mem_filter.mpr ⟨by simp [Molecule.dartsAt, hd], hY⟩
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2

theorem splitTwo (hN : N.IsMolecule) {X X' : Finset V} {v : V} (hvX : v ∈ X) (hvX' : v ∈ X')
    (hdis : ∀ d, N.InGroup X d → N.InGroup X' d → False)
    (h2 : N.degIn X v = 2) (h2' : N.degIn X' v = 2) (hvm : v ∈ N.atoms) {d : D} (hd : N.atom d = v) :
    N.InGroup X d ∨ N.InGroup X' d := by
  have hle : N.deg v ≤ 4 := deg_le_four N hN hvm
  have hdisj : Disjoint ((N.dartsAt v).filter (N.InGroup X)) ((N.dartsAt v).filter (N.InGroup X')) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact hdis z (Finset.mem_filter.mp hz).2 (Finset.mem_filter.mp hz').2
  have hsub : (N.dartsAt v).filter (N.InGroup X) ∪ (N.dartsAt v).filter (N.InGroup X') ⊆ N.dartsAt v := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  have hcard := Finset.card_union_of_disjoint hdisj
  have h2c : ((N.dartsAt v).filter (N.InGroup X)).card = 2 := h2
  have h2c' : ((N.dartsAt v).filter (N.InGroup X')).card = 2 := h2'
  have hle' : (N.dartsAt v).card ≤ 4 := hle
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : d ∈ N.dartsAt v := by simp [Molecule.dartsAt, hd]
  rw [← heq] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact Or.inl (Finset.mem_filter.mp h).2
  · exact Or.inr (Finset.mem_filter.mp h).2

end WaveTurbulence.RedSplice
