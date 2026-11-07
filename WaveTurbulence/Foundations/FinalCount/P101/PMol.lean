/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.P101.Basic
public import WaveTurbulence.Foundations.FinalCount.Degen.EraseMolecule
import Mathlib.Tactic

/-! # Prop 10.1', molecules with a protected set

`PMol B M`: `M` satisfies the molecule axioms, the atoms of the protected set `B` have degree `≤ 2`, and every
component contains an unsaturated atom, where an atom is saturated if its degree is its cap (`4` outside `B`, `2`
in `B`). The class is preserved by atom erasure (copy of `Degen.isMolecule_eraseAtoms`), and every component then
contains an atom that is removable by operation (a): unprotected of degree `≤ 3`, or protected of degree `≤ 1`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {B : Finset V} {M : Molecule V D}

/-- The degree cap of an atom. -/
def cap (B : Finset V) (v : V) : ℕ := if v ∈ B then 2 else 4

structure PMol (B : Finset V) (M : Molecule V D) : Prop where
  caps : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2
  prot : ∀ v ∈ M.atoms, v ∈ B → M.deg v ≤ 2
  unsat : ∀ v ∈ M.atoms, ∃ u ∈ M.atoms, M.SameComponent v u ∧ M.deg u ≠ cap B u

theorem PMol.deg_le (h : PMol B M) {v : V} (hv : v ∈ M.atoms) : M.deg v ≤ cap B v := by
  have h1 := h.caps v hv
  have he := Mole.outdeg_add_indeg M v
  unfold cap
  split_ifs with hB
  · exact h.prot v hv hB
  · omega

theorem PMol.isMolecule (h : PMol B M) : M.IsMolecule := by
  refine ⟨h.caps, fun v hv => ?_⟩
  obtain ⟨u, hu, hvu, hne⟩ := h.unsat v hv
  refine ⟨u, hu, hvu, ?_⟩
  intro h4
  apply hne
  unfold cap
  split_ifs with hB
  · have := h.prot u hu hB; omega
  · exact h4

/-- A surviving saturated atom lost no dart. -/
theorem adj_erase_of_surviving_sat (hdeg : ∀ v ∈ M.atoms, M.deg v ≤ cap B v)
    (Y : Finset V)
    {a b : V} (ha : a ∈ (eraseAtoms M Y).atoms) (hsat : (eraseAtoms M Y).deg a = cap B a)
    (hab : M.Adj a b) : b ∈ (eraseAtoms M Y).atoms ∧ (eraseAtoms M Y).Adj a b := by
  obtain ⟨x,hxa,hxb⟩ := hab
  have haY := (mem_sdiff.mp ha).2
  have he := deg_eraseAtoms_add_removed M Y haY
  have hcap := hdeg a (mem_sdiff.mp ha).1
  have hempty : removedDartsAt M Y a = ∅ := card_eq_zero.mp (by omega)
  have hbY : b ∉ Y := by
    intro hb
    have hx : x ∈ removedDartsAt M Y a := mem_filter.mpr
      ⟨(Mole.mem_dartsAt M a x).mpr hxa,hxb.symm ▸ hb⟩
    rw [hempty] at hx
    simpa using hx
  have hxY : M.atom x ∉ Y := hxa.symm ▸ haY
  have hmxY : M.atom (M.mate x) ∉ Y := hxb.symm ▸ hbY
  exact ⟨mem_sdiff.mpr ⟨hxb ▸ M.atom_mem (M.mate x),hbY⟩,
    ⟨⟨x,hxY,hmxY⟩,hxa,hxb⟩⟩

theorem PMol.erase (hM : PMol B M) (Y : Finset V) : PMol B (eraseAtoms M Y) := by
  classical
  constructor
  · intro z hz
    have ho := card_filtered_dartsAt_erase_le M Y z (fun x => M.out x = true)
    have hi := card_filtered_dartsAt_erase_le M Y z (fun x => M.out x = false)
    exact ⟨ho.trans (hM.caps z (mem_sdiff.mp hz).1).1,hi.trans (hM.caps z (mem_sdiff.mp hz).1).2⟩
  · intro z hz hzB
    have he := deg_eraseAtoms_add_removed M Y (mem_sdiff.mp hz).2
    have := hM.prot z (mem_sdiff.mp hz).1 hzB
    omega
  · intro z hz
    by_contra hn
    have hsat (a : V) (ha : a ∈ (eraseAtoms M Y).atoms)
        (hza : (eraseAtoms M Y).SameComponent z a) : (eraseAtoms M Y).deg a = cap B a := by
      by_contra hne
      exact hn ⟨a,ha,hza,hne⟩
    let C := fun a => a ∈ (eraseAtoms M Y).atoms ∧ (eraseAtoms M Y).SameComponent z a
    have hclosed (a b : V) (hab : M.Adj a b) (ha : C a) : C b := by
      obtain ⟨hb,hab'⟩ := adj_erase_of_surviving_sat (fun v hv => hM.deg_le hv) Y ha.1 (hsat a ha.1 ha.2) hab
      exact ⟨hb,Relation.EqvGen.trans _ _ _ ha.2 (Relation.EqvGen.rel _ _ hab')⟩
    have hpath (a b : V) (hab : M.SameComponent a b) : C a ↔ C b := by
      induction hab with
      | rel a b h => exact ⟨hclosed a b h,hclosed b a (Mole.adj_symmetric M h)⟩
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
    obtain ⟨u,hu,hzu,hu4⟩ := hM.unsat z (mem_sdiff.mp hz).1
    have huC := (hpath z u hzu).mp ⟨hz,Relation.EqvGen.refl z⟩
    have he := deg_eraseAtoms_add_removed M Y (mem_sdiff.mp huC.1).2
    have hfour := hsat u huC.1 huC.2
    have hcap := hM.deg_le hu
    apply hu4
    omega

/-- An unsaturated atom of a nonempty `PMol` is removable by operation (a). -/
theorem PMol.exists_removable (h : PMol B M) (hne : M.atoms ≠ ∅) :
    ∃ v ∈ M.atoms, (v ∉ B ∧ M.deg v ≤ 3) ∨ (v ∈ B ∧ M.deg v ≤ 1) := by
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨u, hu, _, hne'⟩ := h.unsat w hw
  refine ⟨u, hu, ?_⟩
  have hle := h.deg_le hu
  unfold cap at hle hne'
  by_cases hB : u ∈ B
  · simp only [hB, if_true] at hle hne'
    exact Or.inr ⟨hB, by omega⟩
  · simp only [hB, if_false] at hle hne'
    exact Or.inl ⟨hB, by omega⟩

end WaveTurbulence.FinalCountG8.P101
