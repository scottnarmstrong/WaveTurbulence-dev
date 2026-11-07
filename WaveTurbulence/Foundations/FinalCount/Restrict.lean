/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutRank
/-! Restriction of a molecule to a union of components (FINALCOUNT-G2, infrastructure for the removal
steps of Operations 1 and 2 of DH23 §9.3): the molecule on the atoms satisfying `P`, with the darts at them. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) (P : V → Prop) [DecidablePred P]

/-- The darts at the atoms satisfying `P`. -/
abbrev PDart := {x : D // P (M.atom x)}

/-- `P` is closed under adjacency. -/
def PClosed : Prop := ∀ x, P (M.atom x) → P (M.atom (M.mate x))

theorem PClosed.neg (h : PClosed M P) : PClosed M (fun a => ¬ P a) := by
  intro x hx hy
  exact hx (by simpa [M.mate_mate] using h (M.mate x) hy)

/-- The sub-molecule on the atoms satisfying `P`. -/
def restrictP (h : PClosed M P) : Molecule V (PDart M P) where
  atoms := M.atoms.filter P
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1, h x.1 x.2⟩
  out := fun x => M.out x.1
  atom_mem := fun x => Finset.mem_filter.mpr ⟨M.atom_mem x.1, x.2⟩
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x e => M.mate_ne x.1 (congrArg Subtype.val e)
  out_mate := fun x => M.out_mate x.1

variable (h : PClosed M P)
include h

theorem restrictP_dartsAt {a : V} (ha : P a) :
    (restrictP M P h).dartsAt a = (M.dartsAt a).subtype (fun x => P (M.atom x)) := by
  ext x
  simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_subtype]
  rfl

theorem restrictP_deg {a : V} (ha : P a) : (restrictP M P h).deg a = M.deg a := by
  unfold Molecule.deg
  rw [restrictP_dartsAt M P h ha, Finset.card_subtype, Finset.filter_true_of_mem]
  intro x hx
  have : M.atom x = a := by simpa [Molecule.dartsAt] using hx
  rw [this]; exact ha

theorem restrictP_atoms_card :
    (restrictP M P h).atoms.card + (restrictP M (fun a => ¬ P a) h.neg).atoms.card = M.atoms.card := by
  show (M.atoms.filter P).card + (M.atoms.filter (fun a => ¬ P a)).card = M.atoms.card
  exact Finset.card_filter_add_card_filter_not P

omit h in
theorem card_filter_subtype' {α : Type*} [Fintype α] (p g : α → Prop) [DecidablePred p] [DecidablePred g] :
    (Finset.univ.filter fun x : {x // p x} => g x.1).card = (Finset.univ.filter fun x : α => p x ∧ g x).card := by
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨x.2, hx⟩
  · intro x _ y _ e; exact Subtype.ext e
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨⟨x, hx.1⟩, by simpa using hx.2, rfl⟩

theorem restrictP_bonds_card :
    (restrictP M P h).bonds.card + (restrictP M (fun a => ¬ P a) h.neg).bonds.card = M.bonds.card := by
  unfold Molecule.bonds
  show (Finset.univ.filter fun x : PDart M P => M.out x.1 = true).card +
    (Finset.univ.filter fun x : PDart M (fun a => ¬ P a) => M.out x.1 = true).card = _
  rw [card_filter_subtype' (fun x : D => P (M.atom x)) (fun x => M.out x = true),
    card_filter_subtype' (fun x : D => ¬ P (M.atom x)) (fun x => M.out x = true)]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hy.1 hx.1


theorem PClosed.adj_iff {u w : V} (hadj : M.Adj u w) : P u ↔ P w := by
  obtain ⟨x, hx1, hx2⟩ := hadj
  constructor
  · intro hu; rw [← hx2]; exact h x (hx1 ▸ hu)
  · intro hw
    have := h (M.mate x) (by rw [hx2]; exact hw)
    rwa [M.mate_mate, hx1] at this

theorem PClosed.sc_iff {u w : V} (hsc : M.SameComponent u w) : P u ↔ P w := by
  induction hsc with
  | rel _ _ hr => exact PClosed.adj_iff M P h hr
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem restrictP_adj_of {u w : V} (hu : P u) (hadj : M.Adj u w) : (restrictP M P h).Adj u w := by
  obtain ⟨x, hx1, hx2⟩ := hadj
  exact ⟨⟨x, hx1 ▸ hu⟩, hx1, hx2⟩

theorem restrictP_sc_of {u w : V} (hsc : M.SameComponent u w) (hu : P u) :
    (restrictP M P h).SameComponent u w := by
  revert hu
  induction hsc with
  | rel a b hr => exact fun hu => Relation.EqvGen.rel _ _ (restrictP_adj_of M P h hu hr)
  | refl _ => exact fun _ => Relation.EqvGen.refl _
  | symm a b hab ih =>
    exact fun hb => Relation.EqvGen.symm _ _ (ih ((PClosed.sc_iff M P h hab).2 hb))
  | trans a b c hab hbc ih1 ih2 =>
    exact fun hu => Relation.EqvGen.trans _ _ _ (ih1 hu) (ih2 ((PClosed.sc_iff M P h hab).1 hu))

end WaveTurbulence.FinalCount
