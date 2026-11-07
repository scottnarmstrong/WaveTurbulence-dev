/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Restrict
/-! Restriction, part 2 (FINALCOUNT-G2 infrastructure): the number of components is additive. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed M P)

theorem restrictP_atom_mem {a : V} (ha : a ∈ (restrictP M P h).atoms) : a ∈ M.atoms ∧ P a :=
  Finset.mem_filter.mp ha

/-- The inclusion of the components of `restrictP M P` into those of `M`. -/
def inclQ : Quot (fun u w : (restrictP M P h).atoms => (restrictP M P h).Adj u.1 w.1) →
    Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
  Quot.lift (fun a => Quot.mk _ ⟨a.1, (restrictP_atom_mem M P h a.2).1⟩)
    (fun a b hab => Quot.sound (by
      obtain ⟨x, hx1, hx2⟩ := hab
      exact ⟨x.1, hx1, hx2⟩))

theorem inclQ_injective : Function.Injective (inclQ M P h) := by
  intro q q' e
  induction q using Quot.ind with
  | _ a =>
  induction q' using Quot.ind with
  | _ b =>
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have e' := (quot_mk_eq_iff M a b (restrictP_atom_mem M P h ha).1 (restrictP_atom_mem M P h hb).1).1 e
  exact (quot_mk_eq_iff _ a b ha hb).2 (restrictP_sc_of M P h e' (restrictP_atom_mem M P h ha).2)

theorem numComponents_restrictP_add :
    (restrictP M P h).numComponents + (restrictP M (fun a => ¬ P a) h.neg).numComponents = M.numComponents := by
  classical
  unfold Molecule.numComponents
  rw [← Nat.card_sum]
  haveI : Finite (restrictP M P h).atoms := inferInstance
  let Φ : Quot (fun u w : (restrictP M P h).atoms => (restrictP M P h).Adj u.1 w.1) ⊕
      Quot (fun u w : (restrictP M (fun a => ¬ P a) h.neg).atoms => (restrictP M (fun a => ¬ P a) h.neg).Adj u.1 w.1) →
      Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
    Sum.elim (inclQ M P h) (inclQ M (fun a => ¬ P a) h.neg)
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro (q | q) (q' | q') e
      · exact congrArg Sum.inl (inclQ_injective M P h e)
      · exfalso
        induction q using Quot.ind with
        | _ a =>
        induction q' using Quot.ind with
        | _ b =>
        obtain ⟨a, ha⟩ := a
        obtain ⟨b, hb⟩ := b
        have e' := (quot_mk_eq_iff M a b (restrictP_atom_mem M P h ha).1
          (restrictP_atom_mem M (fun a => ¬ P a) h.neg hb).1).1 e
        exact (restrictP_atom_mem M (fun a => ¬ P a) h.neg hb).2
          ((PClosed.sc_iff M P h e').1 (restrictP_atom_mem M P h ha).2)
      · exfalso
        induction q using Quot.ind with
        | _ a =>
        induction q' using Quot.ind with
        | _ b =>
        obtain ⟨a, ha⟩ := a
        obtain ⟨b, hb⟩ := b
        have e' := (quot_mk_eq_iff M a b (restrictP_atom_mem M (fun a => ¬ P a) h.neg ha).1
          (restrictP_atom_mem M P h hb).1).1 e
        exact (restrictP_atom_mem M (fun a => ¬ P a) h.neg ha).2
          ((PClosed.sc_iff M P h e').2 (restrictP_atom_mem M P h hb).2)
      · exact congrArg Sum.inr (inclQ_injective M (fun a => ¬ P a) h.neg e)
    · intro q
      induction q using Quot.ind with
      | _ a =>
      obtain ⟨a, ha⟩ := a
      by_cases hP : P a
      · exact ⟨Sum.inl (Quot.mk _ ⟨a, Finset.mem_filter.mpr ⟨ha, hP⟩⟩), rfl⟩
      · exact ⟨Sum.inr (Quot.mk _ ⟨a, Finset.mem_filter.mpr ⟨ha, hP⟩⟩), rfl⟩
  exact Nat.card_congr (Equiv.ofBijective Φ hbij)

end WaveTurbulence.FinalCount
