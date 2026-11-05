/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! # Pairing parity for the generalized gardens in TARGET `cnblock`
A finite set completely paired without fixed points has even cardinality.
No signs or bond orientations are needed.
-/

public section
namespace WaveTurbulence.Mole
open Finset

theorem involution_card_even {L : Type*} [Fintype L]
    (pair : L → L) (hpair : Function.Involutive pair) (hne : ∀ l, pair l ≠ l) :
    Even (Fintype.card L) := by
  classical
  let idx := Fintype.equivFin L
  let P : L → Prop := fun x => (idx x).val < (idx (pair x)).val
  have hp : ∀ x, P (pair x) ↔ ¬ P x := by
    intro x
    have hne' : (idx x).val ≠ (idx (pair x)).val := by
      intro he
      exact hne x ((idx.injective (Fin.ext he)).symm)
    dsimp only [P]
    rw [hpair x]
    omega
  have hc : (univ.filter P).card = (univ.filter (fun x => ¬ P x)).card := by
    apply Finset.card_bij (fun x _hx => pair x)
    · intro x hx
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      intro hf
      exact (hp x).mp hf (mem_filter.mp hx).2
    · intro x hx y hy he
      exact hpair.injective he
    · intro y hy
      refine ⟨pair y,mem_filter.mpr ⟨mem_univ _,(hp y).mpr (mem_filter.mp hy).2⟩,hpair y⟩
  have hs := (univ : Finset L).card_filter_add_card_filter_not P
  rw [card_univ,← hc] at hs
  exact ⟨(univ.filter P).card,hs.symm⟩

/-- An odd family cannot be closed under a fixed-point-free actual pairing. -/
theorem odd_fiber_has_external_pair {L T : Type*} [Fintype L] [DecidableEq T]
    (root : L → T) (pair : L → L) (hpair : Function.Involutive pair)
    (hne : ∀ l, pair l ≠ l) (t : T)
    (hodd : Odd (Fintype.card {l : L // root l = t})) :
    ∃ l : L, root l = t ∧ root (pair l) ≠ t := by
  classical
  by_contra hn
  have hclosed : ∀ l, root l = t → root (pair l) = t := by
    intro l hl
    by_contra hp
    exact hn ⟨l,hl,hp⟩
  let f : {l : L // root l = t} → {l : L // root l = t} :=
    fun l => ⟨pair l.1,hclosed l.1 l.2⟩
  have hf : Function.Involutive f := fun l => Subtype.ext (hpair l.1)
  have he := involution_card_even f hf (fun l he => hne l.1 (congrArg Subtype.val he))
  exact (Nat.not_even_iff_odd.mpr hodd) he

end WaveTurbulence.Mole
