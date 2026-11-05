/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! # A finite even-weight charging ledger
Combinatorial helper for TARGET `cnblock`: zero-weight components are
injected into positive isolated components; positive weights are even.
-/

public section
namespace WaveTurbulence.Mole
open Finset

theorem even_weight_charge_bound {C : Type*} [DecidableEq C] (all : Finset C)
    (weight : C → ℕ) (R : ℕ) (hR : 1 ≤ R)
    (heven : ∀ c ∈ all, Even (weight c)) (hbudget : ∑ c ∈ all, weight c ≤ 2*R)
    (charge : {c // c ∈ all ∧ weight c = 0} → {c // c ∈ all ∧ 0 < weight c})
    (hinj : Function.Injective charge) :
    all.card ≤ 2*R ∧ (all.card = 2*R → ∃ c ∈ all, weight c = 0) := by
  classical
  let P := all.filter (fun c => 0 < weight c)
  let Z := all.filter (fun c => weight c = 0)
  have hcharge : Z.card ≤ P.card := by
    let f : ↥Z → ↥P := fun c =>
      ⟨(charge ⟨c.1,(mem_filter.mp c.2)⟩).1,mem_filter.mpr (charge ⟨c.1,mem_filter.mp c.2⟩).2⟩
    apply Finset.card_le_card_of_injective (f := f)
    intro x y he
    apply Subtype.ext
    have heval : (charge ⟨x.1,mem_filter.mp x.2⟩).1 =
        (charge ⟨y.1,mem_filter.mp y.2⟩).1 := congrArg (fun z : ↥P => z.1) he
    have hxy := hinj (Subtype.ext heval)
    exact congrArg (fun z : {c // c ∈ all ∧ weight c = 0} => z.1) hxy
  have hpart : P.card+Z.card = all.card := by
    have h := all.card_filter_add_card_filter_not (fun c => 0 < weight c)
    simpa only [Nat.not_lt,Nat.le_zero,P,Z] using h
  have hp : 2*P.card ≤ ∑ c ∈ all, weight c := by
    calc
      _ = ∑ _c ∈ P, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ P, weight c := by
        apply sum_le_sum
        intro c hc
        obtain ⟨hc,hpos⟩ := mem_filter.mp hc
        obtain ⟨n,hn⟩ := heven c hc
        omega
      _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
  have hpR : P.card ≤ R := by omega
  refine ⟨by omega,?_⟩
  intro heq
  have hz : Z.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨c,hc⟩ := hz
  exact ⟨c,(mem_filter.mp hc).1,(mem_filter.mp hc).2⟩

end WaveTurbulence.Mole
