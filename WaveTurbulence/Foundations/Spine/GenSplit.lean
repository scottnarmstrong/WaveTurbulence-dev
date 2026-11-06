/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimeLemma
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic
/-! Enumeration of a forest vertex set `ι = X ⊔ Y` with `Y` ordered so that parents come later. -/
@[expose] public section
open Finset Function
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_split (X : Finset ι) (lt : ι → ι → Prop) (dep : ι → ℕ)
    (hdep : ∀ a b, lt a b → dep b < dep a) (huniq : ∀ a b b', lt a b → lt a b' → b = b') :
    ∃ (k m : ℕ) (e : ι ≃ Fin k ⊕ Fin m) (par : Par m), ParOK par ∧
      (∀ i, e.symm (Sum.inl i) ∈ X) ∧ (∀ j, e.symm (Sum.inr j) ∉ X) ∧
      (∀ j j', par j = some j' ↔ lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j'))) := by
  let Xs := {a : ι // a ∈ X}
  let Ys := {a : ι // a ∉ X}
  let eX : Xs ≃ Fin (Fintype.card Xs) := Fintype.equivFin Xs
  let eY0 : Ys ≃ Fin (Fintype.card Ys) := Fintype.equivFin Ys
  let N := ∑ a, dep a + 1
  let f : Fin (Fintype.card Ys) → ℕ := fun j => N - dep (eY0.symm j).1
  let σ := Tuple.sort f
  have hσ : Monotone (f ∘ σ) := Tuple.monotone_sort f
  let eY : Ys ≃ Fin (Fintype.card Ys) := eY0.trans σ.symm
  have hdepN : ∀ a, dep a < N := fun a => by
    have := Finset.single_le_sum (f := dep) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    omega
  let e : ι ≃ Fin (Fintype.card Xs) ⊕ Fin (Fintype.card Ys) :=
    (Equiv.sumCompl (fun a => a ∈ X)).symm.trans (Equiv.sumCongr eX eY)
  have hY : ∀ j, e.symm (Sum.inr j) = (eY.symm j).1 := fun j => by
    simp [e]
  have hX : ∀ i, e.symm (Sum.inl i) = (eX.symm i).1 := fun i => by
    simp [e]
  -- parent in `Y`
  let par : Par (Fintype.card Ys) := fun j =>
    if h : ∃ j', lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')) then some h.choose else none
  have hparK : ∀ j j', lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')) → j < j' := by
    intro j j' h
    by_contra hnot
    have hle : j' ≤ j := not_lt.mp hnot
    have h1 : (f ∘ σ) j' ≤ (f ∘ σ) j := hσ hle
    have h2 := hdep _ _ h
    have e1 : (f ∘ σ) j = N - dep (e.symm (Sum.inr j)) := by
      simp only [Function.comp_apply, f, hY]
      rfl
    have e2 : (f ∘ σ) j' = N - dep (e.symm (Sum.inr j')) := by
      simp only [Function.comp_apply, f, hY]
      rfl
    have := hdepN (e.symm (Sum.inr j))
    have := hdepN (e.symm (Sum.inr j'))
    omega
  refine ⟨Fintype.card Xs, Fintype.card Ys, e, par, ?_, ?_, ?_, ?_⟩
  · intro j j' h
    simp only [par] at h
    split_ifs at h with hex
    · have := hex.choose_spec
      have hh : hex.choose = j' := by
        have := Option.some.inj h; exact this
      rw [← hh]; exact hparK _ _ this
  · intro i; rw [hX]; exact (eX.symm i).2
  · intro j; rw [hY]; exact (eY.symm j).2
  · intro j j'
    simp only [par]
    constructor
    · intro h
      split_ifs at h with hex
      · have hh : hex.choose = j' := Option.some.inj h
        rw [← hh]; exact hex.choose_spec
    · intro h
      have hex : ∃ j', lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')) := ⟨j', h⟩
      rw [dite_eq_left hex]
      have := hex.choose_spec
      have : e.symm (Sum.inr hex.choose) = e.symm (Sum.inr j') := huniq _ _ _ this h
      rw [e.symm.injective.eq_iff] at this
      simp at this
      rw [this]

theorem exists_split_with (X : Finset ι) {k : ℕ} (eX : {a // a ∈ X} ≃ Fin k) (lt : ι → ι → Prop) (dep : ι → ℕ)
    (hdep : ∀ a b, lt a b → dep b < dep a) (huniq : ∀ a b b', lt a b → lt a b' → b = b') :
    ∃ (m : ℕ) (e : ι ≃ Fin k ⊕ Fin m) (par : Par m), ParOK par ∧
      (∀ i, e.symm (Sum.inl i) = (eX.symm i).1) ∧ (∀ j, e.symm (Sum.inr j) ∉ X) ∧
      (∀ j j', par j = some j' ↔ lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j'))) := by
  let Xs := {a : ι // a ∈ X}
  let Ys := {a : ι // a ∉ X}
  let eY0 : Ys ≃ Fin (Fintype.card Ys) := Fintype.equivFin Ys
  let N := ∑ a, dep a + 1
  let f : Fin (Fintype.card Ys) → ℕ := fun j => N - dep (eY0.symm j).1
  let σ := Tuple.sort f
  have hσ : Monotone (f ∘ σ) := Tuple.monotone_sort f
  let eY : Ys ≃ Fin (Fintype.card Ys) := eY0.trans σ.symm
  have hdepN : ∀ a, dep a < N := fun a => by
    have := Finset.single_le_sum (f := dep) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    omega
  let e : ι ≃ Fin k ⊕ Fin (Fintype.card Ys) :=
    (Equiv.sumCompl (fun a => a ∈ X)).symm.trans (Equiv.sumCongr eX eY)
  have hY : ∀ j, e.symm (Sum.inr j) = (eY.symm j).1 := fun j => by
    simp [e]
  have hX : ∀ i, e.symm (Sum.inl i) = (eX.symm i).1 := fun i => by
    simp [e]
  -- parent in `Y`
  let par : Par (Fintype.card Ys) := fun j =>
    if h : ∃ j', lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')) then some h.choose else none
  have hparK : ∀ j j', lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')) → j < j' := by
    intro j j' h
    by_contra hnot
    have hle : j' ≤ j := not_lt.mp hnot
    have h1 : (f ∘ σ) j' ≤ (f ∘ σ) j := hσ hle
    have h2 := hdep _ _ h
    have e1 : (f ∘ σ) j = N - dep (e.symm (Sum.inr j)) := by
      simp only [Function.comp_apply, f, hY]
      rfl
    have e2 : (f ∘ σ) j' = N - dep (e.symm (Sum.inr j')) := by
      simp only [Function.comp_apply, f, hY]
      rfl
    have := hdepN (e.symm (Sum.inr j))
    have := hdepN (e.symm (Sum.inr j'))
    omega
  refine ⟨Fintype.card Ys, e, par, ?_, ?_, ?_, ?_⟩
  · intro j j' h
    simp only [par] at h
    split_ifs at h with hex
    · have := hex.choose_spec
      have hh : hex.choose = j' := by
        have := Option.some.inj h; exact this
      rw [← hh]; exact hparK _ _ this
  · intro i; rw [hX]
  · intro j; rw [hY]; exact (eY.symm j).2
  · intro j j'
    simp only [par]
    constructor
    · intro h
      split_ifs at h with hex
      · have hh : hex.choose = j' := Option.some.inj h
        rw [← hh]; exact hex.choose_spec
    · intro h
      have hex : ∃ j', lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')) := ⟨j', h⟩
      rw [dite_eq_left hex]
      have := hex.choose_spec
      have : e.symm (Sum.inr hex.choose) = e.symm (Sum.inr j') := huniq _ _ _ this h
      rw [e.symm.injective.eq_iff] at this
      simp at this
      rw [this]

end WaveTurbulence.Ladder
