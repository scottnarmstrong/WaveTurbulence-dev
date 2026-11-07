/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! **FINALCOUNT-ASSEMBLY, M7: greedy runs.**  If every step of a relation strictly decreases a natural measure
(`#bonds + #ε-atoms`), then from every state there is a reachable state with no step enabled; this gives the phases
2-4 of a run ("do steps until the stop predicate, a negation of enabledness, holds"). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountAsm

theorem exists_stuck {α : Type*} (R : α → α → Prop) (μ : α → ℕ) (hμ : ∀ a b, R a b → μ b < μ a) (a : α) :
    ∃ b, Relation.ReflTransGen R a b ∧ ∀ c, ¬ R b c := by
  induction h : μ a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hs : ∃ c, R a c
    · obtain ⟨c, hc⟩ := hs
      obtain ⟨b, hb, hstuck⟩ := ih (μ c) (h ▸ hμ a c hc) c rfl
      exact ⟨b, Relation.ReflTransGen.head hc hb, hstuck⟩
    · push Not at hs
      exact ⟨a, Relation.ReflTransGen.refl, hs⟩

/-- With a side invariant `P` preserved by the steps. -/
theorem exists_stuck_inv {α : Type*} (R : α → α → Prop) (μ : α → ℕ) (P : α → Prop)
    (hμ : ∀ a b, R a b → μ b < μ a) (hP : ∀ a b, R a b → P a → P b) (a : α) (ha : P a) :
    ∃ b, Relation.ReflTransGen R a b ∧ P b ∧ ∀ c, ¬ R b c := by
  obtain ⟨b, hb, hs⟩ := exists_stuck R μ hμ a
  refine ⟨b, hb, ?_, hs⟩
  clear hs
  induction hb with
  | refl => exact ha
  | tail _ h2 ih => exact hP _ _ h2 ih

end WaveTurbulence.FinalCountAsm
