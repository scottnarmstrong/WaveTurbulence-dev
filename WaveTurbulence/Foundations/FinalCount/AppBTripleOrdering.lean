/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceSigns
import Mathlib.Tactic

/-! # Ordering three source signs into the basiccount(2) profile -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- No three signs are equal at a source degree-three atom. Thus two have
the same orientation and the remaining one has the opposite orientation. -/
theorem appb_three_sign_order (σ : Fin 3 → ℤˣ)
    (hplus : ¬∀ i,σ i = 1) (hminus : ¬∀ i,σ i = -1) :
    ∃ i j k : Fin 3,i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ σ i = σ k ∧ σ i ≠ σ j := by
  rcases Int.units_eq_one_or (σ 0) with h0 | h0
  all_goals rcases Int.units_eq_one_or (σ 1) with h1 | h1
  all_goals rcases Int.units_eq_one_or (σ 2) with h2 | h2
  · apply False.elim
    apply hplus
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · exact ⟨0,2,1,by decide,by decide,by decide,by rw [h0,h1],by rw [h0,h2]; decide⟩
  · exact ⟨0,1,2,by decide,by decide,by decide,by rw [h0,h2],by rw [h0,h1]; decide⟩
  · exact ⟨1,0,2,by decide,by decide,by decide,by rw [h1,h2],by rw [h1,h0]; decide⟩
  · exact ⟨1,0,2,by decide,by decide,by decide,by rw [h1,h2],by rw [h1,h0]; decide⟩
  · exact ⟨0,1,2,by decide,by decide,by decide,by rw [h0,h2],by rw [h0,h1]; decide⟩
  · exact ⟨0,2,1,by decide,by decide,by decide,by rw [h0,h1],by rw [h0,h2]; decide⟩
  · apply False.elim
    apply hminus
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

theorem appb_units_eq_neg_of_ne (σ τ : ℤˣ) (h : σ ≠ τ) : τ = -σ := by
  rcases Int.units_eq_one_or σ with rfl | rfl
  all_goals rcases Int.units_eq_one_or τ with rfl | rfl
  all_goals simp_all

theorem appb_signed_triple_momentum {E : Type*} [AddCommGroup E]
    (σ : ℤˣ) (x y z c : E)
    (h : (σ : ℤ) • x-(σ : ℤ) • y+(σ : ℤ) • z = c) :
    x-y+z = ((σ⁻¹ : ℤˣ) : ℤ) • c := by
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simpa using h
  · have hh := congrArg Neg.neg h
    simpa [neg_add,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hh

theorem appb_signed_triple_energy (σ : ℤˣ) (a b c β W : ℝ)
    (h : |(σ : ℤ)*a-(σ : ℤ)*b+(σ : ℤ)*c-β| ≤ W) :
    |a-b+c-((σ⁻¹ : ℤˣ) : ℤ)*β| ≤ W := by
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simpa using h
  · have he : |a-b+c-(((-1 : ℤˣ)⁻¹ : ℤˣ) : ℤ)*β| =
        |(-1 : ℤ)*a-(-1 : ℤ)*b+(-1 : ℤ)*c-β| := by
      rw [← abs_neg]
      congr 1
      simp
      ring
    rw [he]
    exact h

end WaveTurbulence.Mole
