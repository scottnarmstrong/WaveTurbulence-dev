/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GenClass1
import Mathlib.Tactic
/-! The pattern partition of the literal time domain. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Type} [Fintype Q] [DecidableEq Q] {K : Q → ℕ}

/-- The literal time domain (layers and strict parent-child order). -/
def Om0 (ch : ι → ι → Prop) (ls cap : ι → ℝ) : Set (ι → ℝ) :=
  {t | (∀ v, t v ∈ Icc (ls v) (ls v + 1)) ∧ (∀ v, t v < cap v) ∧ ∀ a b, ch a b → t a < t b}

theorem pattern_partition {k : ℕ} (ch : ι → ι → Prop) (ua va : Jr K → ι) (ls cap : ι → ℝ)
    (σ : Fin k ≃ Jr K) (D : ℝ) (hbox : ∀ v, 0 ≤ ls v ∧ ls v + 1 ≤ D)
    (hval : ∀ t ∈ Om0 ch ls cap, ∀ q, NP (fun j : Fin (K q) => max (t (ua ⟨q, j⟩)) (t (va ⟨q, j⟩))))
    (xv : (Jr K → Bool) → Fin k → ι) (hxv : ∀ θ i, xv θ i = xθ ua va θ (σ i)) (t : ι → ℝ) :
    (t ∈ Om0 ch ls cap → ∃! θ : Jr K → Bool,
      t ∈ OmegaC ls cap (ltθ ch ua va θ) (leθ ua va θ) (xv θ) (RvOf σ D)) ∧
    ∀ θ : Jr K → Bool, t ∈ OmegaC ls cap (ltθ ch ua va θ) (leθ ua va θ) (xv θ) (RvOf σ D) → t ∈ Om0 ch ls cap := by
  constructor
  · intro ht
    refine ⟨patOf ua va t, ⟨ht.1, ht.2.1, ?_, ?_, ?_⟩, ?_⟩
    · intro a b hab
      rcases hab with hab | ⟨j, hj, rfl, rfl⟩
      · exact ht.2.2 a b hab
      · simp only [patOf, decide_eq_false_iff_not] at hj
        exact not_le.mp hj
    · rintro a b ⟨j, hj, rfl, rfl⟩
      simpa [patOf] using hj
    · intro q
      have hv := hval t ht q
      have heq : (fun j : Fin (K q) => t (xv (patOf ua va t) (σ.symm ⟨q, j⟩))) =
          fun j : Fin (K q) => max (t (ua ⟨q, j⟩)) (t (va ⟨q, j⟩)) := by
        funext j
        rw [hxv, Equiv.apply_symm_apply]
        unfold xθ patOf
        by_cases h : t (va ⟨q, j⟩) ≤ t (ua ⟨q, j⟩)
        · simp [h]
        · simp [h, (not_le.mp h).le]
      show (fun j : Fin (K q) => t (xv (patOf ua va t) (σ.symm ⟨q, j⟩))) ∈ Vset (K q) D
      rw [heq]
      refine ⟨hv, fun j => ?_⟩
      have h1 := ht.1 (ua ⟨q, j⟩)
      have h2 := ht.1 (va ⟨q, j⟩)
      have h3 := hbox (ua ⟨q, j⟩)
      have h4 := hbox (va ⟨q, j⟩)
      constructor
      · exact le_max_of_le_left (h3.1.trans h1.1)
      · exact max_le (h1.2.trans h3.2) (h2.2.trans h4.2)
    · intro θ hθ
      funext j
      by_cases hj : θ j = true
      · have := hθ.2.2.2.1 (va j) (ua j) ⟨j, hj, rfl, rfl⟩
        simp [patOf, hj, this]
      · have hj' : θ j = false := by simpa using hj
        have := hθ.2.2.1 (ua j) (va j) (Or.inr ⟨j, hj', rfl, rfl⟩)
        simp [patOf, hj', not_le.mpr this]
  · intro θ hθ
    exact ⟨hθ.1, hθ.2.1, fun a b hab => hθ.2.2.1 a b (Or.inl hab)⟩

end WaveTurbulence.Ladder
