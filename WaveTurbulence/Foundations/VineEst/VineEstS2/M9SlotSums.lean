/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ClockSlots

/-! # Exact finite source slot decomposition -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {I : ℕ}

private theorem fintype_sum_irrel {α E : Type*} [AddCommMonoid E]
    (F₁ F₂ : Fintype α) (f : α → E) :
    @Finset.sum α E _ (@Finset.univ α F₁) f = @Finset.sum α E _ (@Finset.univ α F₂) f := by
  cases Subsingleton.elim F₁ F₂
  rfl

open Classical in
/-- All atoms are counted exactly once: joint, paired rung slots, and normal
core slots. This uses the actual coordinate bijection, not a count alone. -/
theorem sum_familySlots {E : Type*} [AddCommGroup E]
    (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (f : (Σ i, Fin (A i).n) → E) :
    (∑ v, f v) =
      (∑ i, (f ⟨i,(A i).x0⟩ + ∑ j : Fin (A i).m,
        (f ⟨i,(A i).xSlot j⟩ + f ⟨i,(A i).ySlot j⟩))) +
      ∑ i : {i : Fin I // (shapeFamily X A).nor i = true}, ∑ c : Fin 3,
        f ⟨i.1,(A i.1).uSlot ((shapeFamily_normal_iff X A i.1).mp i.2) c⟩ := by
  have ht : (∑ p : Σ i : Fin I, Fin ((A i).m+1), f (familyTimeEquiv X A (.inl p))) =
      ∑ i, (f ⟨i,(A i).x0⟩ + ∑ j : Fin (A i).m, f ⟨i,(A i).xSlot j⟩) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succ]
    rfl
  have hy : (∑ p : Σ i : Fin I, Fin (A i).m, f (familyTimeEquiv X A (.inr (.inl p)))) =
      ∑ i, ∑ j : Fin (A i).m, f ⟨i,(A i).ySlot j⟩ := by
    rw [Fintype.sum_sigma]
    rfl
  have hn : (∑ p : Σ i : {i : Fin I // (shapeFamily X A).nor i = true}, Fin 3,
      f (familyTimeEquiv X A (.inr (.inr p)))) =
      ∑ i : {i : Fin I // (shapeFamily X A).nor i = true}, ∑ c : Fin 3,
        f ⟨i.1,(A i.1).uSlot ((shapeFamily_normal_iff X A i.1).mp i.2) c⟩ := by
    rw [Fintype.sum_sigma]
    rfl
  calc
    _ = ∑ τ, f (familyTimeEquiv X A τ) := ((familyTimeEquiv X A).sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
      calc
        _ = _ := by
          convert congrArg₂ (fun x y : E => x+y) ht (congrArg₂ (fun x y : E => x+y) hy hn) using 1
          congr 2
          exact fintype_sum_irrel _ _ _
        _ = _ := by
          simp_rw [Finset.sum_add_distrib]
          abel

end WaveTurbulence.VineEstS2
