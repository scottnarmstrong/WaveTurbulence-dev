/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ShapeSlots

/-! # Literal source clock slots under the M9 family time bijection -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {I : ℕ}

theorem shapeFamily_normal_iff (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) :
    (shapeFamily X A).nor i = true ↔ (X i).IsBad = false := by
  cases h : (X i).IsBad <;> simp only [shapeFamily,h,Bool.not_true,Bool.not_false,Bool.false_eq_true,
    Bool.true_eq_false]

theorem familySlotEquiv_u (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I)
    (hn : (X i).IsBad = false) (hNor : (shapeFamily X A).nor i = true) (c : Fin 3) :
    familySlotEquiv X A i ((A i).uSlot hn c) = ((shapeFamily X A).uSlot i hNor c).2 := Fin.ext rfl

theorem familyTimeEquiv_x0 (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) :
    familyTimeEquiv X A (.inl ⟨i,0⟩) = ⟨i,(A i).x0⟩ := rfl

theorem familyTimeEquiv_x (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) (j : Fin (A i).m) :
    familyTimeEquiv X A (.inl ⟨i,j.succ⟩) = ⟨i,(A i).xSlot j⟩ := rfl

theorem familyTimeEquiv_y (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) (j : Fin (A i).m) :
    familyTimeEquiv X A (.inr (.inl ⟨i,j⟩)) = ⟨i,(A i).ySlot j⟩ := rfl

theorem familyTimeEquiv_u (X : Fin I → VineType) (A : ∀ i, Shape (X i))
    (i : {i : Fin I // (shapeFamily X A).nor i = true}) (c : Fin 3) :
    familyTimeEquiv X A (.inr (.inr ⟨i,c⟩)) =
      ⟨i.1,(A i.1).uSlot ((shapeFamily_normal_iff X A i.1).mp i.2) c⟩ := rfl

/-- Pull the source clocks back to the actual atom slots. -/
noncomputable def familyClock (X : Fin I → VineType) (A : ∀ i, Shape (X i))
    (τ : (shapeFamily X A).TVar → ℝ) (z : Σ i, Fin (A i).n) : ℝ :=
  τ ((familyTimeEquiv X A).symm z)

theorem familyClock_x0 (X : Fin I → VineType) (A : ∀ i, Shape (X i))
    (τ : (shapeFamily X A).TVar → ℝ) (i : Fin I) :
    familyClock X A τ ⟨i,(A i).x0⟩ = τ (.inl ⟨i,0⟩) :=
  congrArg τ ((familyTimeEquiv X A).symm_apply_eq.mpr (familyTimeEquiv_x0 X A i).symm)

theorem familyClock_x (X : Fin I → VineType) (A : ∀ i, Shape (X i))
    (τ : (shapeFamily X A).TVar → ℝ) (i : Fin I) (j : Fin (A i).m) :
    familyClock X A τ ⟨i,(A i).xSlot j⟩ = τ (.inl ⟨i,j.succ⟩) :=
  congrArg τ ((familyTimeEquiv X A).symm_apply_eq.mpr (familyTimeEquiv_x X A i j).symm)

theorem familyClock_y (X : Fin I → VineType) (A : ∀ i, Shape (X i))
    (τ : (shapeFamily X A).TVar → ℝ) (i : Fin I) (j : Fin (A i).m) :
    familyClock X A τ ⟨i,(A i).ySlot j⟩ = τ (.inr (.inl ⟨i,j⟩)) :=
  congrArg τ ((familyTimeEquiv X A).symm_apply_eq.mpr (familyTimeEquiv_y X A i j).symm)

theorem familyClock_u (X : Fin I → VineType) (A : ∀ i, Shape (X i))
    (τ : (shapeFamily X A).TVar → ℝ)
    (i : {i : Fin I // (shapeFamily X A).nor i = true}) (c : Fin 3) :
    familyClock X A τ ⟨i.1,(A i.1).uSlot ((shapeFamily_normal_iff X A i.1).mp i.2) c⟩ =
      τ (.inr (.inr ⟨i,c⟩)) :=
  congrArg τ ((familyTimeEquiv X A).symm_apply_eq.mpr (familyTimeEquiv_u X A i c).symm)

end WaveTurbulence.VineEstS2
