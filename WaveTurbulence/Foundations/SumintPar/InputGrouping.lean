/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ShapeFacts
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Exact grouping of source input variables into linear, pair and cubic factors

The source time index already has one coordinate per momentum input.
Matching its t, s and normal coordinates to x, y and u gives a literal
bijection. The subsequent grouping has an explicit inverse and introduces
no Jacobian or combinatorial multiplicity into a lattice sum.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- The momentum slot corresponding to each source input-time coordinate. -/
@[expose] def inputTimeSlot (S : SumintShape) : S.TVar → S.VIdx
  | .inl ⟨i,j⟩ => ⟨i,⟨j,by have hj := j.isLt; unfold SumintShape.n; omega⟩⟩
  | .inr (.inl ⟨i,j⟩) => S.ySlot i j
  | .inr (.inr ⟨i,j⟩) => S.uSlot i.1 i.2 j

/-- Every source momentum slot is represented by a source time coordinate. -/
theorem inputTimeSlot_surjective (S : SumintShape) : Function.Surjective (inputTimeSlot S) := by
  rintro ⟨i,j⟩
  have hn := j.isLt
  unfold SumintShape.n at hn
  by_cases h0 : (j:ℕ) ≤ S.m i
  · refine ⟨.inl ⟨i,⟨j,by omega⟩⟩,?_⟩
    rfl
  · by_cases h1 : (j:ℕ) ≤ 2*S.m i
    · refine ⟨.inr (.inl ⟨i,⟨(j:ℕ)-(S.m i+1),by omega⟩⟩),?_⟩
      dsimp only [inputTimeSlot,SumintShape.ySlot]
      apply congrArg (fun k : Fin (S.n i) => (⟨i,k⟩ : S.VIdx))
      apply Fin.ext
      change S.m i+1+((j:ℕ)-(S.m i+1)) = j
      omega
    · have hnor : S.nor i = true := by
        cases h : S.nor i with
        | false => simp only [h,Bool.false_eq_true,ite_false] at hn; omega
        | true => rfl
      have hj3 : (j:ℕ)-(2*S.m i+1) < 3 := by
        have hn' : (j:ℕ) < 2*S.m i+1+3 := by simpa only [hnor,ite_true] using hn
        omega
      refine ⟨.inr (.inr ⟨⟨i,hnor⟩,⟨(j:ℕ)-(2*S.m i+1),hj3⟩⟩),?_⟩
      dsimp only [inputTimeSlot,SumintShape.uSlot]
      apply congrArg (fun k : Fin (S.n i) => (⟨i,k⟩ : S.VIdx))
      apply Fin.ext
      change 2*S.m i+1+((j:ℕ)-(2*S.m i+1)) = j
      omega

/-- Exact coordinate bijection between the source time and momentum index sets. -/
@[expose] noncomputable def timeVectorEquiv (S : SumintShape) : S.TVar ≃ S.VIdx :=
  Equiv.ofBijective (inputTimeSlot S) ((Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨inputTimeSlot_surjective S,by rw [card_time_index,card_vector_index]⟩)

/-- Explicit grouping of coordinate functions by their source factor. -/
@[expose] def timeGroupingEquiv (S : SumintShape) (α : Type*) :
    (S.TVar → α) ≃ (Fin S.I → α) ×
      ((Σ i : Fin S.I, Fin (S.m i)) → α × α) ×
      ({i : Fin S.I // S.nor i = true} → Fin 3 → α) where
  toFun x := (fun i => x (.inl ⟨i,0⟩),
    (fun p => (x (.inl ⟨p.1,p.2.succ⟩),x (.inr (.inl p)))),
    fun i j => x (.inr (.inr ⟨i,j⟩)))
  invFun z
    | .inl ⟨i,j⟩ => Fin.cases (z.1 i) (fun j => (z.2.1 ⟨i,j⟩).1) j
    | .inr (.inl p) => (z.2.1 p).2
    | .inr (.inr ⟨i,j⟩) => z.2.2 i j
  left_inv x := by
    funext a
    rcases a with ⟨i,j⟩ | (⟨i,j⟩ | ⟨i,j⟩)
    · refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
    · rfl
    · rfl
  right_inv z := by
    rcases z with ⟨u,v,w⟩
    rfl

/-- Group the actual input vector functions without changing any index multiplicity. -/
@[expose] noncomputable def inputGroupingEquiv (S : SumintShape) (α : Type*) :
    (S.VIdx → α) ≃ (Fin S.I → α) ×
      ((Σ i : Fin S.I, Fin (S.m i)) → α × α) ×
      ({i : Fin S.I // S.nor i = true} → Fin 3 → α) :=
  (Equiv.arrowCongr (timeVectorEquiv S).symm (Equiv.refl α)).trans (timeGroupingEquiv S α)

end WaveTurbulence.SumintPar
