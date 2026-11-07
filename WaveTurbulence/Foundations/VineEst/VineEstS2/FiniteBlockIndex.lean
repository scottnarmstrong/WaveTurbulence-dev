/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Basic

/-! # Exact dependent finite block index splitting -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
variable {n : ℕ}

/-- Split the first block from a dependent finite Sigma index. -/
def sigmaFinSuccEquiv (α : Fin (n+1) → Type*) :
    (Σ i, α i) ≃ α 0 ⊕ (Σ j : Fin n, α j.succ) where
  toFun p := (Fin.cases (motive := fun i => α i → α 0 ⊕ (Σ j : Fin n, α j.succ)) (fun x : α 0 => Sum.inl x)
    (fun j (x : α j.succ) => Sum.inr ⟨j,x⟩) p.1) p.2
  invFun
    | .inl x => ⟨0,x⟩
    | .inr ⟨j,x⟩ => ⟨j.succ,x⟩
  left_inv := by
    rintro ⟨i,x⟩
    revert x
    refine Fin.cases ?_ (fun _ => ?_) i <;> intro x <;> rfl
  right_inv := by
    rintro (x | ⟨j,x⟩) <;> rfl

theorem sigmaFinSuccEquiv_zero (α : Fin (n+1) → Type*) (x : α 0) :
    sigmaFinSuccEquiv α ⟨0,x⟩ = .inl x := rfl

theorem sigmaFinSuccEquiv_succ (α : Fin (n+1) → Type*) (i : Fin n) (x : α i.succ) :
    sigmaFinSuccEquiv α ⟨i.succ,x⟩ = .inr ⟨i,x⟩ := rfl

end WaveTurbulence.VineEstS2
