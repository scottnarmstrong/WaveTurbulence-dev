/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootWeightExpansion
/-! Exact redistribution of finitely many coordinate weights among individual input leaves.
This is an algebraic identity before summation over decorations; no absolute-value estimate
is taken inside the oscillatory sum. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def coordinateSlot {I : Type*} [DecidableEq I] {d : ℕ}
    (c : Option (I × Fin d)) (l : I) (k : Mom d) : ℝ :=
  match c with
  | none => 1
  | some (a, j) => if a = l then k j else 1

def coordinateSlotValue {I : Type*} {d : ℕ}
    (v : I → Mom d) : Option (I × Fin d) → ℝ
  | none => 1
  | some (a, j) => v a j

theorem prod_coordinateSlot {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (v : I → Mom d) (c : Option (I × Fin d)) :
    (∏ l, coordinateSlot c l (v l)) = coordinateSlotValue v c := by
  classical
  cases c with
  | none => simp [coordinateSlot, coordinateSlotValue]
  | some c =>
    rcases c with ⟨a, j⟩
    simp only [coordinateSlot, coordinateSlotValue]
    rw [Fintype.prod_eq_single a]
    · simp
    · intro b hb
      simp [Ne.symm hb]

/-- The input profile assigned to one actual positive leaf after the finite coordinate
choices have been fixed. Each choice contributes at most one coordinate to this leaf. -/
noncomputable def monomialLeafProfile {I T : Type*} [DecidableEq I] [Fintype T]
    {d : ℕ} (H : I → Mom d → ℝ) (c : T → Option (I × Fin d))
    (l : I) (k : Mom d) : ℝ := H l k * ∏ t, coordinateSlot (c t) l k

/-- Exact factorization of all chosen coordinate weights into separate leaf inputs. -/
theorem prod_monomialLeafProfile {I T : Type*} [Fintype I] [DecidableEq I]
    [Fintype T] {d : ℕ} (H : I → Mom d → ℝ)
    (c : T → Option (I × Fin d)) (v : I → Mom d) :
    (∏ l, monomialLeafProfile H c l (v l)) =
      (∏ l, H l (v l)) * ∏ t, coordinateSlotValue v (c t) := by
  classical
  simp only [monomialLeafProfile, prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  exact prod_congr rfl (fun t _ => prod_coordinateSlot v (c t))

/-- A leaf untouched by the fixed choices retains its original input profile. -/
theorem monomialLeafProfile_eq_of_unselected {I T : Type*} [DecidableEq I]
    [Fintype T] {d : ℕ} (H : I → Mom d → ℝ)
    (c : T → Option (I × Fin d)) (l : I)
    (hl : ∀ t j, c t ≠ some (l, j)) : monomialLeafProfile H c l = H l := by
  classical
  funext k
  unfold monomialLeafProfile
  suffices (∏ t, coordinateSlot (c t) l k) = 1 by rw [this, mul_one]
  apply prod_eq_one
  intro t _
  cases hc : c t with
  | none => rfl
  | some a =>
    rcases a with ⟨a, j⟩
    have hne : a ≠ l := by
      intro he
      subst a
      exact hl t j hc
    simp [coordinateSlot, hne]

end WaveTurbulence.LGSpine
