/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutDev
/-! The `α`-cut (FINALCOUNT-G2 step 4), part 1: the half-cut atom `v` carries exactly `x₁, x₂`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem cut_x_ne (hcd : M.IsCutData v v₂ x₁ x₂) : x₁ ≠ x₂ := by
  intro e
  have h1 := hcd.2.2.2.2.2.1
  have h2 := hcd.2.2.2.2.2.2
  rw [e] at h1
  rw [h1] at h2
  exact Bool.false_ne_true h2

theorem cut_dartsAt_v_eq (hcd : M.IsCutData v v₂ x₁ x₂) : (M.cut v v₂ x₁ x₂).dartsAt v = {x₁, x₂} := by
  ext x
  rw [cut_mem_dartsAt_v M hcd]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro (h | h)
    · exact ⟨h ▸ hcd.2.2.1, Or.inl h⟩
    · exact ⟨h ▸ hcd.2.2.2.1, Or.inr h⟩

theorem cut_sum_v (hcd : M.IsCutData v v₂ x₁ x₂) {E : Type*} [AddCommMonoid E] (g : D → E) :
    ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v, g x = g x₁ + g x₂ := by
  rw [cut_dartsAt_v_eq M hcd, Finset.sum_pair (cut_x_ne M hcd)]

theorem dartSign_x₁ (hcd : M.IsCutData v v₂ x₁ x₂) : M.dartSign x₁ = -1 := by
  unfold Molecule.dartSign; rw [hcd.2.2.2.2.2.1]; simp

theorem dartSign_x₂ (hcd : M.IsCutData v v₂ x₁ x₂) : M.dartSign x₂ = 1 := by
  unfold Molecule.dartSign; rw [hcd.2.2.2.2.2.2]; simp

theorem cut_gamma_v (hcd : M.IsCutData v v₂ x₁ x₂) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) :
    (M.cut v v₂ x₁ x₂).Gamma L w κ v =
      ‖Molecule.kvec L w κ x₂‖ ^ 2 - ‖Molecule.kvec L w κ x₁‖ ^ 2 := by
  unfold Molecule.Gamma
  rw [cut_sum_v M hcd]
  show M.dartSign x₁ * _ + M.dartSign x₂ * _ = _
  rw [dartSign_x₁ M hcd, dartSign_x₂ M hcd]; ring

theorem cut_c_v (hcd : M.IsCutData v v₂ x₁ x₂) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) :
    ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v, (M.cut v v₂ x₁ x₂).dartSign x • Molecule.kvec L w κ x =
      -(Molecule.kvec L w κ x₁ - Molecule.kvec L w κ x₂) := by
  rw [cut_sum_v M hcd]
  show M.dartSign x₁ • _ + M.dartSign x₂ • _ = _
  rw [dartSign_x₁ M hcd, dartSign_x₂ M hcd]; simp; abel

theorem norm_sq_sub_norm_sq (a b : Mom d) : ‖a‖ ^ 2 - ‖b‖ ^ 2 = inner ℝ (a - b) (a + b) := by
  simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm a b]; ring

end WaveTurbulence.FinalCount
