/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.BetaSums
/-! The `β`-cut count bound `𝔈(𝕄) ≤ (4|𝕄|+6) 𝔈(𝕄_cut)` (FINALCOUNT-HALF M2c; DH23 L1784 case of Prop 9.4). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem cut_deg_v₂ (hcd : M.IsCutData v v₂ x₁ x₂) :
    (M.cut v v₂ x₁ x₂).deg v₂ + 2 = M.deg v := by
  have h := cut_sum_split M hcd (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have h2 := cut_deg_v M hcd
  unfold Molecule.deg at h2 ⊢
  omega

theorem cut_gamma_other (hcd : M.IsCutData v v₂ x₁ x₂) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) {a : V}
    (hav : a ≠ v) (hav₂ : a ≠ v₂) : (M.cut v v₂ x₁ x₂).Gamma L w κ a = M.Gamma L w κ a := by
  unfold Molecule.Gamma; rw [cut_dartsAt_other M hcd hav hav₂]; rfl

theorem cut_gamma_split (hcd : M.IsCutData v v₂ x₁ x₂) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) :
    M.Gamma L w κ v = (M.cut v v₂ x₁ x₂).Gamma L w κ v + (M.cut v v₂ x₁ x₂).Gamma L w κ v₂ := by
  unfold Molecule.Gamma
  exact cut_sum_split M hcd (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2)

theorem beta_gamma_side (hcd : M.IsCutData v v₂ x₁ x₂) (hsep : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂)
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) :
    (M.cut v v₂ x₁ x₂).Gamma L w κ v₂ = - ∑ a ∈ betaSide M v v₂ x₁ x₂, M.Gamma L w κ a := by
  have h := beta_side_sum M hcd hsep (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) (by
    intro x
    rw [dartSign_mate]
    have : Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by unfold Molecule.kvec; rw [hκ]
    rw [this]; ring)
  have e : (M.cut v v₂ x₁ x₂).dartSign = M.dartSign := rfl
  unfold Molecule.Gamma
  rw [e]
  linarith

theorem beta_c_side (hcd : M.IsCutData v v₂ x₁ x₂) (hsep : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂)
    (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) :
    ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂, M.dartSign x • Molecule.kvec L w κ x =
      - ∑ a ∈ betaSide M v v₂ x₁ x₂, c a := by
  have h := beta_side_sum M hcd hsep (fun x => M.dartSign x • Molecule.kvec L w κ x) (by
    intro x
    rw [dartSign_mate]
    have : Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by unfold Molecule.kvec; rw [hκ.1]
    rw [this, neg_smul])
  have h2 : ∑ a ∈ betaSide M v v₂ x₁ x₂, ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L w κ x =
      ∑ a ∈ betaSide M v v₂ x₁ x₂, c a := by
    refine Finset.sum_congr rfl fun a ha => hκ.2 a ?_
    have := betaSide_sub M hcd hsep ha
    exact (Finset.mem_erase.mp this).2
  rw [h2] at h
  exact eq_neg_of_add_eq_zero_left h

end WaveTurbulence.FinalCount
