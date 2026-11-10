/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitPost
import Mathlib.Tactic

/-! # The transported decoration: conservation and energy windows

DH23 L1954. A decoration of `N` with charges `c` gives, for every `g`, a decoration of the post molecule with the
fixed charges `postCharges c g`. Its energies are unchanged away from `c, d`; at `c` and `d` they lie within
`(1 + |1−g|·|Y|)τ`, resp. `(1 + |g|·|Y|)τ`, of explicit centers, because `|k_x|² − |k_y|² = ∑_{v ∈ Y} Γ_v` is known up
to `|Y| τ` ("fixed up to distance `O(n δ⁻¹ L^{-2γ})`", L1969).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

theorem post_dartSign_inr (t : Bool) : T.post.dartSign (Sum.inr t) = if t then 1 else -1 := by
  unfold Molecule.dartSign; cases t <;> rfl

/-- The post star sum of a signed function of labels, written through `N`'s darts. -/
theorem post_signed_sum {E : Type*} [AddCommGroup E] [Module ℝ E] {v : V} (hv : v ∉ T.Y) (F : D → E) (Fnew : E) :
    ∑ z ∈ T.post.dartsAt v, T.post.dartSign z • Sum.elim (fun z : Degen.RetainedDart N T.Y => F z.val)
        (fun _ => Fnew) z =
      ∑ z ∈ N.dartsAt v, N.dartSign z • F z - (if v = T.c then N.dartSign (N.mate T.x) • F (N.mate T.x) else 0)
        - (if v = T.d then N.dartSign (N.mate T.y) • F (N.mate T.y) else 0)
        + (if T.d = v then Fnew else 0) + (if T.c = v then -Fnew else 0) := by
  have h := T.post_star_sum hv (fun z => N.dartSign z • F z) (fun t => (if t then (1 : ℝ) else -1) • Fnew)
  simp only [ite_true, one_smul, Bool.false_eq_true, ite_false, neg_one_smul] at h
  rw [← h]
  refine sum_congr rfl fun z _ => ?_
  rcases z with z | t
  · rfl
  · rw [post_dartSign_inr]; rfl

/-- **The transported labels form a decoration of the post molecule** with the fixed charges `postCharges c g`. -/
theorem post_isDecoration {d : ℕ} {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : N.IsDecoration L w c κ) (g : ℤ) :
    T.post.IsDecoration L w (T.postCharges c g) (T.postLabels κ g) := by
  constructor
  · rintro (z | t)
    · exact hκ.1 z.val
    · rfl
  · intro v hv
    rw [post_atoms] at hv
    obtain ⟨hvN, hvY⟩ := mem_sdiff.mp hv
    have hkv : ∀ z, Molecule.kvec L w (T.postLabels κ g) z = Sum.elim
        (fun z : Degen.RetainedDart N T.Y => Molecule.kvec L w κ z.val)
        (fun _ => Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)) z := by
      rintro (z | t)
      · rfl
      · exact T.kvec_postLabels_new L w κ g t
    simp only [hkv]
    rw [T.post_signed_sum hvY, hκ.2 v hvN, T.dartSign_mate_x, T.dartSign_mate_y]
    have hmx : Molecule.kvec L w κ (N.mate T.x) = Molecule.kvec L w κ T.x := by simp [Molecule.kvec, hκ.1]
    have hmy : Molecule.kvec L w κ (N.mate T.y) = Molecule.kvec L w κ T.y := by simp [Molecule.kvec, hκ.1]
    rw [hmx, hmy]
    have hR := T.kvec_x_sub_y hκ
    have hcd := T.c_ne_d
    unfold postCharges
    by_cases hc : v = T.c
    · subst hc
      simp only [ite_true, Ne.symm hcd, hcd, ite_false, sub_zero, add_zero, neg_one_smul, sub_neg_eq_add]
      rw [← hR]; module
    · by_cases hd : v = T.d
      · subst hd
        simp only [hc, hcd, ite_false, ite_true, sub_zero, one_smul]
        rw [← hR]; module
      · simp only [hc, hd, ite_false, Ne.symm hc, Ne.symm hd, sub_zero, add_zero]

/-- The exits' energy difference is the energy sum over `Y`. -/
theorem norm_sq_x_sub_y {d : ℕ} (L : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)} (hκ : ∀ z, κ (N.mate z) = κ z) :
    ‖Molecule.kvec L w κ T.x‖ ^ 2 - ‖Molecule.kvec L w κ T.y‖ ^ 2 = ∑ v ∈ T.Y, N.Gamma L w κ v := by
  rw [sum_gamma_eq_cross N L w hκ T.Y, T.cross, sum_pair T.ne]
  unfold Molecule.dartSign
  rw [T.out_x, T.out_y]
  simp only [ite_true, Bool.false_eq_true, ite_false, one_mul, neg_one_mul]
  ring

/-- The window of the energy sum over `Y`. -/
theorem sum_gamma_window {d : ℕ} {L γ δ : ℝ} {w : Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hres : N.IsRestricted L γ δ w β k0 κ) :
    |∑ v ∈ T.Y, N.Gamma L w κ v - ∑ v ∈ T.Y, β v| ≤ T.Y.card * (δ⁻¹ * L ^ (-2 * γ)) := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul]
  exact sum_le_card_nsmul _ _ _ fun v hv => hres.1 v (T.sub hv)

/-- The post energy at a surviving atom. -/
theorem post_gamma {d : ℕ} (L : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)} (hκ : ∀ z, κ (N.mate z) = κ z) (g : ℤ)
    {v : V} (hv : v ∉ T.Y) :
    T.post.Gamma L w (T.postLabels κ g) v =
      N.Gamma L w κ v + (if v = T.c then ‖Molecule.kvec L w κ T.x‖ ^ 2 -
          ‖Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)‖ ^ 2 else 0)
        + (if v = T.d then ‖Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)‖ ^ 2
          - ‖Molecule.kvec L w κ T.y‖ ^ 2 else 0) := by
  unfold Molecule.Gamma
  have hkv : ∀ z, ‖Molecule.kvec L w (T.postLabels κ g) z‖ ^ 2 = Sum.elim
      (fun z : Degen.RetainedDart N T.Y => ‖Molecule.kvec L w κ z.val‖ ^ 2)
      (fun _ => ‖Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)‖ ^ 2) z := by
    rintro (z | t)
    · rfl
    · simp only [Sum.elim_inr]; rw [T.kvec_postLabels_new L w κ g t]
  have hs : ∀ z ∈ T.post.dartsAt v, T.post.dartSign z * ‖Molecule.kvec L w (T.postLabels κ g) z‖ ^ 2 =
      T.post.dartSign z • Sum.elim (fun z : Degen.RetainedDart N T.Y => ‖Molecule.kvec L w κ z.val‖ ^ 2)
        (fun _ => ‖Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)‖ ^ 2) z := by
    intro z _; rw [hkv, smul_eq_mul]
  rw [sum_congr rfl hs, T.post_signed_sum hv (fun z => ‖Molecule.kvec L w κ z‖ ^ 2)
    (‖Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)‖ ^ 2),
    T.dartSign_mate_x, T.dartSign_mate_y]
  have hmx : ‖Molecule.kvec L w κ (N.mate T.x)‖ = ‖Molecule.kvec L w κ T.x‖ := by simp [Molecule.kvec, hκ]
  have hmy : ‖Molecule.kvec L w κ (N.mate T.y)‖ = ‖Molecule.kvec L w κ T.y‖ := by simp [Molecule.kvec, hκ]
  simp only [smul_eq_mul, hmx, hmy]
  have hcd := T.c_ne_d
  by_cases hc : v = T.c
  · subst hc; simp only [ite_true, Ne.symm hcd, hcd, ite_false]; ring
  · by_cases hd : v = T.d
    · subst hd; simp only [hc, hcd, ite_false, ite_true]; ring
    · simp only [hc, hd, ite_false, Ne.symm hc, Ne.symm hd]; ring

end TwoExit
end WaveTurbulence.MoleProp4
