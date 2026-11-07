/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreGraph
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCount
import Mathlib.Tactic

/-! # The (Y2) post molecule when the two exit labels are equal

DH23 L1969: if `k_{ℓ₁} = k_{ℓ₂}`, replacing the two bonds of a bi-bridge by one bond carrying the common label changes
no energy and no gap: the transport of MOLEPROP4's `TwoExit` is exact (`g = 0`), the post energies are those of `N`,
and the large-gap condition passes over with the same parameter `η`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace EqPost
variable {N : Molecule V D} (T : TwoExit N)

theorem kvec_eq {d : ℕ} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} (hxy : κ T.x = κ T.y) :
    Molecule.kvec L w κ T.x = Molecule.kvec L w κ T.y := by simp [Molecule.kvec, hxy]

/-- With equal exit labels the post energies are the energies of `N`. -/
theorem post_gamma_eq {d : ℕ} (L : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)} (hb : ∀ z, κ (N.mate z) = κ z)
    (hxy : κ T.x = κ T.y) {v : V} (hv : v ∉ T.Y) :
    T.post.Gamma L w (T.postLabels κ 0) v = N.Gamma L w κ v := by
  rw [T.post_gamma L w hb 0 hv]
  have hk := kvec_eq (L := L) (w := w) T hxy
  simp [hk]

/-- The new bond carries the common label. -/
theorem kvec_new_eq {d : ℕ} (L : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)} (t : Bool) :
    Molecule.kvec L w (T.postLabels κ 0) (Sum.inr t) = Molecule.kvec L w κ T.y := by
  rw [T.kvec_postLabels_new L w κ 0 t]; simp

/-- The large-gap condition passes to the post molecule with the same parameter. -/
theorem post_largeGap_eq {d : ℕ} {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} (hb : ∀ z, κ (N.mate z) = κ z)
    (hxy : κ T.x = κ T.y) (hLG : MoleProp.LargeGap N L γ η w κ) :
    MoleProp.LargeGap T.post L γ η w (T.postLabels κ 0) := by
  have hkmx : Molecule.kvec L w κ (N.mate T.x) = Molecule.kvec L w κ T.x := by simp [Molecule.kvec, hb]
  have hkmy : Molecule.kvec L w κ (N.mate T.y) = Molecule.kvec L w κ T.y := by simp [Molecule.kvec, hb]
  have hxy' := kvec_eq (L := L) (w := w) T hxy
  have hk : ∀ z, Molecule.kvec L w (T.postLabels κ 0) z = Sum.elim
      (fun z : Degen.RetainedDart N T.Y => Molecule.kvec L w κ z.val)
      (fun _ => Molecule.kvec L w κ T.y) z := by
    rintro (z | t)
    · rfl
    · exact kvec_new_eq T L w t
  intro z₁ z₂ hat hout
  rw [hk, hk]
  rcases z₁ with z₁ | t₁ <;> rcases z₂ with z₂ | t₂
  · exact hLG z₁.val z₂.val hat hout
  · simp only [Sum.elim_inl, Sum.elim_inr]
    cases t₂
    · have hz : N.atom z₁.val = T.c := hat
      have hzo : N.out z₁.val = true := by
        have : T.post.out (Sum.inl z₁) ≠ false := hout
        simpa [TwoExit.post_out_inl] using this
      have := hLG z₁.val (N.mate T.x) hz (by rw [N.out_mate, T.out_x, hzo]; decide)
      rwa [hkmx, hxy'] at this
    · have hz : N.atom z₁.val = T.d := hat
      have hzo : N.out z₁.val = false := by
        have : T.post.out (Sum.inl z₁) ≠ true := hout
        simpa [TwoExit.post_out_inl] using this
      have := hLG z₁.val (N.mate T.y) hz (by rw [N.out_mate, T.out_y, hzo]; decide)
      rwa [hkmy] at this
  · simp only [Sum.elim_inl, Sum.elim_inr]
    cases t₁
    · have hz : N.atom z₂.val = T.c := hat.symm
      have hzo : N.out z₂.val = true := by
        cases h : N.out z₂.val
        · exact absurd (show (false : Bool) = T.post.out (Sum.inl z₂) by rw [TwoExit.post_out_inl, h]) hout
        · rfl
      have := hLG (N.mate T.x) z₂.val hz.symm (by rw [N.out_mate, T.out_x, hzo]; decide)
      rwa [hkmx, hxy'] at this
    · have hz : N.atom z₂.val = T.d := hat.symm
      have hzo : N.out z₂.val = false := by
        cases h : N.out z₂.val
        · rfl
        · exact absurd (show (true : Bool) = T.post.out (Sum.inl z₂) by rw [TwoExit.post_out_inl, h]) hout
      have := hLG (N.mate T.y) z₂.val hz.symm (by rw [N.out_mate, T.out_y, hzo]; decide)
      rwa [hkmy] at this
  · exfalso
    cases t₁ <;> cases t₂
    · exact hout rfl
    · exact T.c_ne_d hat
    · exact T.c_ne_d hat.symm
    · exact hout rfl

end EqPost
end WaveTurbulence.FinalCountG8
