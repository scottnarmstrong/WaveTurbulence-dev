/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitDecor
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Scales
import Mathlib.Tactic

/-! # The large-gap condition after the new bond (DH23 L1954)

"This will keep the LG assumption for `𝕄′` (which is weakened by a constant multiple...)". If `κ` is LG with
parameter `η` on `N` (caps `≤ 2`), some `g ∈ {0,…,4}` makes the transported labels LG with parameter `η/2` on the
post molecule, once `L^{η/2} ≥ 11`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

theorem post_atom_inl (z : Degen.RetainedDart N T.Y) : T.post.atom (Sum.inl z) = N.atom z.val := rfl
theorem post_atom_inr_true : T.post.atom (Sum.inr true) = T.d := rfl
theorem post_atom_inr_false : T.post.atom (Sum.inr false) = T.c := rfl

/-- The constraint vectors at the two ends of the new bond, flagged by the exit they are compared with. -/
noncomputable def lgTargets {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) : Finset (Mom d × Bool) :=
  ((univ.filter fun z : D => N.atom z = T.c ∧ N.out z = true).image fun z => (Molecule.kvec L w κ z, true)) ∪
    ((univ.filter fun z : D => N.atom z = T.d ∧ N.out z = false).image fun z => (Molecule.kvec L w κ z, false))

theorem card_lgTargets_le {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) : (T.lgTargets L w κ).card ≤ 4 := by
  unfold lgTargets
  refine (card_union_le _ _).trans ?_
  have h1 : (univ.filter fun z : D => N.atom z = T.c ∧ N.out z = true).card ≤ 2 := by
    have := (hcap T.c (mem_sdiff.mp T.c_mem).1).1
    unfold Molecule.outdeg Molecule.dartsAt at this
    rwa [filter_filter] at this
  have h2 : (univ.filter fun z : D => N.atom z = T.d ∧ N.out z = false).card ≤ 2 := by
    have := (hcap T.d (mem_sdiff.mp T.d_mem).1).2
    unfold Molecule.indeg Molecule.dartsAt at this
    rwa [filter_filter] at this
  have := card_image_le (s := univ.filter fun z : D => N.atom z = T.c ∧ N.out z = true)
    (f := fun z => (Molecule.kvec L w κ z, true))
  have := card_image_le (s := univ.filter fun z : D => N.atom z = T.d ∧ N.out z = false)
    (f := fun z => (Molecule.kvec L w κ z, false))
  omega

/-- **Choice of `g` keeping the large gap.** -/
theorem exists_post_largeGap {d : ℕ} {L γ η : ℝ} (hL : 1 ≤ L) (hL11 : 11 ≤ L ^ (η / 2))
    {w : Mom d} {κ : D → (Fin d → ℤ)} (hb : ∀ z, κ (N.mate z) = κ z)
    (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hLG : MoleProp.LargeGap N L γ η w κ) :
    ∃ g ∈ Icc (0 : ℤ) 4, MoleProp.LargeGap T.post L γ (η / 2) w (T.postLabels κ g) := by
  have hLp : 0 < L := by linarith
  set lam := L ^ (-γ + η) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hLp _
  have hkmx : Molecule.kvec L w κ (N.mate T.x) = Molecule.kvec L w κ T.x := by simp [Molecule.kvec, hb]
  have hkmy : Molecule.kvec L w κ (N.mate T.y) = Molecule.kvec L w κ T.y := by simp [Molecule.kvec, hb]
  obtain ⟨g, hg, hgood⟩ := exists_good_multiplier hlam0 (Molecule.kvec L w κ T.x) (Molecule.kvec L w κ T.y)
    (T.lgTargets L w κ) (T.card_lgTargets_le L w κ hcap) (by
      intro p hp
      unfold lgTargets at hp
      rcases mem_union.mp hp with hp | hp
      · obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
        obtain ⟨hzc, hzo⟩ := (mem_filter.mp hz).2
        simp only [ite_true]
        rw [← hkmx]
        refine hLG (N.mate T.x) z hzc.symm ?_
        rw [N.out_mate, T.out_x, hzo]; decide
      · obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
        obtain ⟨hzd, hzo⟩ := (mem_filter.mp hz).2
        simp only [Bool.false_eq_true, ite_false]
        rw [← hkmy]
        refine hLG (N.mate T.y) z hzd.symm ?_
        rw [N.out_mate, T.out_y, hzo]; decide)
  refine ⟨g, hg, ?_⟩
  -- the comparison `L^{-γ+η/2} ≤ λ/11 ≤ λ`
  have hcmp : L ^ (-γ + η / 2) ≤ lam / 11 := by
    have h2 : lam = L ^ (-γ + η / 2) * L ^ (η / 2) := by
      rw [hlam, ← Real.rpow_add hLp]; congr 1; ring
    rw [h2, le_div_iff₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_left hL11 (Real.rpow_pos_of_pos hLp _).le
  have hcmp' : lam / 11 ≤ lam := by linarith
  intro z₁ z₂ hat hout
  have hk : ∀ z, Molecule.kvec L w (T.postLabels κ g) z = Sum.elim
      (fun z : Degen.RetainedDart N T.Y => Molecule.kvec L w κ z.val)
      (fun _ => Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)) z := by
    rintro (z | t)
    · rfl
    · exact T.kvec_postLabels_new L w κ g t
  rw [hk, hk]
  rcases z₁ with z₁ | t₁ <;> rcases z₂ with z₂ | t₂
  · exact hcmp.trans (hcmp'.trans (hLG z₁.val z₂.val hat hout))
  · -- new dart `t₂`, old dart `z₁` at the same atom
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [norm_sub_rev]
    cases t₂
    · -- at `c`, the new dart is incoming, `z₁` outgoing
      have hz : N.atom z₁.val = T.c := hat
      have hzo : N.out z₁.val = true := by
        have : T.post.out (Sum.inl z₁) ≠ false := hout
        simpa [post_out_inl] using this
      have := hgood (Molecule.kvec L w κ z₁.val, true) (by
        unfold lgTargets; exact mem_union_left _ (mem_image.mpr ⟨z₁.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
    · have hz : N.atom z₁.val = T.d := hat
      have hzo : N.out z₁.val = false := by
        have : T.post.out (Sum.inl z₁) ≠ true := hout
        simpa [post_out_inl] using this
      have := hgood (Molecule.kvec L w κ z₁.val, false) (by
        unfold lgTargets; exact mem_union_right _ (mem_image.mpr ⟨z₁.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
  · simp only [Sum.elim_inl, Sum.elim_inr]
    cases t₁
    · have hz : N.atom z₂.val = T.c := hat.symm
      have hzo : N.out z₂.val = true := by
        cases h : N.out z₂.val
        · exact absurd (show (false : Bool) = T.post.out (Sum.inl z₂) by rw [post_out_inl, h]) hout
        · rfl
      have := hgood (Molecule.kvec L w κ z₂.val, true) (by
        unfold lgTargets; exact mem_union_left _ (mem_image.mpr ⟨z₂.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
    · have hz : N.atom z₂.val = T.d := hat.symm
      have hzo : N.out z₂.val = false := by
        cases h : N.out z₂.val
        · rfl
        · exact absurd (show (true : Bool) = T.post.out (Sum.inl z₂) by rw [post_out_inl, h]) hout
      have := hgood (Molecule.kvec L w κ z₂.val, false) (by
        unfold lgTargets; exact mem_union_right _ (mem_image.mpr ⟨z₂.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
  · -- two new darts at the same atom: impossible (`c ≠ d`) or equal orientation
    exfalso
    cases t₁ <;> cases t₂
    · exact hout rfl
    · exact T.c_ne_d hat
    · exact T.c_ne_d hat.symm
    · exact hout rfl

end TwoExit
end WaveTurbulence.MoleProp4
