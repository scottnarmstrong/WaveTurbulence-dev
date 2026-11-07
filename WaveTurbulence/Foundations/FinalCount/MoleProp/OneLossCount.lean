/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DegreeTwoDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DegreeThreeOneLossDeletion
import Mathlib.Tactic

/-! # Both genuine one-circuit-loss counting branches in DH23 10.1 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem one_loss_deletion_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ v ∈ M.atoms,
    (M.deg v = 2 ∨ (M.deg v = 3 ∧ (Degen.newComponents M {v}).card = 2)) →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*δ⁻¹*L^((d : ℝ)-γ-η)⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {v}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) := by
  obtain ⟨C2,R2,hC2,hB2⟩ := degree_two_deletion_bound d hd γ hγ η hη hηmax
  obtain ⟨C3,R3,hC3,hB3⟩ := degree_three_one_loss_deletion_bound d hd γ hγ η hη hηmax
  refine ⟨max C2 C3,max (max R2 R3) 1,hC2.trans (le_max_left _ _),?_⟩
  intro L hL δ hδ V D _ _ _ M hM v hv hbranch Adm hAdm
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right (max R2 R3) 1).trans hL)
  have hmono (C : ℝ) (hC : C ≤ max C2 C3) :
      (⌈C*δ⁻¹*L^((d : ℝ)-γ-η)⌉₊ : ℕ∞) ≤ (⌈max C2 C3*δ⁻¹*L^((d : ℝ)-γ-η)⌉₊ : ℕ∞) := by
    have hr := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hδ.1.le))
      (Real.rpow_nonneg hLp.le ((d : ℝ)-γ-η))
    have hn := Nat.ceil_mono hr
    exact_mod_cast hn
  rcases hbranch with h2 | ⟨h3,hC⟩
  · exact (hB2 L ((le_max_left R2 R3).trans ((le_max_left (max R2 R3) 1).trans hL)) δ hδ M hM v hv h2 Adm hAdm).trans
      (mul_le_mul_of_nonneg_right (hmono C2 (le_max_left _ _)) bot_le)
  · exact (hB3 L ((le_max_right R2 R3).trans ((le_max_left (max R2 R3) 1).trans hL)) δ hδ M hM v hv h3 hC Adm hAdm).trans
      (mul_le_mul_of_nonneg_right (hmono C3 (le_max_right _ _)) bot_le)

end WaveTurbulence.MoleProp
