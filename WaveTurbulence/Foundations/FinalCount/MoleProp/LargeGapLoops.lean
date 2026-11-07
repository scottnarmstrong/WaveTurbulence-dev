/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
import Mathlib.Tactic

/-! # Self-loops contribute no actual large-gap decorations -/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem not_largeGap_of_self_loop (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ η : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)}
    (hb : ∀ x, κ (M.mate x) = κ x) (x : D) (hx : M.atom x = M.atom (M.mate x)) :
    ¬ LargeGap M L γ η w κ := by
  intro h
  have hdir : M.out x ≠ M.out (M.mate x) := by
    rw [M.out_mate]
    cases M.out x <;> decide
  have hg := h x (M.mate x) hx hdir
  simp only [Molecule.kvec,hb x,sub_self,norm_zero] at hg
  exact (not_le_of_gt (Real.rpow_pos_of_pos hL (-γ+η))) hg

theorem countEFree_eq_zero_of_loop (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGap M L γ η w κ)
    (x : D) (hx : M.atom x = M.atom (M.mate x)) : countEFree M L γ δ w Adm = 0 := by
  apply le_antisymm _ bot_le
  unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun _ => ?_
  have he : {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} = ∅ := by
    ext κ
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    intro hκ
    exact not_largeGap_of_self_loop M hL γ η w hκ.1.1 x hx (hAdm κ hκ.2.2)
  rw [he,Set.encard_empty]
  exact bot_le

theorem countAFree_eq_zero_of_loop (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ C1 η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGap M L γ η w κ) (P : Finset V → ℝ)
    (x : D) (hx : M.atom x = M.atom (M.mate x)) : countAFree M L γ δ C1 w Adm P = 0 := by
  unfold countAFree
  rw [countEFree_eq_zero_of_loop M hL γ δ η w Adm hAdm x hx]
  simp only [ENat.toENNReal_zero,zero_mul]

end WaveTurbulence.MoleProp
