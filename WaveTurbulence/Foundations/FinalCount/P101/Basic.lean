/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGapLoops
public import WaveTurbulence.Foundations.FinalCount.MoleProp.HereditaryConstraints
import Mathlib.Tactic

/-! # Prop 10.1', basics: large gap at a single atom, and off a protected set

DH23 Prop 10.1 is applied (L1862-L1874) to final components whose alpha/beta atoms are not large-gap. The
G6 development requires `LargeGap` at every atom; its operations use it only at the removed atoms. We therefore
fork the operations with `LargeGapAt M v` (large gap at the single atom `v`) and carry
`LargeGapOff B M` (large gap at every atom outside the protected set `B`) in the induction.
-/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Large gap at the atom `v` only. -/
def LargeGapAt (M : Molecule V D) {d : ℕ} (v : V) (L γ η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∀ x y : D, M.atom x = v → M.atom y = v → M.out x ≠ M.out y →
    L ^ (-γ + η) ≤ ‖Molecule.kvec L w κ x - Molecule.kvec L w κ y‖

/-- Large gap at every atom outside the protected set `B`. -/
def LargeGapOff (B : Finset V) (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∀ v : V, v ∉ B → LargeGapAt M v L γ η w κ

/-- Large gap at `v` is inherited by erasure of other atoms. -/
theorem largeGapAt_erase (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (Y : Finset V) {κ : D → (Fin d → ℤ)} {v : V} (hv : v ∉ Y) (h : LargeGapAt M v L γ η w κ) :
    LargeGapAt (Degen.eraseAtoms M Y) v L γ η w (fun x => κ x.val) := by
  intro x y hx hy hd
  exact h x.val y.val hx hy hd

theorem largeGapOff_erase (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (B : Finset V) (Y : Finset V) {κ : D → (Fin d → ℤ)} (h : LargeGapOff B M L γ η w κ) :
    LargeGapOff B (Degen.eraseAtoms M Y) L γ η w (fun x => κ x.val) := by
  intro v hv x y hx hy hd
  exact h v hv x.val y.val hx hy hd

theorem projected_largeGapOff (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (B Y : Finset V) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGapOff B M L γ η w κ) :
    ∀ κ, erasedFreeAdmissibility M Y Adm κ → LargeGapOff B (Degen.eraseAtoms M Y) L γ η w κ := by
  intro κ hκ
  obtain ⟨κ0,h0,_hb,rfl⟩ := hκ
  exact largeGapOff_erase M L γ η w B Y (hAdm κ0 h0)

theorem projected_largeGapAt (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (Y : Finset V) {v : V} (hv : v ∉ Y) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGapAt M v L γ η w κ) :
    ∀ κ, erasedFreeAdmissibility M Y Adm κ → LargeGapAt (Degen.eraseAtoms M Y) v L γ η w κ := by
  intro κ hκ
  obtain ⟨κ0,h0,_hb,rfl⟩ := hκ
  exact largeGapAt_erase M L γ η w Y hv (hAdm κ0 h0)

/-- A self-loop at an atom with large gap there is impossible. -/
theorem not_largeGapAt_of_self_loop (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ η : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)}
    (hb : ∀ x, κ (M.mate x) = κ x) (x : D) (hx : M.atom x = M.atom (M.mate x)) :
    ¬ LargeGapAt M (M.atom x) L γ η w κ := by
  intro h
  have hdir : M.out x ≠ M.out (M.mate x) := by
    rw [M.out_mate]
    cases M.out x <;> decide
  have hg := h x (M.mate x) rfl hx.symm hdir
  simp only [Molecule.kvec,hb x,sub_self,norm_zero] at hg
  exact (not_le_of_gt (Real.rpow_pos_of_pos hL (-γ+η))) hg

theorem countEFree_eq_zero_of_loop_at (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (x : D) (hx : M.atom x = M.atom (M.mate x))
    (hAdm : ∀ κ, Adm κ → LargeGapAt M (M.atom x) L γ η w κ) :
    countEFree M L γ δ w Adm = 0 := by
  apply le_antisymm _ bot_le
  unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun _ => ?_
  have he : {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} = ∅ := by
    ext κ
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    intro hκ
    exact not_largeGapAt_of_self_loop M hL γ η w hκ.1.1 x hx (hAdm κ hκ.2.2)
  rw [he,Set.encard_empty]
  exact bot_le

theorem countAFree_eq_zero_of_loop_at (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ C1 η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (x : D) (hx : M.atom x = M.atom (M.mate x))
    (hAdm : ∀ κ, Adm κ → LargeGapAt M (M.atom x) L γ η w κ) :
    countAFree M L γ δ C1 w Adm P = 0 := by
  unfold countAFree
  rw [countEFree_eq_zero_of_loop_at M hL γ δ η w Adm x hx hAdm]
  simp only [ENat.toENNReal_zero,zero_mul]

end WaveTurbulence.FinalCountG8.P101
