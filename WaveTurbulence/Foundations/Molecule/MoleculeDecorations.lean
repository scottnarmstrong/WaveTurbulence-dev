/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-!
# Conservation and energy sums for actual molecule decorations

TARGET `defdecmol`, equations (decmole1) and (defomegadec), L1308–L1325.
Opposite darts of every bond cancel, including self-loops and parallel bonds.
-/

public section

namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

omit [DecidableEq V] [Fintype D] in
theorem dartSign_mate (x : D) : M.dartSign (M.mate x) = -M.dartSign x := by
  unfold Molecule.dartSign
  rw [M.out_mate]
  cases M.out x <;> norm_num

omit [DecidableEq V] in
/-- Cancellation across the actual mate involution for any bond-constant
vector assignment. No conservation equation is assumed. -/
theorem sum_signed_darts_eq_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : D → E) (hk : ∀ x, k (M.mate x) = k x) :
    ∑ x : D, M.dartSign x • k x = 0 := by
  apply Finset.sum_ninvolution M.mate
  · intro x
    rw [hk x,dartSign_mate,neg_smul,add_neg_cancel]
  · intro x _hx
    exact M.mate_ne x
  · intro x
    exact Finset.mem_univ _
  · exact M.mate_mate

/-- The source conservation parameters necessarily have zero total sum. -/
theorem sum_conservation_eq_zero {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d)
    (kappa : D → (Fin d → ℤ)) (hk : M.IsDecoration L w c kappa) :
    ∑ v ∈ M.atoms, c v = 0 := by
  have hvec (x : D) : Molecule.kvec L w kappa (M.mate x) = Molecule.kvec L w kappa x := by
    simp only [Molecule.kvec,hk.1 x]
  calc
    _ = ∑ v ∈ M.atoms, ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w kappa x := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (hk.2 v hv).symm
    _ = ∑ x : D, M.dartSign x • Molecule.kvec L w kappa x := by
      exact Finset.sum_fiberwise_of_maps_to (fun x _hx => M.atom_mem x) _
    _ = 0 := sum_signed_darts_eq_zero M _ hvec

/-- The signed quadratic energies also cancel globally across bonds. -/
theorem sum_Gamma_eq_zero {d : ℕ} (L : ℝ) (w : Mom d)
    (kappa : D → (Fin d → ℤ)) (hk : ∀ x, kappa (M.mate x) = kappa x) :
    ∑ v ∈ M.atoms, M.Gamma L w kappa v = 0 := by
  have hvec (x : D) : ‖Molecule.kvec L w kappa (M.mate x)‖^2 = ‖Molecule.kvec L w kappa x‖^2 := by
    simp only [Molecule.kvec,hk x]
  calc
    _ = ∑ x : D, M.dartSign x * ‖Molecule.kvec L w kappa x‖^2 := by
      exact Finset.sum_fiberwise_of_maps_to (fun x _hx => M.atom_mem x) _
    _ = 0 := by
      simpa only [smul_eq_mul] using sum_signed_darts_eq_zero M
        (fun x => ‖Molecule.kvec L w kappa x‖^2) hvec

end WaveTurbulence.Mole
