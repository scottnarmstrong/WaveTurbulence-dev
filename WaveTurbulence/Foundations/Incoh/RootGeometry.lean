/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootCoordinates
public import WaveTurbulence.Foundations.Incoh.LayerLink

/-!
# The links touched by the two root coordinates

TARGET (incohproof18): at most two links meet the root times. The factors
of every other link are independent of the root coordinates, as a proved
consequence of the stored finite permutation.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Reconstructing an original time is just evaluating the finite coordinate permutation. -/
@[simp] theorem RootCoordinates.equiv_symm_apply {n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (t : Fin r → ℝ) (u : Fin R.restCount → ℝ) (i : Fin n) (j : Fin 2) :
    R.equiv.symm (t, u) i j = Sum.elim t u (R.permutation (finProdFinEquiv (i, j))) := by
  rfl

/-- The original vertex occupied by a selected root time. -/
@[expose] def RootCoordinates.rootVertex {n : ℕ} {r : ℕ} (R : RootCoordinates n r) (a : Fin r) : Fin n × Fin 2 :=
  finProdFinEquiv.symm (R.permutation.symm (Sum.inl a))

/-- The finite set of links meeting either root time. -/
@[expose] def RootCoordinates.rootLinks {n : ℕ} {r : ℕ} (R : RootCoordinates n r) : Finset (Fin n) :=
  Finset.univ.image (fun a : Fin r => (R.rootVertex a).1)

theorem RootCoordinates.card_rootLinks_le {n : ℕ} {r : ℕ} (R : RootCoordinates n r) :
    R.rootLinks.card ≤ r := by
  exact Finset.card_image_le.trans_eq (by simp)

@[simp] theorem RootCoordinates.equiv_symm_rootVertex {n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (t : Fin r → ℝ) (u : Fin R.restCount → ℝ) (a : Fin r) :
    R.equiv.symm (t, u) (R.rootVertex a).1 (R.rootVertex a).2 = t a := by
  rw [R.equiv_symm_apply]
  simp only [rootVertex, Prod.mk.eta, Equiv.apply_symm_apply, Sum.elim_inl]

/-- Untouched links do not depend on either selected root time. -/
theorem RootCoordinates.equiv_symm_eq_of_notMem_rootLinks {n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (t t' : Fin r → ℝ) (u : Fin R.restCount → ℝ) (i : Fin n) (hi : i ∉ R.rootLinks) :
    R.equiv.symm (t, u) i = R.equiv.symm (t', u) i := by
  funext j
  rw [R.equiv_symm_apply, R.equiv_symm_apply]
  cases he : R.permutation (finProdFinEquiv (i, j)) with
  | inr k => rfl
  | inl a =>
      exfalso
      apply hi
      have hv : R.rootVertex a = (i, j) := by
        unfold rootVertex
        rw [← he, R.permutation.symm_apply_apply, finProdFinEquiv.symm_apply_apply]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, congrArg Prod.fst hv⟩

end WaveTurbulence.Incoh
