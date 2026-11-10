/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootGeometry

/-!
# Root and internal unit time boxes

TARGET (incohproof11), (incohproof18). Finite coordinate permutations split
the full product box into the root box and the remaining internal box.
Each has volume one, regardless of the integer layer values.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The integer layer at an individual branching vertex. -/
@[expose] def vertexLayer {d n : ℕ} (Q : Fin n → LayerLink d) (v : Fin n × Fin 2) : ℤ :=
  ![(Q v.1).leftLayer, (Q v.1).rightLayer] v.2

/-- The two root-time intervals in the permuted coordinates. -/
@[expose] def RootCoordinates.rootBox {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (Q : Fin n → LayerLink d) :
    Set (Fin r → ℝ) :=
  Icc (fun a => (vertexLayer Q (R.rootVertex a) : ℝ))
    (fun a => (vertexLayer Q (R.rootVertex a) : ℝ) + 1)

/-- The internal-time intervals in the permuted coordinates. -/
@[expose] def RootCoordinates.restBox {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (Q : Fin n → LayerLink d) :
    Set (Fin R.restCount → ℝ) :=
  Icc (fun k => (vertexLayer Q (finProdFinEquiv.symm (R.permutation.symm (Sum.inr k))) : ℝ))
    (fun k => (vertexLayer Q (finProdFinEquiv.symm (R.permutation.symm (Sum.inr k))) : ℝ) + 1)

/-- The literal link-box product expressed as individual vertex intervals. -/
theorem mem_linkBoxes_iff {d n : ℕ} (Q : Fin n → LayerLink d) (t : Fin n → Fin 2 → ℝ) :
    t ∈ univ.pi (fun i => linkBox (Q i)) ↔
      ∀ v : Fin n × Fin 2, (vertexLayer Q v : ℝ) ≤ t v.1 v.2 ∧
        t v.1 v.2 ≤ (vertexLayer Q v : ℝ) + 1 := by
  simp only [mem_pi, mem_univ, forall_const, linkBox, mem_Icc, Pi.le_def,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Prod.forall, vertexLayer]
  apply forall_congr'
  intro i
  tauto

/-- The root-coordinate reconstruction carries the full box exactly to a product box. -/
theorem RootCoordinates.equiv_symm_mem_linkBoxes {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (t : Fin r → ℝ) (u : Fin R.restCount → ℝ) :
    R.equiv.symm (t, u) ∈ univ.pi (fun i => linkBox (Q i)) ↔
      t ∈ R.rootBox Q ∧ u ∈ R.restBox Q := by
  rw [mem_linkBoxes_iff]
  constructor
  · intro h
    constructor
    · constructor <;> intro a
      · simpa only [R.equiv_symm_rootVertex] using (h (R.rootVertex a)).1
      · simpa only [R.equiv_symm_rootVertex] using (h (R.rootVertex a)).2
    · constructor <;> intro k
      · have hk := (h (finProdFinEquiv.symm (R.permutation.symm (Sum.inr k)))).1
        simpa only [R.equiv_symm_apply, Prod.mk.eta, Equiv.apply_symm_apply, Sum.elim_inr] using hk
      · have hk := (h (finProdFinEquiv.symm (R.permutation.symm (Sum.inr k)))).2
        simpa only [R.equiv_symm_apply, Prod.mk.eta, Equiv.apply_symm_apply, Sum.elim_inr] using hk
  · rintro ⟨ht, hu⟩ v
    cases he : R.permutation (finProdFinEquiv v) with
    | inl a =>
        have hv : R.rootVertex a = v := by
          unfold rootVertex
          rw [← he, R.permutation.symm_apply_apply, finProdFinEquiv.symm_apply_apply]
        have hcoord : R.equiv.symm (t, u) v.1 v.2 = t a := by rw [← hv, R.equiv_symm_rootVertex]
        rw [hcoord, ← hv]
        exact ⟨ht.1 a, ht.2 a⟩
    | inr k =>
        have hv : finProdFinEquiv.symm (R.permutation.symm (Sum.inr k)) = v := by
          rw [← he, R.permutation.symm_apply_apply, finProdFinEquiv.symm_apply_apply]
        have hcoord : R.equiv.symm (t, u) v.1 v.2 = u k := by
          rw [R.equiv_symm_apply, Prod.mk.eta, he, Sum.elim_inr]
        rw [hcoord, ← hv]
        exact ⟨hu.1 k, hu.2 k⟩

/-- Each root box has unit volume, with no restriction on the integer layer values. -/
theorem RootCoordinates.volume_rootBox {d n : ℕ} {r : ℕ} (R : RootCoordinates n r) (Q : Fin n → LayerLink d) :
    volume (R.rootBox Q) = 1 := by
  simp only [rootBox, Real.volume_Icc_pi, add_sub_cancel_left, ENNReal.ofReal_one, Finset.prod_const_one]

end WaveTurbulence.Incoh
