/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulenceVineParam.Contract

/-! # Re-indexing the rungs of a `FullVineChart` (R20 (1))

`FullVineChart.reindex C σ` is the chart obtained from `C` by permuting the rung indices by `σ`; it uses only the
fields of the VINEPARAM contract (`Contract.lean` is not amended).  The slot permutation fixes `x₀` and the
core slots and sends `xSlot j`, `ySlot j` to `xSlot (σ j)`, `ySlot (σ j)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence VineParamContract Finset

variable {X : VineType}

/-- The slot map of a rung permutation (as a function; `slotPerm` packages it as an equivalence). -/
def slotMap (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (i : Fin A.n) : Fin A.n :=
  if h : 1 ≤ i.1 ∧ i.1 ≤ A.m then A.xSlot (σ ⟨i.1 - 1, by omega⟩)
  else if h : A.m + 1 ≤ i.1 ∧ i.1 ≤ 2 * A.m then A.ySlot (σ ⟨i.1 - (A.m + 1), by omega⟩)
  else i

theorem slotMap_x0 (A : Shape X) (σ : Equiv.Perm (Fin A.m)) : slotMap A σ A.x0 = A.x0 := by
  unfold slotMap Shape.x0
  simp

theorem slotMap_xSlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (j : Fin A.m) :
    slotMap A σ (A.xSlot j) = A.xSlot (σ j) := by
  unfold slotMap Shape.xSlot
  have h : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ A.m := ⟨by omega, by have := j.2; omega⟩
  simp only [h, and_self, dite_true]
  congr 2

theorem slotMap_ySlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (j : Fin A.m) :
    slotMap A σ (A.ySlot j) = A.ySlot (σ j) := by
  unfold slotMap Shape.ySlot
  have h : ¬ (1 ≤ A.m + 1 + j.1 ∧ A.m + 1 + j.1 ≤ A.m) := by omega
  have h' : A.m + 1 ≤ A.m + 1 + j.1 ∧ A.m + 1 + j.1 ≤ 2 * A.m := ⟨by omega, by have := j.2; omega⟩
  simp only [h, h', and_self, dite_false, dite_true]
  congr 3
  ext; simp

theorem slotMap_uSlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (hn : X.IsBad = false) (c : Fin 3) :
    slotMap A σ (A.uSlot hn c) = A.uSlot hn c := by
  unfold slotMap Shape.uSlot
  have h : ¬ (1 ≤ 2 * A.m + 1 + c.1 ∧ 2 * A.m + 1 + c.1 ≤ A.m) := by omega
  have h' : ¬ (A.m + 1 ≤ 2 * A.m + 1 + c.1 ∧ 2 * A.m + 1 + c.1 ≤ 2 * A.m) := by omega
  simp only [h, h', dite_false]

theorem slotMap_slotMap (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (i : Fin A.n) :
    slotMap A σ.symm (slotMap A σ i) = i := by
  by_cases h1 : 1 ≤ i.1 ∧ i.1 ≤ A.m
  · have e : i = A.xSlot ⟨i.1 - 1, by omega⟩ := by ext; simp [Shape.xSlot]; omega
    rw [e, slotMap_xSlot, slotMap_xSlot]; simp
  · by_cases h2 : A.m + 1 ≤ i.1 ∧ i.1 ≤ 2 * A.m
    · have e : i = A.ySlot ⟨i.1 - (A.m + 1), by omega⟩ := by ext; simp [Shape.ySlot]; omega
      rw [e, slotMap_ySlot, slotMap_ySlot]; simp
    · have : slotMap A σ i = i := by unfold slotMap; rw [dif_neg h1, dif_neg h2]
      rw [this]
      unfold slotMap; rw [dif_neg h1, dif_neg h2]

/-- The slot permutation of a rung permutation. -/
def slotPerm (A : Shape X) (σ : Equiv.Perm (Fin A.m)) : Equiv.Perm (Fin A.n) where
  toFun := slotMap A σ
  invFun := slotMap A σ.symm
  left_inv i := slotMap_slotMap A σ i
  right_inv i := by simpa using slotMap_slotMap A σ.symm i


theorem slotPerm_x0 (A : Shape X) (σ : Equiv.Perm (Fin A.m)) : slotPerm A σ A.x0 = A.x0 := slotMap_x0 A σ

theorem slotPerm_xSlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (j : Fin A.m) :
    slotPerm A σ (A.xSlot j) = A.xSlot (σ j) := slotMap_xSlot A σ j

theorem slotPerm_ySlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (j : Fin A.m) :
    slotPerm A σ (A.ySlot j) = A.ySlot (σ j) := slotMap_ySlot A σ j

theorem slotPerm_uSlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (hn : X.IsBad = false) (c : Fin 3) :
    slotPerm A σ (A.uSlot hn c) = A.uSlot hn c := slotMap_uSlot A σ hn c

theorem slotPerm_symm_x0 (A : Shape X) (σ : Equiv.Perm (Fin A.m)) : (slotPerm A σ).symm A.x0 = A.x0 := by
  rw [Equiv.symm_apply_eq]; exact (slotPerm_x0 A σ).symm

theorem slotPerm_symm_xSlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (j : Fin A.m) :
    (slotPerm A σ).symm (A.xSlot (σ j)) = A.xSlot j := by
  rw [Equiv.symm_apply_eq]; exact (slotPerm_xSlot A σ j).symm

theorem slotPerm_symm_ySlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (j : Fin A.m) :
    (slotPerm A σ).symm (A.ySlot (σ j)) = A.ySlot j := by
  rw [Equiv.symm_apply_eq]; exact (slotPerm_ySlot A σ j).symm

theorem slotPerm_symm_uSlot (A : Shape X) (σ : Equiv.Perm (Fin A.m)) (hn : X.IsBad = false) (c : Fin 3) :
    (slotPerm A σ).symm (A.uSlot hn c) = A.uSlot hn c := by
  rw [Equiv.symm_apply_eq]; exact (slotPerm_uSlot A σ hn c).symm

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V}

theorem nodeResonance_reindex {d : ℕ} (A : Indexing M X S a b) (σ : Equiv.Perm (Fin A.shape.m))
    (k : Bond M S → Mom d) (g r : Mom d) (i : Fin A.shape.n) :
    nodeResonance (Indexing.mk A.shape ((slotPerm A.shape σ).trans A.atom)
        (by simpa [slotPerm, slotMap_x0] using A.lower) : Indexing M X S a b) k g r i =
      nodeResonance A k g r (slotPerm A.shape σ i) := by
  unfold nodeResonance
  have hx : slotPerm A.shape σ A.shape.x0 = A.shape.x0 := slotMap_x0 A.shape σ
  have : (i = A.shape.x0) ↔ (slotPerm A.shape σ i = A.shape.x0) := by
    constructor
    · rintro rfl; exact hx
    · intro h; exact (slotPerm A.shape σ).injective (h.trans hx.symm)
  simp only [Equiv.trans_apply, this]

/-- **Re-indexing a chart by a permutation of its rungs.**  Only the contract's own fields are used. -/
noncomputable def FullVineChart.reindex (C : FullVineChart M X S a b) (σ : Equiv.Perm (Fin C.indexing.shape.m)) :
    FullVineChart M X S a b where
  indexing := Indexing.mk C.indexing.shape ((slotPerm C.indexing.shape σ).trans C.indexing.atom)
    (by simpa [slotPerm, slotMap_x0] using C.indexing.lower)
  bond_count := C.bond_count
  junction := C.junction.map σ.symm
  junction_type := by simpa using C.junction_type
  rung_bonds := by
    intro j
    have h := C.rung_bonds (σ j)
    have e1 : (slotPerm C.indexing.shape σ) (C.indexing.shape.xSlot j) = C.indexing.shape.xSlot (σ j) :=
      slotMap_xSlot _ _ _
    have e2 : (slotPerm C.indexing.shape σ) (C.indexing.shape.ySlot j) = C.indexing.shape.ySlot (σ j) :=
      slotMap_ySlot _ _ _
    simp only [Equiv.trans_apply, e1, e2, h]
    have key : (C.junction.map σ.symm = some j) ↔ C.junction = some (σ j) := by
      cases C.junction <;> simp [Equiv.symm_apply_eq]
    simp only [key]
  decodeFree := Matrix.of fun e i => C.decodeFree e (slotPerm C.indexing.shape σ i)
  decodeGap := C.decodeGap
  free_unit := fun e i => C.free_unit e _
  chart := fun {E} _ g r => (C.chart g r).trans
    (Equiv.arrowCongr (slotPerm C.indexing.shape σ).symm (Equiv.refl E))
  decode_eq := by
    intro E _ g r x e
    have hs : ((Equiv.arrowCongr (slotPerm C.indexing.shape σ).symm (Equiv.refl E)).symm x) =
        fun i => x ((slotPerm C.indexing.shape σ).symm i) := by
      ext i; simp [Equiv.arrowCongr]
    show ((C.chart g r).symm ((Equiv.arrowCongr (slotPerm C.indexing.shape σ).symm (Equiv.refl E)).symm x)).1 e = _
    rw [C.decode_eq, hs]
    congr 2
    have := Equiv.sum_comp (slotPerm C.indexing.shape σ)
      (fun i => (C.decodeFree e i) • x ((slotPerm C.indexing.shape σ).symm i))
    simpa using this.symm
  difference := by
    intro i
    obtain ⟨p, q, h⟩ := C.difference (slotPerm C.indexing.shape σ i)
    exact ⟨p, q, fun g r k => by simpa [Equiv.arrowCongr] using h g r k⟩
  ζc := fun j c => C.ζc (σ j) c
  ζ_unit := fun j c => C.ζ_unit _ _
  ζ_bad_nonzero := fun h j => C.ζ_bad_nonzero h (σ j)
  coreLinear := C.coreLinear
  coreFirstSign := C.coreFirstSign
  coreSign := C.coreSign
  ξc := C.ξc
  ξ_unit := C.ξ_unit
  joint_phase := by
    intro d g r x
    have := C.joint_phase d g r (x ∘ (slotPerm C.indexing.shape σ).symm)
    erw [nodeResonance_reindex, slotPerm_x0]
    simpa [Equiv.arrowCongr, slotPerm_symm_x0] using this
  rung_t_phase := by
    intro d g r x j
    have := C.rung_t_phase d g r (x ∘ (slotPerm C.indexing.shape σ).symm) (σ j)
    erw [nodeResonance_reindex, slotPerm_xSlot]
    simpa [Equiv.arrowCongr, slotPerm_symm_xSlot, slotPerm_symm_ySlot] using this
  rung_s_phase := by
    intro d g r x j
    have := C.rung_s_phase d g r (x ∘ (slotPerm C.indexing.shape σ).symm) (σ j)
    erw [nodeResonance_reindex, slotPerm_ySlot]
    simpa [Equiv.arrowCongr, slotPerm_symm_xSlot, slotPerm_symm_ySlot] using this
  core_first_phase := by
    intro hn d g r x
    have := C.core_first_phase hn d g r (x ∘ (slotPerm C.indexing.shape σ).symm)
    erw [nodeResonance_reindex, slotPerm_uSlot]
    simpa [Equiv.arrowCongr, slotPerm_symm_uSlot] using this
  core_second_phase := by
    intro hn d g r x
    have := C.core_second_phase hn d g r (x ∘ (slotPerm C.indexing.shape σ).symm)
    erw [nodeResonance_reindex, slotPerm_uSlot]
    simpa [Equiv.arrowCongr, slotPerm_symm_uSlot] using this
  core_sum_phase := by
    intro hn d g r x
    have := C.core_sum_phase hn d g r (x ∘ (slotPerm C.indexing.shape σ).symm)
    simp only [nodeResonance_reindex] at *
    simpa [Equiv.arrowCongr, slotPerm_uSlot, slotPerm_symm_uSlot] using this

end WaveTurbulence.VineEstS2
