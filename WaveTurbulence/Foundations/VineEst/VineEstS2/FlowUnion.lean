/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.BondUnion

/-! # Exact flow splitting and gluing over a source concatenation -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract Finset RegRed
variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {S T : Finset V} {a b c : V}

/-- Full internal flow is the sum of the two actual piece flows. -/
theorem flow_union {E : Type*} [AddCommGroup E] (hM : M.IsMolecule)
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) (k : Bond M (S ∪ T) → E) (v : V) :
    flow M (S ∪ T) k v =
      flow M S (restrictBondLabels Finset.subset_union_left k) v +
      flow M T (restrictBondLabels Finset.subset_union_right k) v := by
  classical
  let e := bondUnionEquiv hM hS hT hi hU
  calc
    _ = ∑ z : Bond M S ⊕ Bond M T, incidence M v (e z).1 • k (e z) :=
      (e.sum_comp (fun q => incidence M v q.1 • k q)).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      rfl

noncomputable def glueBondLabels {E : Type*} (hM : M.IsMolecule)
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) (kS : Bond M S → E) (kT : Bond M T → E) : Bond M (S ∪ T) → E :=
  fun e => Sum.elim kS kT ((bondUnionEquiv hM hS hT hi hU).symm e)

theorem restrict_glueBondLabels_left {E : Type*} (hM : M.IsMolecule)
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) (kS : Bond M S → E) (kT : Bond M T → E) :
    restrictBondLabels Finset.subset_union_left (glueBondLabels hM hS hT hi hU kS kT) = kS := by
  funext e
  change Sum.elim kS kT ((bondUnionEquiv hM hS hT hi hU).symm
    ((bondUnionEquiv hM hS hT hi hU) (.inl e))) = kS e
  rw [Equiv.symm_apply_apply]
  rfl

theorem restrict_glueBondLabels_right {E : Type*} (hM : M.IsMolecule)
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) (kS : Bond M S → E) (kT : Bond M T → E) :
    restrictBondLabels Finset.subset_union_right (glueBondLabels hM hS hT hi hU kS kT) = kT := by
  funext e
  change Sum.elim kS kT ((bondUnionEquiv hM hS hT hi hU).symm
    ((bondUnionEquiv hM hS hT hi hU) (.inr e))) = kT e
  rw [Equiv.symm_apply_apply]
  rfl

theorem glue_restrictBondLabels {E : Type*} (hM : M.IsMolecule)
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) (k : Bond M (S ∪ T) → E) :
    glueBondLabels hM hS hT hi hU (restrictBondLabels Finset.subset_union_left k)
      (restrictBondLabels Finset.subset_union_right k) = k := by
  funext e
  obtain ⟨z,rfl⟩ := (bondUnionEquiv hM hS hT hi hU).surjective e
  unfold glueBondLabels
  rw [Equiv.symm_apply_apply]
  cases z <;> rfl

theorem flow_glueBondLabels {E : Type*} [AddCommGroup E] (hM : M.IsMolecule)
    (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) (kS : Bond M S → E) (kT : Bond M T → E) (v : V) :
    flow M (S ∪ T) (glueBondLabels hM hS hT hi hU kS kT) v = flow M S kS v+flow M T kT v := by
  rw [flow_union hM hS hT hi hU,restrict_glueBondLabels_left,restrict_glueBondLabels_right]

end WaveTurbulence.VineEstS2
