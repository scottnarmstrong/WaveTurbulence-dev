/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.ConditionedPostAdmissibility
public import WaveTurbulence.Foundations.FinalCount.Degen.LatticeLabels
import Mathlib.Tactic

/-! # The fixed-label branch of the corrected degenerate-atom removal -/

@[expose] public section
set_option autoImplicit false
open Finset Set
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Fixed-parameter restriction injection. This helper is consumed below
with the fixed label proved from an actual bridge or a prescribed root. -/
theorem encard_fixed_conditioned_restriction_le (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    {v : V} {e : D} (he : M.atom e = v) (q : Fin d → ℤ)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hc : ∀ z ∈ M.atoms, M.deg z = 4 → c z = 0) (hk0 : ∀ x, k0 (M.mate x) = k0 x)
    (hconstant : ∀ κ, Adm κ → ConstantAt M κ v)
    (hfixed : ∀ κ, M.IsDecoration L w c κ → M.IsRestricted L γ δ w β k0 κ → Adm κ → κ e = q) :
    {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}.encard ≤
      (eraseAtoms M {v}).countE L γ δ w (conditionedPostAdmissibility M L w v e Adm q) := by
  let c' := momentumForCommon M {v} c (w + latticePoint L q)
  let β' := energyForCommon M {v} β (w + latticePoint L q)
  let P := conditionedPostAdmissibility M L w v e Adm q
  let T : Set (RetainedDart M {v} → (Fin d → ℤ)) := {κ' |
    (eraseAtoms M {v}).IsDecoration L w c' κ' ∧
      (eraseAtoms M {v}).IsRestricted L γ δ w β' (fun x => k0 x.val) κ' ∧ P κ'}
  let r := fun κ : D → (Fin d → ℤ) => fun x : RetainedDart M {v} => κ x.val
  have hmap : Set.MapsTo r {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} T := by
    intro κ hκ
    exact restriction_maps_conditioned_source M he L γ δ w Adm c β k0 hc hκ.1 hκ.2.1 hκ.2.2
      (hconstant κ hκ.2.2) (hfixed κ hκ.1 hκ.2.1 hκ.2.2)
  have hinj : Set.InjOn r {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} := by
    intro κ hκ κ' hκ' hr
    apply removal_pair_injective M he hκ.1.1 hκ'.1.1 (hconstant κ hκ.2.2) (hconstant κ' hκ'.2.2)
    exact Prod.ext ((hfixed κ hκ.1 hκ.2.1 hκ.2.2).trans (hfixed κ' hκ'.1 hκ'.2.1 hκ'.2.2).symm) hr
  have hc' := momentumForCommon_zero_at_four M hM {v} c (w + latticePoint L q) hc
  have hk' : ∀ x : RetainedDart M {v}, k0 ((eraseAtoms M {v}).mate x).val = k0 x.val := by
    intro x
    exact hk0 x.val
  exact (Set.encard_le_encard_of_injOn hmap hinj).trans
    (encard_le_countE (eraseAtoms M {v}) L γ δ w P c' β' (fun x => k0 x.val) hc' hk')

/-- A source-prescribed common root label makes countE non-increasing. -/
theorem countE_conditioned_erase_prescribed_label_le (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    {v : V} {e : D} (he : M.atom e = v) (q : Fin d → ℤ)
    (hconstant : ∀ κ, Adm κ → ConstantAt M κ v) (hfixed : ∀ κ, Adm κ → κ e = q) :
    M.countE L γ δ w Adm ≤ (eraseAtoms M {v}).countE L γ δ w (conditionedPostAdmissibility M L w v e Adm q) := by
  conv_lhs => unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  exact encard_fixed_conditioned_restriction_le M hM L γ δ w Adm he q c β k0 hc hk0 hconstant
    (fun κ _ _ ha => hfixed κ ha)

/-- The adopted ONE crossing BOND condition fixes the common label in each
actual parameter set. No root-value or fixed-sum hypothesis is added. -/
theorem countE_conditioned_erase_single_crossing_le_sup (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) {v : V} {e : D} (he : M.atom e = v)
    (hconstant : ∀ κ, Adm κ → ConstantAt M κ v)
    (S : Finset V) (hS : S ⊆ M.atoms) {a : D} (hcut : boundaryDarts M S = {a})
    (ha : M.atom a = v ∨ M.atom (M.mate a) = v) :
    M.countE L γ δ w Adm ≤ (⨆ q : Fin d → ℤ, (eraseAtoms M {v}).countE L γ δ w (conditionedPostAdmissibility M L w v e Adm q)) := by
  classical
  conv_lhs => unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  by_cases hnonempty : ∃ κ, M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ
  · obtain ⟨κ0, hd0, hr0, ha0⟩ := hnonempty
    refine le_trans (encard_fixed_conditioned_restriction_le M hM L γ δ w Adm he (κ0 e) c β k0 hc hk0 hconstant ?_) (le_iSup (fun q : Fin d → ℤ => (eraseAtoms M {v}).countE L γ δ w (conditionedPostAdmissibility M L w v e Adm q)) (κ0 e))
    intro κ hd _hr hadm
    have hphysical := single_boundary_momentum_unique M hd hd0 S hS hcut
    have hlabel : κ a = κ0 a := coset_label_injective hL w hphysical
    have hv := removed_value_eq_common M hd.1 (hconstant κ hadm) he ha
    have hv0 := removed_value_eq_common M hd0.1 (hconstant κ0 ha0) he ha
    exact hv.symm.trans (hlabel.trans hv0)
  · have heq : {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} = ∅ := by
      ext κ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hnonempty ⟨κ, h⟩
    rw [heq, Set.encard_empty]
    exact bot_le

/-- The actual worst conditioned post problem realizes the bridge bound. -/
theorem countE_conditioned_erase_single_crossing_exists_post (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) {v : V} {e : D} (he : M.atom e = v)
    (hconstant : ∀ κ, Adm κ → ConstantAt M κ v)
    (S : Finset V) (hS : S ⊆ M.atoms) {a : D} (hcut : boundaryDarts M S = {a})
    (ha : M.atom a = v ∨ M.atom (M.mate a) = v) :
    ∃ q : Fin d → ℤ, M.countE L γ δ w Adm ≤
      (eraseAtoms M {v}).countE L γ δ w (conditionedPostAdmissibility M L w v e Adm q) := by
  obtain ⟨q, hq⟩ := exists_worst_conditioned_post M hL γ δ w v e Adm
  refine ⟨q, ?_⟩
  rw [hq]
  exact countE_conditioned_erase_single_crossing_le_sup M hM hL.ne' γ δ w Adm he hconstant S hS hcut ha

end WaveTurbulence.Degen
