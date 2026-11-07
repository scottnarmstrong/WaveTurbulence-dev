/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.GeneralCircuitDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeBoundaryPatterns
public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarLabels
public import WaveTurbulence.Foundations.FinalCount.MoleProp.CellDeletionGeometry
import Mathlib.Tactic

/-! # DH23 10.1 operation(a): the zero circuit-loss branch

All incident labels are fixed by actual singleton residual boundaries.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem incidentBonds_card_eq_degree_of_loopless (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) (v : V) :
    (Degen.incidentBondsAt M v).card = M.deg v := by
  have he : Degen.selfBondsAt M v = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨ho,hi⟩ := mem_inter.mp hx
    exact hloop x ((mem_filter.mp ho).2.trans (mem_filter.mp hi).2.symm)
  have hh := Degen.card_incident_add_self_eq_deg M v
  simpa only [he,card_empty,add_zero] using hh

/-- Zero circuit loss fixes every actual removed label; hence the relaxed
count cannot increase, with no common-label or zero-charge premise. -/
theorem countEFree_erase_zero_loss_le (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {v : V} (hv : v ∈ M.atoms)
    (hχ : (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) :
    countEFree M L γ δ w Adm ≤ countEFree (Degen.eraseAtoms M {v}) L γ δ w (erasedFreeAdmissibility M {v} Adm) := by
  classical
  have hdrop := circuitRank_erase_singleton_sub_general M hv
  have hinc := incidentBonds_card_eq_degree_of_loopless M hloop v
  have hC : (Degen.newComponents M {v}).card = M.deg v := by rw [hχ,hinc] at hdrop; omega
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}
  by_cases hne : A.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    have hfixed (κ) (hκ : κ ∈ A) : deletedLabels M {v} κ = deletedLabels M {v} κ0 := by
      apply starLabels_injective_on_deleted_fibers M v hκ.1.1 hκ0.1.1
      funext x
      exact incident_labels_unique_of_card_newComponents_eq_degree M hloop hC hL hκ.1 hκ0.1 x.val x.property
    have he : A = {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧
        Adm κ ∧ deletedLabels M {v} κ = deletedLabels M {v} κ0} := by
      ext κ
      constructor
      · intro hκ
        exact ⟨hκ.1,hκ.2.1,hκ.2.2,hfixed κ hκ⟩
      · intro hκ
        exact ⟨hκ.1,hκ.2.1,hκ.2.2.1⟩
    change A.encard ≤ _
    rw [he]
    exact fixed_deleted_fiber_encard_le M {v} L γ δ w Adm c β k0 hk0 _
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he,Set.encard_empty]
    exact bot_le

/-- The full normalized zero-loss operation(a), with actual ladder
invariance proved from its priority condition. -/
theorem countAFree_erase_zero_loss_le (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {v : V} (hv : v ∈ M.atoms)
    (hdeg : M.deg v ≤ 3)
    (hno : ¬ ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2)
    (hχ : (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P ≤
      countAFree (Degen.eraseAtoms M {v}) L γ δ C1 w (erasedFreeAdmissibility M {v} Adm) P := by
  have hcells := ladderCells_erase_eq_of_no_operation_b M hM hv hdeg hno
  have hprod : cellProduct (Degen.eraseAtoms M {v}) L γ δ P = cellProduct M L γ δ P := by
    unfold cellProduct
    rw [hcells]
  unfold countAFree
  rw [hχ,hprod]
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono (countEFree_erase_zero_loss_le M hloop hv hχ hL γ δ w Adm)) bot_le

end WaveTurbulence.MoleProp
