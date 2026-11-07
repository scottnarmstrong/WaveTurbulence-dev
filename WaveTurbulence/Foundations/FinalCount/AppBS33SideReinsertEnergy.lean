/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SideReinsertMomentum
import Mathlib.Tactic

/-! # The single changed energy window in the 35 side after reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33SideCutEnergy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (β : V → ℝ) : ℝ :=
  (((appbCutSign M (appbS33Side r) (r.edge ⟨1,by decide⟩).val)⁻¹ : ℤˣ) : ℤ)*
    (∑ v ∈ appbS33Side r,β v)

noncomputable def appbS33SideReinsertEnergy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (β : V → ℝ) (v : V) : ℝ :=
  β v+if r.vertex 5 = v then (appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val : ℤ)*
    appbS33SideCutEnergy r β else 0

noncomputable def appbS33SideReinsertExactEnergy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ} (L : ℝ) (w : Mom d)
    (β : V → ℝ) (κ : D → (Fin d → ℤ)) (v : V) : ℝ :=
  β v+if r.vertex 5 = v then (appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val : ℤ)*
    (‖Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val‖^2-
      ‖Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖^2) else 0

noncomputable def appbS33SideDirectedResidualEnergy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ} (L : ℝ) (w : Mom d)
    (β : V → ℝ) (κ : D → (Fin d → ℤ)) : V → ℝ :=
  if M.atom (r.edge ⟨1,by decide⟩).val = r.vertex 3 then
    appbAddedEnergy (r.vertex 3) (r.vertex 5) L w (κ (r.edge ⟨1,by decide⟩).val)
      (Degen.residualEnergy M r.removedAtoms L w β κ)
  else appbAddedEnergy (r.vertex 5) (r.vertex 3) L w (κ (r.edge ⟨1,by decide⟩).val)
      (Degen.residualEnergy M r.removedAtoms L w β κ)

theorem appb_s33_side_directed_residual_energy_eq {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (L : ℝ) (w : Mom d) (β : V → ℝ) (κ : D → (Fin d → ℤ))
    (hκ : ∀ x,κ (M.mate x) = κ x) {v : V} (hv : v ∈ appbS33Side r) :
    appbS33SideDirectedResidualEnergy r L w β κ v = appbS33SideReinsertExactEnergy r L w β κ v := by
  have ht := appb_s33_splitTopology_of_geometry hg
  have hsign := appb_s33_external_signs_opposite r hg.2.2.2.1
  by_cases ha : M.atom (r.edge ⟨1,by decide⟩).val = r.vertex 3
  · have hs3 : appbIncidenceSign M (r.vertex 3) (r.edge ⟨1,by decide⟩).val = 1 := by simp [appbIncidenceSign,ha]
    have hs4 : appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val = -1 := by
      rw [appb_units_eq_neg_of_ne _ _ hsign,hs3]
    unfold appbS33SideDirectedResidualEnergy
    rw [if_pos ha]
    unfold appbAddedEnergy appbS33SideReinsertExactEnergy
    rw [appb_s33_side_residual_energy r ht L w β κ hκ hv,hs3,hs4]
    by_cases hA : r.vertex 3 = v <;> by_cases hB : r.vertex 5 = v
    all_goals simp only [hA,hB,ite_true,ite_false,Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg]
    all_goals try dsimp only [Molecule.kvec]
    all_goals ring
  · have hs3 : appbIncidenceSign M (r.vertex 3) (r.edge ⟨1,by decide⟩).val = -1 := by simp [appbIncidenceSign,ha]
    have hs4 : appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val = 1 := by
      rw [appb_units_eq_neg_of_ne _ _ hsign,hs3,neg_neg]
    unfold appbS33SideDirectedResidualEnergy
    rw [if_neg ha]
    unfold appbAddedEnergy appbS33SideReinsertExactEnergy
    rw [appb_s33_side_residual_energy r ht L w β κ hκ hv,hs3,hs4]
    by_cases hA : r.vertex 3 = v <;> by_cases hB : r.vertex 5 = v
    all_goals simp only [hA,hB,ite_true,ite_false,Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg]
    all_goals try dsimp only [Molecule.kvec]
    all_goals ring

theorem appb_s33_side_reinsert_energy_center_error {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ)
    (v : V) :
    |appbS33SideReinsertExactEnergy r L w β κ v-appbS33SideReinsertEnergy r β v| ≤
      (if r.vertex 5 = v then ((appbS33Side r).card : ℝ) else 0)*(δ⁻¹*L^(-2*γ)) := by
  have ht := appb_s33_splitTopology_of_geometry hg
  have he := (appbS33TopologyCutPair r ht).energy_difference
    ((appb_s33_topology_first_signs_iff M r ht).mpr hg.2.2.2.1)
    L γ δ w c β k0 κ hκ hres
  unfold appbS33SideReinsertExactEnergy appbS33SideReinsertEnergy
  by_cases hv : r.vertex 5 = v
  · rw [if_pos hv,if_pos hv,if_pos hv]
    have heq : β v+(appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val : ℤ)*
        (‖Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val‖^2-‖Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖^2)-
        (β v+(appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val : ℤ)*appbS33SideCutEnergy r β) =
        (appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val : ℤ)*
        (‖Molecule.kvec L w κ (r.edge ⟨1,by decide⟩).val‖^2-‖Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖^2-appbS33SideCutEnergy r β) := by ring
    rw [heq,abs_mul]
    have hunit : |((appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (appbIncidenceSign M (r.vertex 5) (r.edge ⟨3,by decide⟩).val) with h | h <;> rw [h] <;> norm_num
    rw [hunit,one_mul]
    exact he
  · simp only [hv,ite_false,add_zero,sub_self,abs_zero,zero_mul,le_refl]

end WaveTurbulence.Mole
