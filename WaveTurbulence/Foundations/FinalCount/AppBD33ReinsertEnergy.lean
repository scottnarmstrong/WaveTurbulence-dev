/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33ReinsertMomentum
import Mathlib.Tactic

/-! # The single changed energy window in double-pair reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbD33CutEnergy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (β : V → ℝ) : ℝ :=
  (((appbCutSign M r.removedAtoms (r.edge ⟨2,by decide⟩).val)⁻¹ : ℤˣ) : ℤ)*
    (∑ v ∈ r.removedAtoms,β v)

noncomputable def appbD33ReinsertEnergy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (β : V → ℝ) (v : V) : ℝ :=
  β v+if r.vertex 4 = v then (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ)*
    appbD33CutEnergy r β else 0

noncomputable def appbD33ReinsertExactEnergy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} (L : ℝ) (w : Mom d)
    (β : V → ℝ) (κ : D → (Fin d → ℤ)) (v : V) : ℝ :=
  β v+if r.vertex 4 = v then (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ)*
    (‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val‖^2-
      ‖Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖^2) else 0

noncomputable def appbD33DirectedResidualEnergy {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} (L : ℝ) (w : Mom d)
    (β : V → ℝ) (κ : D → (Fin d → ℤ)) : V → ℝ :=
  if M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 3 then
    appbAddedEnergy (r.vertex 3) (r.vertex 4) L w (κ (r.edge ⟨2,by decide⟩).val)
      (Degen.residualEnergy M r.removedAtoms L w β κ)
  else appbAddedEnergy (r.vertex 4) (r.vertex 3) L w (κ (r.edge ⟨2,by decide⟩).val)
      (Degen.residualEnergy M r.removedAtoms L w β κ)

theorem appb_d33_directed_residual_energy_eq {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hOpp : AppbD33BoundaryOpposite M r)
    {d : ℕ} (L : ℝ) (w : Mom d) (β : V → ℝ) (κ : D → (Fin d → ℤ))
    (hκ : ∀ x,κ (M.mate x) = κ x) {v : V} (hv : v ∉ r.removedAtoms) :
    appbD33DirectedResidualEnergy r L w β κ v = appbD33ReinsertExactEnergy r L w β κ v := by
  have hsign := appb_d33_external_signs_opposite r hOpp
  by_cases ha : M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 3
  · have hs3 : appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val = 1 := by simp [appbIncidenceSign,ha]
    have hs4 : appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val = -1 := by
      rw [appb_units_eq_neg_of_ne _ _ hsign,hs3]
    unfold appbD33DirectedResidualEnergy
    rw [if_pos ha]
    unfold appbAddedEnergy appbD33ReinsertExactEnergy
    rw [appb_d33_residual_energy r L w β κ hκ hv,hs3,hs4]
    by_cases hA : r.vertex 3 = v <;> by_cases hB : r.vertex 4 = v
    all_goals simp only [hA,hB,ite_true,ite_false,Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg]
    all_goals try dsimp only [Molecule.kvec]
    all_goals ring
  · have hs3 : appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val = -1 := by simp [appbIncidenceSign,ha]
    have hs4 : appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val = 1 := by
      rw [appb_units_eq_neg_of_ne _ _ hsign,hs3,neg_neg]
    unfold appbD33DirectedResidualEnergy
    rw [if_neg ha]
    unfold appbAddedEnergy appbD33ReinsertExactEnergy
    rw [appb_d33_residual_energy r L w β κ hκ hv,hs3,hs4]
    by_cases hA : r.vertex 3 = v <;> by_cases hB : r.vertex 4 = v
    all_goals simp only [hA,hB,ite_true,ite_false,Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg]
    all_goals try dsimp only [Molecule.kvec]
    all_goals ring

theorem appb_d33_reinsert_energy_center_error {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hOpp : AppbD33BoundaryOpposite M r)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ)
    (v : V) :
    |appbD33ReinsertExactEnergy r L w β κ v-appbD33ReinsertEnergy r β v| ≤
      (if r.vertex 4 = v then (2 : ℝ) else 0)*(δ⁻¹*L^(-2*γ)) := by
  have he := (appbD33CutPair r).energy_difference (appb_d33_cut_signs_opposite M r hOpp)
    L γ δ w c β k0 κ hκ hres
  have hc : r.removedAtoms.card = 2 := by
    change (AppbPatternKind.d33.pattern.removed.image r.vertex).card = 2
    rw [card_image_of_injOn (fun a ha b hb h => r.vertex_injective
      (mem_union_left _ ha) (mem_union_left _ hb) h)]
    decide
  rw [hc] at he
  unfold appbD33ReinsertExactEnergy appbD33ReinsertEnergy
  by_cases hv : r.vertex 4 = v
  · rw [if_pos hv,if_pos hv,if_pos hv]
    have heq : β v+(appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ)*
        (‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val‖^2-‖Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖^2)-
        (β v+(appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ)*appbD33CutEnergy r β) =
        (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ)*
        (‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val‖^2-‖Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖^2-appbD33CutEnergy r β) := by ring
    rw [heq,abs_mul]
    have hunit : |((appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (appbIncidenceSign M (r.vertex 4) (r.edge ⟨3,by decide⟩).val) with h | h <;> rw [h] <;> norm_num
    rw [hunit,one_mul]
    exact he
  · simp only [hv,ite_false,add_zero,sub_self,abs_zero,zero_mul,le_refl]

end WaveTurbulence.Mole
