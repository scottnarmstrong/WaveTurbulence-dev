/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33ReinsertEnergy
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertAdmissibility
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteCounts
import Mathlib.Tactic

/-! # Fixed post parameters and one widened window for double-pair reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbD33ReinsertParameters {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} (p : AppbCountParameters M d) :
    AppbCountParameters (r.directedPostWithBond 3 4 ⟨2,by decide⟩) d where
  momentum := appbD33ReinsertMomentum r p.momentum
  energy := appbD33ReinsertEnergy r p.energy
  center := Sum.elim (fun x => p.center x.val) (fun _ => p.center (r.edge ⟨2,by decide⟩).val)
  center_mate := by
    unfold AppbRealization.directedPostWithBond
    split_ifs
    all_goals rintro (x|t)
    · exact p.center_mate x.val
    · rfl
    · exact p.center_mate x.val
    · rfl

theorem appb_d33_reinsert_energy_window {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hOpp : AppbD33BoundaryOpposite M r)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (p : AppbCountParameters M d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w p.momentum κ) (hres : M.IsRestricted L γ δ w p.energy p.center κ) :
    ∀ v ∈ (r.directedPostWithBond 3 4 ⟨2,by decide⟩).atoms,
      |(r.directedPostWithBond 3 4 ⟨2,by decide⟩).Gamma L w (r.reinsertedLabels κ ⟨2,by decide⟩) v-
          (appbD33ReinsertParameters r p).energy v| ≤
        (if v = r.vertex 4 then (3 : ℝ) else 1)*(δ⁻¹*L^(-2*γ)) := by
  have h3 := r.vertex_mem_post 3 (by decide) (by decide)
  have h4 := r.vertex_mem_post 4 (by decide) (by decide)
  have hres0 := Degen.isRestricted_eraseAtoms M r.removedAtoms hres
  intro v hv
  have hcompare := appb_d33_reinsert_energy_center_error r hOpp L γ δ w p.momentum p.energy p.center κ hκ hres v
  have hbase : |(r.directedPostWithBond 3 4 ⟨2,by decide⟩).Gamma L w
      (r.reinsertedLabels κ ⟨2,by decide⟩) v-appbD33ReinsertExactEnergy r L w p.energy κ v| ≤ δ⁻¹*L^(-2*γ) := by
    by_cases ha : M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 3
    · rw [AppbRealization.directedPostWithBond,if_pos ha] at hv ⊢
      have hvret : v ∈ r.post.atoms := by
        change v ∈ insert (r.vertex 3) (insert (r.vertex 4) r.post.atoms) at hv
        simpa only [insert_eq_of_mem h4,insert_eq_of_mem h3] using hv
      have hr := appb_isRestricted_addBond r.post (r.vertex 3) (r.vertex 4) h3 h4
        (κ (r.edge ⟨2,by decide⟩).val) hres0
      have he := appb_d33_directed_residual_energy_eq r hOpp L w p.energy κ hκ.1 (mem_sdiff.mp hvret).2
      simp only [appbD33DirectedResidualEnergy,if_pos ha] at he
      have hh := hr.1 v hv
      rw [he] at hh
      exact hh
    · rw [AppbRealization.directedPostWithBond,if_neg ha] at hv ⊢
      have hvret : v ∈ r.post.atoms := by
        change v ∈ insert (r.vertex 4) (insert (r.vertex 3) r.post.atoms) at hv
        simpa only [insert_eq_of_mem h3,insert_eq_of_mem h4] using hv
      have hr := appb_isRestricted_addBond r.post (r.vertex 4) (r.vertex 3) h4 h3
        (κ (r.edge ⟨2,by decide⟩).val) hres0
      have he := appb_d33_directed_residual_energy_eq r hOpp L w p.energy κ hκ.1 (mem_sdiff.mp hvret).2
      simp only [appbD33DirectedResidualEnergy,if_neg ha] at he
      have hh := hr.1 v hv
      rw [he] at hh
      exact hh
  have htri := abs_sub_le ((r.directedPostWithBond 3 4 ⟨2,by decide⟩).Gamma L w
    (r.reinsertedLabels κ ⟨2,by decide⟩) v) (appbD33ReinsertExactEnergy r L w p.energy κ v)
    (appbD33ReinsertEnergy r p.energy v)
  change |_-appbD33ReinsertEnergy r p.energy v| ≤ _
  by_cases hB : v = r.vertex 4
  · have hB' := hB.symm
    rw [if_pos hB] 
    rw [if_pos hB'] at hcompare
    linarith only [hbase,hcompare,htri]
  · have hB' : r.vertex 4 ≠ v := Ne.symm hB
    rw [if_neg hB]
    rw [if_neg hB'] at hcompare
    linarith only [hbase,hcompare,htri]

theorem appb_d33_reinsert_spatial {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (p : AppbCountParameters M d) (κ : D → (Fin d → ℤ)) (hres : M.IsRestricted L γ δ w p.energy p.center κ) :
    ∀ x,‖Molecule.kvec L w (r.reinsertedLabels κ ⟨2,by decide⟩) x-
      (appbD33ReinsertParameters r p).center x‖ ≤ 1 := by
  rintro (x|t)
  · exact hres.2 x.val
  · exact hres.2 (r.edge ⟨2,by decide⟩).val

end WaveTurbulence.Mole
