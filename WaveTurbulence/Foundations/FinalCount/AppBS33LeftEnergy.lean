/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33LeftParameters
public import WaveTurbulence.Foundations.FinalCount.AppBOneWindowCount
import Mathlib.Tactic

/-! # The one enlarged energy window on the 35 component -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_side_reinsert_energy_window {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (p : AppbCountParameters M d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w p.momentum κ) (hres : M.IsRestricted L γ δ w p.energy p.center κ) :
    ∀ v ∈ appbS33Side r,
      |(r.directedPostWithBond 3 5 ⟨1,by decide⟩).Gamma L w (r.reinsertedLabels κ ⟨1,by decide⟩) v-
          (appbS33SideFullParameters r p).energy v| ≤
        (if v = r.vertex 5 then ((appbS33Side r).card+1 : ℝ) else 1)*(δ⁻¹*L^(-2*γ)) := by
  have ht := appb_s33_splitTopology_of_geometry hg
  have h3 := r.vertex_mem_post 3 (by decide) (by decide)
  have h4 := r.vertex_mem_post 5 (by decide) (by decide)
  have hres0 := Degen.isRestricted_eraseAtoms M r.removedAtoms hres
  intro v hv
  have hvret := (appb_residual_closedSide M r.removedAtoms (r.vertex 3)).subset_atoms hv
  have hcompare := appb_s33_side_reinsert_energy_center_error r hg L γ δ w p.momentum p.energy p.center κ hκ hres v
  have hbase : |(r.directedPostWithBond 3 5 ⟨1,by decide⟩).Gamma L w
      (r.reinsertedLabels κ ⟨1,by decide⟩) v-appbS33SideReinsertExactEnergy r L w p.energy κ v| ≤ δ⁻¹*L^(-2*γ) := by
    by_cases ha : M.atom (r.edge ⟨1,by decide⟩).val = r.vertex 3
    · rw [AppbRealization.directedPostWithBond,if_pos ha]
      have hr := appb_isRestricted_addBond r.post (r.vertex 3) (r.vertex 5) h3 h4
        (κ (r.edge ⟨1,by decide⟩).val) hres0
      have he := appb_s33_side_directed_residual_energy_eq r hg L w p.energy κ hκ.1 hv
      simp only [appbS33SideDirectedResidualEnergy,if_pos ha] at he
      have hvN : v ∈ (r.postWithBond 3 5).atoms := mem_insert_of_mem (mem_insert_of_mem hvret)
      have hh := hr.1 v hvN
      rw [he] at hh
      exact hh
    · rw [AppbRealization.directedPostWithBond,if_neg ha]
      have hr := appb_isRestricted_addBond r.post (r.vertex 5) (r.vertex 3) h4 h3
        (κ (r.edge ⟨1,by decide⟩).val) hres0
      have he := appb_s33_side_directed_residual_energy_eq r hg L w p.energy κ hκ.1 hv
      simp only [appbS33SideDirectedResidualEnergy,if_neg ha] at he
      have hvN : v ∈ (r.postWithBond 5 3).atoms := mem_insert_of_mem (mem_insert_of_mem hvret)
      have hh := hr.1 v hvN
      rw [he] at hh
      exact hh
  have htri := abs_sub_le ((r.directedPostWithBond 3 5 ⟨1,by decide⟩).Gamma L w
    (r.reinsertedLabels κ ⟨1,by decide⟩) v) (appbS33SideReinsertExactEnergy r L w p.energy κ v)
    (appbS33SideReinsertEnergy r p.energy v)
  change |_-appbS33SideReinsertEnergy r p.energy v| ≤ _
  by_cases hB : v = r.vertex 5
  · have hB' := hB.symm
    rw [if_pos hB] 
    rw [if_pos hB'] at hcompare
    linarith only [hbase,hcompare,htri]
  · have hB' : r.vertex 5 ≠ v := Ne.symm hB
    rw [if_neg hB]
    rw [if_neg hB'] at hcompare
    linarith only [hbase,hcompare,htri]


end WaveTurbulence.Mole
