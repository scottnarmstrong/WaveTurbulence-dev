/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionSupport
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks

/-! # The three exterior clocks and actual internal CL time coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

abbrev CLInternalTime {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) := ↥(clInteriorBranches R) → ℝ

noncomputable def clLocalClock {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) (t : Fin 3 → ℝ)
    (τ : CLInternalTime R) (v : GBranch G.tree) : ℝ := by
  classical
  exact if ha : v = a then t 0
    else if hv : v ∈ U then τ ⟨v,Finset.mem_erase.mpr ⟨ha,hv⟩⟩
    else if v.toNode = b.child R.positive then t 1
    else if v.toNode = b.child R.negative then t 2 else 0

noncomputable def clBranchClock {w : ℕ} {G : Garden w} (τ : GBranch G.tree → ℝ)
    (x : GNode G.tree) : ℝ := by
  classical
  exact if hb : x.1.2 ∈ (G.tree x.1.1).branching then τ ⟨x.1,hb⟩ else 0

noncomputable def clExternalTimes {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) (τ : GBranch G.tree → ℝ) : Fin 3 → ℝ :=
  ![τ a,clBranchClock τ (b.child R.positive),clBranchClock τ (b.child R.negative)]

noncomputable def clRestrictTime {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) (τ : GBranch G.tree → ℝ) : CLInternalTime R :=
  fun v => τ v.1

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clLocalClock_upper (R : CLRegionData G U a b) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalClock R t τ a = t 0 := dite_eq_left rfl

theorem clLocalClock_internal (R : CLRegionData G U a b) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : ↥(clInteriorBranches R)) : clLocalClock R t τ v.1 = τ v := by
  classical
  have hv := Finset.mem_erase.mp v.2
  exact (dite_eq_right hv.1).trans (dite_eq_left hv.2)

theorem clLocalClock_restrict_region (R : CLRegionData G U a b) (τ : GBranch G.tree → ℝ)
    (v : GBranch G.tree) (hv : v ∈ U) :
    clLocalClock R (clExternalTimes R τ) (clRestrictTime R τ) v = τ v := by
  classical
  by_cases ha : v = a
  · subst v
    exact clLocalClock_upper R _ _
  · exact clLocalClock_internal R _ _ ⟨v,Finset.mem_erase.mpr ⟨ha,hv⟩⟩

theorem clLocalParentClock_restrict (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (τ : GBranch G.tree → ℝ) (top : ℝ) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    parentClock ((clExternalTimes R τ) 0) (clLocalClock R (clExternalTimes R τ) (clRestrictTime R τ)) x =
      parentClock top τ x := by
  obtain ⟨hn,hp⟩ := cl_realization_parent hU R x hx hne
  exact (parentClock_nonroot _ _ x hn).trans
    ((clLocalClock_restrict_region R τ _ hp).trans (parentClock_nonroot top τ x hn).symm)

/-- TARGET regred: only internal branch clocks are integrated. The upper joint's
own parent/window condition belongs to the exterior factor. Lower boundary
inequalities are retained precisely when the excluded child is a branch. -/
noncomputable def clLocalTimeDomain (R : CLRegionData G U a b) (layer : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ) : Set (CLInternalTime R) :=
  {τ | (∀ v : ↥(clInteriorBranches R), (layer v.1 : ℝ) < τ v ∧ τ v < layer v.1+1 ∧ 0 < τ v ∧
    τ v < parentClock (t 0) (clLocalClock R t τ) v.1.toNode) ∧
    ((b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching → t 1 < clLocalClock R t τ b) ∧
    ((b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching → t 2 < clLocalClock R t τ b)}

end WaveTurbulence.RegRed
