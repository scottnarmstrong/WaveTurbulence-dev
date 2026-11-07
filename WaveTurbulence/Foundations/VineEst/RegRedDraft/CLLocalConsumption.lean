/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalFactors

/-! # Regional phase and epsilon consume only the actual local coordinates -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clRegionalEpsilon_restrict (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (κ : GNode G.tree → (Fin d → ℤ)) :
    clRegionalEpsilon G U (clExtendIndices R (fun x => κ x.1)) = clRegionalEpsilon G U κ := by
  classical
  apply Finset.prod_congr rfl
  intro v hv
  unfold epsBranch
  rw [clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 0),
    clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 1),
    clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 2)]

theorem clRegionalPhase_restrict (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (base : Mom d) (κ : GNode G.tree → (Fin d → ℤ))
    (τ : GBranch G.tree → ℝ) :
    clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R (fun x => κ x.1)))
      (clLocalClock R (clExternalTimes R τ) (clRestrictTime R τ)) =
    clRegionalPhase G U L γ δ (cosetDecoration G L base κ) τ := by
  classical
  apply Finset.prod_congr rfl
  intro v hv
  rw [clLocalClock_restrict_region R τ v hv]
  have hnode := cl_realization_mem_support R ((branch_mem_clRealizationNodes v).mpr hv)
  have he : omegaNode G (cosetDecoration G L base (clExtendIndices R (fun x => κ x.1))) v =
      omegaNode G (cosetDecoration G L base κ) v := by
    unfold omegaNode cosetDecoration
    rw [clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 0),
      clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 1),
      clExtendIndices_restrict R κ _ (cl_child_mem_support hU R hv 2),
      clExtendIndices_restrict R κ _ hnode]
  rw [he]

end WaveTurbulence.RegRed
