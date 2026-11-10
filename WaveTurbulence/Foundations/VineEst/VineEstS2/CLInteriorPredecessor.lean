/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInteriorCrop
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignSearchTarget

/-! # The actual same-sign predecessor stays inside the CL interior -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clForestBranch_depth (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : GBranch (CLTreeForest R)) :
    ((clForestBranchEquiv hU R) v).1.1.2.length = a.1.2.length+v.1.2.length := by
  have hp := congrArg (fun x : GNode G.tree => x.1.2) (clForestBranch_node hU R v)
  change a.1.2++v.1.2 = ((clForestBranchEquiv hU R) v).1.1.2 at hp
  rw [← hp,List.length_append]

theorem clPredecessor_mem_interior (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : ↥(clInteriorBranches R)) (u : GBranch (CLTreeForest R))
    (hu : signPredecessor (fun _ : Fin 1 => G.sign a.toNode) (clInteriorCrop hU R v) = some u) :
    ((clForestBranchEquiv hU R) u).1 ∈ clInteriorBranches R := by
  have hd := (signPredecessor_target _ _ _ hu).2.1
  apply Finset.mem_erase.mpr
  refine ⟨?_,((clForestBranchEquiv hU R) u).2⟩
  intro he
  have hl := clForestBranch_depth hU R u
  rw [he] at hl
  omega

noncomputable def clInteriorPredecessor (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v : ↥(clInteriorBranches R)) : Option ↥(clInteriorBranches R) :=
  (signPredecessor (fun _ : Fin 1 => G.sign a.toNode) (clInteriorCrop hU R v)).pmap
    (fun u hu => ⟨((clForestBranchEquiv hU R) u).1,hu⟩) (clPredecessor_mem_interior hU R v)

theorem clInteriorPredecessor_deeper (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (v u : ↥(clInteriorBranches R)) (hu : clInteriorPredecessor hU R v = some u) :
    v.1.1.2.length < u.1.1.2.length := by
  unfold clInteriorPredecessor at hu
  obtain ⟨z,hmem,hz,hzu⟩ := Option.pmap_eq_some_iff.mp hu
  have hd := (signPredecessor_target _ _ _ hz).2.1
  have he := congrArg (fun q : ↥(clInteriorBranches R) => q.1.1.2.length) hzu.symm
  change ((clForestBranchEquiv hU R) z).1.1.2.length = u.1.1.2.length at he
  rw [clForestBranch_depth hU R z] at he
  rw [clInteriorCrop_depth hU R v]
  omega

end WaveTurbulence.VineEstS2
