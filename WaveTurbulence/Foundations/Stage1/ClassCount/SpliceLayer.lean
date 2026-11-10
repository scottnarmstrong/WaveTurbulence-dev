/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.LayerCnt.LayerRange
import Mathlib.Tactic

/-!
# CLASSCOUNT: a branch pre-layering of the skeleton induces one on the spliced garden

For a branch pre-layering `f` of `S`, `f ∘ ob` is a branch pre-layering of `G_sb = stSt S σ` (TARGET L1958): layers do not
increase from a unit representative to the atoms of the unit (`layer_le_upper`), and `ob` intertwines parents up to `repC`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt

variable {w : ℕ}

/-- B1b (Mk-general form of `layer_le_repC`). -/
theorem layer_le_repCMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {f : GBranch S.tree → ℕ} (hf : LFTwist.IsBranchPrelayering S f) (v : GBranch S.tree) {Mk : Set (Stage1.CLVine _)} :
    f v ≤ f (repC (stSt (Mk := Mk) S σ).cls v) := by
  by_cases h : ∃ u ∈ unitBlocks (Mk := Mk) S σ, v ∈ u.atoms
  · obtain ⟨u, hu, hv⟩ := h
    rw [stSt_repC_memMk (Mk := Mk) hM σ hu hv]
    exact layer_le_upper S u.isBlock u.cl hf v hv
  · push_neg at h
    rw [stSt_repC_noneMk (Mk := Mk) hM σ h]

/-- B1b (Mk-general form of `ob_prelayering`). -/
theorem ob_prelayeringMk (S : Garden w) (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {f : GBranch S.tree → ℕ} (hf : LFTwist.IsBranchPrelayering S f) {Mk : Set (Stage1.CLVine _)} :
    LFTwist.IsBranchPrelayering (stSt (Mk := Mk) S σ).G (f ∘ (stSt (Mk := Mk) S σ).M.ob) := by
  intro b c i hc
  have hn : c.1.2 ≠ [] := by
    have := congrArg (fun x : GNode (stSt (Mk := Mk) S σ).G.tree => x.1.2) hc
    simp [GBranch.toNode, GBranch.child] at this
    rw [this]; simp
  have hpar : GNode.parent c.toNode hn = b := by
    apply Subtype.ext
    have := congrArg (fun x : GNode (stSt (Mk := Mk) S σ).G.tree => x.1) hc
    simp [GBranch.toNode, GBranch.child] at this
    change (c.1.1, c.1.2.dropLast) = b.1
    rw [this]
    simp
  have ho : ((stSt (Mk := Mk) S σ).M.ob c).1.2 ≠ [] := fun h => hn (((stSt (Mk := Mk) S σ).M.ob_root c).1 h)
  have h1 := (stSt (Mk := Mk) S σ).M.ob_parent c hn ho
  rw [hpar] at h1
  simp only [Function.comp]
  rw [h1]
  have h2 : f ((stSt (Mk := Mk) S σ).M.ob c) ≤ f (GNode.parent ((stSt (Mk := Mk) S σ).M.ob c).toNode ho) := by
    have := hf (GNode.parent ((stSt (Mk := Mk) S σ).M.ob c).toNode ho) ((stSt (Mk := Mk) S σ).M.ob c)
      (((stSt (Mk := Mk) S σ).M.ob c).1.2.getLast ho)
    refine this ?_
    exact (Mole.parent_child_eq_node ((stSt (Mk := Mk) S σ).M.ob c).toNode ho).symm
  exact h2.trans (layer_le_repCMk (Mk := Mk) S hM σ hf _)

end WaveTurbulence.ClassCount
