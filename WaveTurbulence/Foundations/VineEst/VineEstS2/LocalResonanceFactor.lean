/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSlotOrigins

/-! # Literal source resonance as a product of two local incidence differences -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w d : ℕ} {G : Garden w}

/-- The local source factorization also used in LINKS, proved here from
its single branching conservation equation. Both factors compare opposite
incidences at the same original branching node. -/
theorem omegaNode_local_factor (κ : GNode G.tree → Mom d) (v : GBranch G.tree)
    (hc : κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2)) :
    omegaNode G κ v = 2*inner ℝ (κ (v.child 0)-κ v.toNode) (κ v.toNode-κ (v.child 2)) := by
  have hmid : κ (v.child 1) = κ (v.child 0)-κ v.toNode+κ (v.child 2) := by rw [hc]; abel
  unfold omegaNode
  rw [hmid]
  simp only [resFactor,← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
    inner_sub_left,inner_sub_right,real_inner_comm]
  ring

end WaveTurbulence.VineEstS2
