/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.TwistCLTransport
public import WaveTurbulence.Foundations.Molecule.TwistBlockTransport

/-! # The CL parent pattern of a chain survives a unit twist at any of its pieces (V5 Step 4a)

M6's `clParentPattern_twistedAtoms` treats a twist at the chain's own lower joint `b = P.lower` with the placement
selected for the whole block.  A chain `U` is twisted at *each* of its pieces, so here the twist may sit at an inner
piece (`b ≠ P.lower`); this is the transport of the CL pattern from `internalPositions_twist_other` at both joints.
The case `b = P.lower` needs only that the retained slot is internal to the block `U` (it is internal to the piece,
hence to `U`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist TTree

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- A twist at a joint-free inner atom transports the CL pattern of a chain (`a, b ≠ P.lower`). -/
theorem clParentPattern_twistedAtoms_inner
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (ha : a ≠ P.lower) (hb : b ≠ P.lower) :
    Mole.CLParentPattern (unitTwistGarden G P) (twistedAtoms G P S)
      (coreBranchEquiv G P a) (coreBranchEquiv G P b) := by
  constructor
  · intro hp
    have hv := (mem_twistedAtoms G P S a).mpr hB.2.1
    have hz := (Mole.zero_mem_internalPositions (unitTwistGarden G P) hv).mpr hp
    have hzold := (internalPositions_twist_other G P S a ha 0).mp hz
    exact hCL.1 ((Mole.zero_mem_internalPositions G hB.2.1).mp hzold)
  · have hv := (mem_twistedAtoms G P S b).mpr hB.2.2.1
    refine (Mole.zero_mem_internalPositions (unitTwistGarden G P) hv).mp ?_
    exact (internalPositions_twist_other G P S b hb 0).mpr
      ((Mole.zero_mem_internalPositions G hB.2.2.1).mpr hCL.2)

/-- A twist at the lower joint of the chain, with the retained slot internal to the block. -/
theorem clParentPattern_twistedAtoms_lower
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hkeep : P.keep.succ ∈ Mole.internalPositions G S P.lower) :
    Mole.CLParentPattern (unitTwistGarden G P) (twistedAtoms G P S)
      (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower) := by
  constructor
  · intro ha
    have hv := (mem_twistedAtoms G P S a).mpr hB.2.1
    have hz := (Mole.zero_mem_internalPositions (unitTwistGarden G P) hv).mpr ha
    have hzold := (internalPositions_twist_other G P S a hB.2.2.2.1 0).mp hz
    exact hCL.1 ((Mole.zero_mem_internalPositions G hB.2.1).mp hzold)
  · refine ⟨(coreBranchEquiv_nonroot G P P.lower).mpr P.nonroot, ?_⟩
    have hmem : GNode.parent (G.pair P.retained).toNode P.paired_nonroot ∈ S := by
      obtain ⟨x, hx, hg, hpos⟩ := (Mole.mem_internalPositions G).mp hkeep
      have he : x = retainedLP G P := Mole.atom_position_injective G
        (Prod.ext (hx.trans (retained_parent G P).symm) (hpos.trans (retainedLP_position G P).symm))
      subst x
      exact hg.2
    exact (lower_new_parent G P).symm ▸ (mem_twistedAtoms G P S _).mpr hmem

/-- A unit twist at any atom `P.lower ≠ a` of the chain transports its CL parent pattern, provided the retained
slot is internal to the block when the twisted atom is the lower joint. -/
theorem clParentPattern_twistedAtoms_chain
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (ha : a ≠ P.lower) (hkeep : P.keep.succ ∈ Mole.internalPositions G S P.lower) :
    Mole.CLParentPattern (unitTwistGarden G P) (twistedAtoms G P S)
      (coreBranchEquiv G P a) (coreBranchEquiv G P b) := by
  by_cases hb : b = P.lower
  · subst hb
    exact clParentPattern_twistedAtoms_lower G P hB hCL hkeep
  · exact clParentPattern_twistedAtoms_inner G P hB hCL ha hb

end WaveTurbulence.VineEstS4
