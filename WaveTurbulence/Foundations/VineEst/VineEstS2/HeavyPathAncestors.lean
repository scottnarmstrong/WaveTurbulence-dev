/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.HeavySuccessor

/-! # Intermediate ancestors on an actual heavy-child step -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem node_depth_lt_of_desc_ne {a b : GNode tree} (hab : a.IsDesc b) (hne : a ≠ b) :
    a.1.2.length < b.1.2.length := by
  have hl := hab.2.length_le
  have hn : a.1.2.length ≠ b.1.2.length := by
    intro he
    exact hne (Subtype.ext (Prod.ext hab.1 (hab.2.eq_of_length he)))
  omega

/-- A branch strictly between a parent and a descendant of its chosen child
is already below that child. This uses actual tree ancestry, not an assumed
path-intersection property. -/
theorem nextHeavyBranch_between {v c z x : GBranch tree}
    (hc : nextHeavyBranch v = some c) (hcx : c.toNode.IsDesc x.toNode)
    (hvz : v.toNode.IsDesc z.toNode) (hzx : z.toNode.IsDesc x.toNode) (hne : z ≠ v) :
    c.toNode.IsDesc z.toNode := by
  rcases ancestors_comparable hcx hzx with hcz | hzc
  · exact hcz
  · have hd := nextHeavyBranch_depth hc
    have hvz' : v.toNode ≠ z.toNode := by
      intro he
      exact hne (show z = v from Subtype.ext (congrArg (fun y : GNode tree => y.1) he.symm))
    have hl := node_depth_lt_of_desc_ne hvz hvz'
    have hz := hzc.2.length_le
    have he : z.toNode = c.toNode := by
      apply Subtype.ext
      apply Prod.ext hzc.1
      apply hzc.2.eq_of_length
      change z.1.2.length = c.1.2.length
      change v.1.2.length < z.1.2.length at hl
      change z.1.2.length ≤ c.1.2.length at hz
      omega
    rw [he]
    exact GNode.isDesc_refl _

end WaveTurbulence.VineEstS2
