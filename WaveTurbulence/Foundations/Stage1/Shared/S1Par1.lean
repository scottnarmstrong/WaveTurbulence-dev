/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cons5
public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin7
import Mathlib.Tactic

/-!
# Parent layers of native positions
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {S : Garden w}

/-- The parent layer of the inflated position of a nonroot skeleton node is the layer of the core of its parent. -/
theorem par_nonroot (N : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS N.garden) (n : GNode S.tree) (hn : n.1.2 ≠ []) :
    parAt N p (inflatedPosition S D.tree n) = layerAt N (D.corePosition (GNode.parent n hn)) := by
  have e := Mole.parent_child_eq_node n hn
  set c := GNode.parent n hn with hc
  set k := n.1.2.getLast hn
  have hpos : inflatedPosition S D.tree n = addrExt (D.corePosition c) [k] := by
    rw [← e]
    exact D.core_child_position c k
  have hmem : (addrExt (D.corePosition c) [k]).2 ∈ (N.garden.tree (addrExt (D.corePosition c) [k]).1).nodes := by
    rw [← hpos]
    exact (D.decodedNode hS hd n).2
  rw [hpos]
  exact parAt_child N p k hmem

end WaveTurbulence.Stage1
