/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin4
public import WaveTurbulence.Foundations.Molecule.LFTwist.IdentityData
import Mathlib.Tactic

/-!
# K2 for an LF source and the three pin fields of an LF construction (choice `false`)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

/-- **K2.** Native-coordinate layer agreement between the source and the base of choice `ε`. -/
@[expose] def K2Pins (s : LFSource p kind LG) (ε : Bool) : Prop :=
  (∀ b : GBranch s.skeleton.tree, layerAt LG (s.data.corePosition b) =
    layerAt (s.base ε) ((s.baseData ε).corePosition (s.branches ε b))) ∧
  (∀ b : GBranch s.skeleton.tree, b ≠ s.placement.lower →
    ∀ q ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes,
    layerAt LG (addrExt (inflatedPosition s.skeleton s.data.tree b.toNode) q) =
      layerAt (s.base ε) (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree
        (s.branches ε b).toNode) q)) ∧
  (∀ q : SourcePair s.skeleton, q ≠ s.exceptional → ∀ (i : Fin 2) (r : Path),
    r ∈ ((decodedCouple (s.data.couple q)).tree i).nodes →
    layerAt LG (addrExt (coupleRoot s.data s.plain q i) r) =
      layerAt (s.base ε) (addrExt (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε q) i) r))

theorem k2_false (s : LFSource p kind LG) : K2Pins s false := by
  have hk := k2_normalized (p := p) LG s.data s.plain s.decodes s.placement.lower s.exceptional s.canonical
    s.treeCoherent
  have hbd : s.baseData false = normalizedData s.data s.placement.lower s.exceptional := LFSource.baseData_false s
  refine ⟨?_, ?_, ?_⟩
  · intro b
    rw [hbd]
    exact hk.1 b
  · intro b hb q hq
    rw [hbd]
    exact hk.2.1 b hb q hq
  · intro q hq i r _
    rw [LFSource.pairs_false, hbd]
    exact hk.2.2 q hq i r

end WaveTurbulence.Stage1
