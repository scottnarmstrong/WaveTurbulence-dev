/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ForestSet
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# instFintypeGNode

Wave B tier B1 (WaveB1-Core.lean), source: — (Fintype instance for `GNode`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Forest

open TTree
variable {w : ℕ} (tree : Fin w → TTree)

@[instance_reducible, instance] def instFintypeGNode : Fintype (GNode tree) :=
  Fintype.subtype (forestSet tree TTree.nodes) fun a => by
    simp only [forestSet, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    constructor
    · rintro ⟨j, q, hq, rfl⟩
      exact hq
    · intro h
      exact ⟨a.1, a.2, h, rfl⟩

end Forest
end WaveTurbulence
