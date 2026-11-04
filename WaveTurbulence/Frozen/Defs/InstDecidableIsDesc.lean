/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIsDesc
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# instDecidableIsDesc

Wave B tier B1 (WaveB1-Core.lean), source: — (Decidable instance for `IsDesc`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Forest

open TTree
variable {w : ℕ} (tree : Fin w → TTree)
variable {tree}

@[instance_reducible, instance] def instDecidableIsDesc (a a' : GNode tree) : Decidable (a.IsDesc a') :=
  inferInstanceAs (Decidable (_ ∧ _))

end Forest
end WaveTurbulence
