/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
public import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-! # Distinct figure labels and retained next-step labels stay distinct -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem realized_vertex_list_nodup {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (xs : List ℕ) (hxs : xs.Nodup)
    (hmem : ∀ i ∈ xs,i ∈ P.vertices) : (xs.map r.vertex).Nodup :=
  List.Nodup.map_on (fun i hi j hj he => r.vertex_injective (hmem i hi) (hmem j hj) he) hxs

end WaveTurbulence.Mole.AppbAlgorithm
