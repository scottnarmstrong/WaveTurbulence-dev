/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR32SplitSide
public import WaveTurbulence.Foundations.FinalCount.AppBCutPairOfCrossing
public import WaveTurbulence.Foundations.FinalCount.AppBCombinedCoordinates
import Mathlib.Tactic

/-! # The proven two-bond 3R-2G cut in combined local coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbR32CutPair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms)
    (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin AppbPatternKind.r3.pattern.edges.length)
    (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val}) :
    AppbCutPair (r.combinedRemoval s v0) S :=
  appbCutPairOfCrossing (r.combinedRemoval s v0) S
    (fun v hv => (mem_sdiff.mp (hS hv)).1) (r.combinedLeftIndex s j) (r.combinedRightIndex s ⟨0,by decide⟩)
    (r.combinedLeftRight_ne s _ _) (by rw [r.combined_edge_left,r.combined_edge_right]; exact hcross)

end WaveTurbulence.Mole
