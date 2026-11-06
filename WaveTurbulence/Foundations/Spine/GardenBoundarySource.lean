/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.GardenConservation
import Mathlib.Tactic

/-! # Explicit boundary source formula for the garden decoration correspondence -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (G : Garden w)

/-- Boundary value at any node: a root receives its prescribed vector;
a nonroot leaf paired to a root receives that root vector; all other
nodes have zero boundary value. -/
@[expose] def rootBoundaryValue (n : Fin w → E) (a : GNode G.tree) : E :=
  if a.1.2 = [] then n a.1.1
  else if hl : a.1.2 ∈ (G.tree a.1.1).leaves then
    let l : GLeaf G.tree := ⟨a.1,hl⟩
    if (G.pair l).1.2 = [] then n (G.pair l).1.1 else 0
  else 0

omit [Module ℝ E] in
/-- Setting all bond labels to zero gives exactly the root boundary data,
not an additional free conservation parameter. -/
theorem extend_zero_eq_rootBoundary (hP : G.IsPlain) (n : Fin w → E) :
    extendLabels G hP n (fun _ => 0) = rootBoundaryValue G n := by
  funext a
  by_cases hr : a.1.2 = []
  · simp [extendLabels,rootBoundaryValue,hr]
  · by_cases hb : a.1.2 ∈ (G.tree a.1.1).branching
    · have hl : a.1.2 ∉ (G.tree a.1.1).leaves :=
        fun hl => TTree.not_mem_branching_of_mem_leaves _ hl hb
      simp [extendLabels,rootBoundaryValue,hr,hb,hl]
    · have hl : a.1.2 ∈ (G.tree a.1.1).leaves :=
        ((TTree.mem_nodes_iff _ _).mp a.2).resolve_right hb
      simp only [extendLabels,rootBoundaryValue,hr,hb,hl,↓reduceDIte,↓reduceIte]
      split <;> simp_all

/-- TARGET `molecv`: the source is the negative signed sum of the prescribed
root slots, with zero contribution from every interior bond slot. -/
theorem gardenSource_eq_boundary (hP : G.IsPlain) (n : Fin w → E) (v : GBranch G.tree) :
    gardenSource G hP n v =
      -∑ i : Fin 4, slotWeight G v i • rootBoundaryValue G n (slotNode G v i) := by
  rw [gardenSource,extend_zero_eq_rootBoundary,slotSum]

end WaveTurbulence.Mole
