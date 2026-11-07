/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalSmallBoundaryEffects
public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
import Mathlib.Tactic

/-! # The two-rail deletion retains its current connected component -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_post_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hc : ∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b)
    (hb : ∀ e : D,¬Degen.IsBridge M e) :
    ∀ a ∈ r.post.atoms,∀ b ∈ r.post.atoms,r.post.SameComponent a b := by
  have he := (global_small_boundary_graph_effects M .d33 (by decide) r hb (by decide) (by decide)).1
  have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hc
  have hf : r.post.numComponents = 1 := he.trans hm
  intro a ha b hb
  exact appb_connected_of_numComponents_eq_one r.post hf ha hb

end WaveTurbulence.Mole.AppbAlgorithm
