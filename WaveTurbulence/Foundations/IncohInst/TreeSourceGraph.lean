/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeLinkCoordinates
public import WaveTurbulence.Foundations.IncohInst.InternalTimeDomain
public import WaveTurbulence.Foundations.IncohInst.ClockTransport
public import WaveTurbulence.Foundations.Incoh.GraphTreeComparison
public import WaveTurbulence.Foundations.Incoh.ClockHyperplanes

/-! # The finite actual tree clock graph and its literal source domain -/

public section
noncomputable section
open scoped Classical
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- The exact branching-child/branching-parent edges in actual link coordinates. -/
@[expose] def treeClockEdges {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    Finset (((Fin (X.treeLinks (G.sig 0)).length × Fin 2)) ×
      ((Fin (X.treeLinks (G.sig 0)).length × Fin 2))) :=
  Finset.univ.filter fun vw => (treeLinkEquiv hX vw.1).IsChildOf (treeLinkEquiv hX vw.2)

@[simp] theorem mem_treeClockEdges {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (v w : Fin (X.treeLinks (G.sig 0)).length × Fin 2) :
    (v, w) ∈ treeClockEdges hX ↔ (treeLinkEquiv hX v).IsChildOf (treeLinkEquiv hX w) := by
  simp only [treeClockEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Source graph edges always connect distinct actual clocks. -/
theorem treeClockEdges_ne {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {v w : Fin (X.treeLinks (G.sig 0)).length × Fin 2} (h : (v,w) ∈ treeClockEdges hX) : v ≠ w := by
  intro he
  subst w
  obtain ⟨_, j, hp⟩ := (mem_treeClockEdges hX v v).mp h
  have hl := congrArg List.length hp
  simp only [List.length_append, List.length_singleton] at hl
  omega

/-- Almost every actual branching clock vector avoids all graph-edge equality hyperplanes. -/
theorem ae_treeClockEdges_ne {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    ∀ᵐ t : (Fin (X.treeLinks (G.sig 0)).length × Fin 2) → ℝ,
      ∀ v w, (v,w) ∈ treeClockEdges hX → t v ≠ t w := by
  apply ae_all_iff.mpr
  intro v
  apply ae_all_iff.mpr
  intro w
  by_cases he : (v,w) ∈ treeClockEdges hX
  · filter_upwards [ae_clock_ne_clock v w (treeClockEdges_ne hX he)] with t ht
    exact fun _ => ht
  · exact Filter.Eventually.of_forall fun _ h => False.elim (he h)

end WaveTurbulence.IncohInst
