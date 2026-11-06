/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedContractChart
public import WaveTurbulenceVineParam.VineParamPhysicalGraphChart
public import WaveTurbulenceVineParam.VineParamNormalizedBaseSupport
public import WaveTurbulenceVineParam.VineParamAnchoredOldDifferences
import Mathlib.Tactic

/-! # Geometric cap support and exact old directed physical origins -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β]

/-- Both fixed difference bonds touch one common side of the marked cap.
A crossing bond may be represented on either side. -/
@[expose] def PhysicalGraphChart.CapSupported {ends : β → V×V} {X : VineType} {a b : V}
    (P : PhysicalGraphChart ends X a b) (C : Finset V) : Prop :=
  ∀ i,(((ends (P.differencePair i).1).1 ∈ C ∨ (ends (P.differencePair i).1).2 ∈ C) ∧
    ((ends (P.differencePair i).2).1 ∈ C ∨ (ends (P.differencePair i).2).2 ∈ C)) ∨
    (((ends (P.differencePair i).1).1 ∉ C ∨ (ends (P.differencePair i).1).2 ∉ C) ∧
    ((ends (P.differencePair i).2).1 ∉ C ∨ (ends (P.differencePair i).2).2 ∉ C))

namespace RungSpliceGeometry
variable [DecidableEq β] (G : RungSpliceGeometry V β)

/-- The fixed reference bond always has a physical representative on the
included-joint side, solely because it is incident to that joint. -/
theorem physical_reference_admissible {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b) :
    G.AdmissibleSide P.reference (decide (b ∈ G.cap)) := by
  apply G.admissibleSide_of_endpoint
  by_cases h : b ∈ G.cap
  · simp only [h,decide_true,ite_true]
    rcases P.reference_at with hp | hp
    · exact Or.inl (hp.symm ▸ h)
    · exact Or.inr (hp.symm ▸ h)
  · simp only [h,decide_false]
    rcases P.reference_at with hp | hp
    · exact Or.inl (hp.symm ▸ h)
    · exact Or.inr (hp.symm ▸ h)

/-- Exact old reference in the whole directed source fiber. -/
theorem oldDirectedChart_reference {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b)
    {E : Type} [AddCommGroup E] (g r : E) (k : DirectedRootFiber G.ends a b r) :
    G.oldDirectedChart P.full P.distinct g r k P.full.indexing.shape.x0=g-k.1 P.reference := by
  have h := P.reference_eq g r ((graphContractFiber G.ends a b P.distinct r).symm k)
  change G.oldDirectedChart P.full P.distinct g r k P.full.indexing.shape.x0=
    g-k.1 ((graphBondEquiv G.ends).symm (graphBondEquiv G.ends P.reference)) at h
  simpa only [Equiv.symm_apply_apply] using h

/-- Exact old internal differences in the whole directed source fiber. -/
theorem oldDirectedChart_difference {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b)
    (i : {i : Fin P.full.indexing.shape.n // i ≠ P.full.indexing.shape.x0})
    {E : Type} [AddCommGroup E] (g r : E) (k : DirectedRootFiber G.ends a b r) :
    G.oldDirectedChart P.full P.distinct g r k i.1=
      k.1 (P.differencePair i).1-k.1 (P.differencePair i).2 := by
  have h := P.difference_eq i g r ((graphContractFiber G.ends a b P.distinct r).symm k)
  change G.oldDirectedChart P.full P.distinct g r k i.1=
    k.1 ((graphBondEquiv G.ends).symm (graphBondEquiv G.ends (P.differencePair i).1))-
      k.1 ((graphBondEquiv G.ends).symm (graphBondEquiv G.ends (P.differencePair i).2)) at h
  simpa only [Equiv.symm_apply_apply] using h

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
