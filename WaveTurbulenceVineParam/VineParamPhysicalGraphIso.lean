/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedGraphIso
public import WaveTurbulenceVineParam.VineParamPhysicalGraphChart
import Mathlib.Tactic

/-! # Reindexing complete physical charts along actual graph isomorphisms -/

public section
namespace WaveTurbulence.Vine.Param.DirectedGraphIso
open Finset VineParamContract
variable {V W β δ : Type*} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] [Fintype β] [Fintype δ]
  {ends : β → V×V} {other : δ → W×W} (I : DirectedGraphIso ends other)

/-- The graph-isomorphism fiber map preserves each actual bond label. -/
theorem bondModelFiber_label (a b : V) (hab : a ≠ b)
    {E : Type} [AddCommGroup E] (r : E)
    (k : FlowFiber (graphMolecule other) univ (I.atom a) (I.atom b) E r) (e : β) :
    (I.bondModel.contractFiber a b hab r k).1 (graphBondEquiv ends e)=
      k.1 (graphBondEquiv other (I.edge e)) := by
  change k.1 (graphBondEquiv other (I.edge ((graphBondEquiv ends).symm (graphBondEquiv ends e))))=_
  rw [Equiv.symm_apply_apply]

/-- The full chart and its fixed physical origins transport together.
This helper changes only the exact atom/bond enumeration. -/
@[expose] noncomputable def physicalChart {X : VineType} {a b : V}
    (P : PhysicalGraphChart ends X a b) : PhysicalGraphChart other X (I.atom a) (I.atom b) where
  distinct := fun h => P.distinct (I.atom.injective h)
  full := I.bondModel.pullFullChart P.full P.distinct
  reference := I.edge P.reference
  reference_at := by
    rw [I.endpoints]
    exact P.reference_at.imp (congrArg I.atom) (congrArg I.atom)
  reference_eq := by
    intro E _ g r k
    have h := P.reference_eq g r (I.bondModel.contractFiber a b P.distinct r k)
    rw [I.bondModelFiber_label] at h
    exact h
  reference_column := by
    intro e
    exact P.reference_column (I.bondModel.contractEdge.symm e)
  differencePair i := (I.edge (P.differencePair i).1,I.edge (P.differencePair i).2)
  difference_eq := by
    intro i E _ g r k
    have h := P.difference_eq i g r (I.bondModel.contractFiber a b P.distinct r k)
    rw [I.bondModelFiber_label,I.bondModelFiber_label] at h
    exact h

end WaveTurbulence.Vine.Param.DirectedGraphIso
