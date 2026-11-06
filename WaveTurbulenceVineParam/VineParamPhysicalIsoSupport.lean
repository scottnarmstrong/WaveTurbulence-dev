/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamPhysicalGraphIso
public import WaveTurbulenceVineParam.VineParamPhysicalChartSupport
import Mathlib.Tactic

/-! # Exact cap support transports with the actual directed graph -/

public section
namespace WaveTurbulence.Vine.Param.DirectedGraphIso
open Finset VineParamContract
variable {V W β δ : Type*} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] [Fintype β] [Fintype δ]
  {ends : β → V×V} {other : δ → W×W} (I : DirectedGraphIso ends other)

/-- Relabeling retains every physical difference's common geometric side. -/
theorem physicalChart_capSupported {X : VineType} {a b : V}
    (P : PhysicalGraphChart ends X a b) (C : Finset V) (C' : Finset W)
    (hC : ∀ v,I.atom v ∈ C' ↔ v ∈ C) (hP : P.CapSupported C) :
    (I.physicalChart P).CapSupported C' := by
  intro i
  change (((other (I.edge (P.differencePair i).1)).1 ∈ C' ∨
      (other (I.edge (P.differencePair i).1)).2 ∈ C') ∧
    ((other (I.edge (P.differencePair i).2)).1 ∈ C' ∨
      (other (I.edge (P.differencePair i).2)).2 ∈ C')) ∨
    (((other (I.edge (P.differencePair i).1)).1 ∉ C' ∨
      (other (I.edge (P.differencePair i).1)).2 ∉ C') ∧
    ((other (I.edge (P.differencePair i).2)).1 ∉ C' ∨
      (other (I.edge (P.differencePair i).2)).2 ∉ C'))
  rw [I.endpoints,I.endpoints]
  simpa only [hC] using hP i

/-- Actual paired atoms retain uniform membership of every transported cap. -/
theorem physicalChart_pair_uniform {X : VineType} {a b : V}
    (P : PhysicalGraphChart ends X a b) (C : Finset V) (C' : Finset W)
    (hC : ∀ v,I.atom v ∈ C' ↔ v ∈ C)
    (hP : ∀ j : Fin P.full.indexing.shape.m,
      (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ C ↔
        (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ C) :
    ∀ j : Fin (I.physicalChart P).full.indexing.shape.m,
      ((I.physicalChart P).full.indexing.atom ((I.physicalChart P).full.indexing.shape.xSlot j)).1 ∈ C' ↔
        ((I.physicalChart P).full.indexing.atom ((I.physicalChart P).full.indexing.shape.ySlot j)).1 ∈ C' := by
  intro j
  change I.atom (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ C' ↔
    I.atom (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ C'
  rw [hC,hC]
  exact hP j

end WaveTurbulence.Vine.Param.DirectedGraphIso
