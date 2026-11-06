/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphContractFiber
public import WaveTurbulenceVineParam.VineParamDirectedBondFiber
public import WaveTurbulenceVineParam.VineParamDirectedBondAtoms
public import WaveTurbulenceVineParam.VineParamDirectedBondCounts
import Mathlib.Tactic

/-! # Pulling the exact full-chart data from a graph model to an actual molecule -/

public section
namespace WaveTurbulence.Vine.Param.DirectedBondModel
open Finset VineParamContract
variable {V D A β : Type*} [DecidableEq V] [Fintype D] [DecidableEq A] [Fintype A] [Fintype β]
  {M : Molecule V D} {S : Finset V}
variable (Q : DirectedBondModel M S A β)

/-- Every outgoing graph bond corresponds to its individually marked
actual internal bond, with no decoration-dependent choices. -/
@[expose] noncomputable def contractEdge : Bond (graphMolecule Q.ends) univ ≃ Bond M S :=
  (graphBondEquiv Q.ends).symm.trans Q.edge

/-- Actual and graph contract source fibers agree completely. -/
@[expose] noncomputable def contractFiber {E : Type} [AddCommGroup E] (a b : A) (hab : a ≠ b) (r : E) :
    FlowFiber M S (Q.atom a).1 (Q.atom b).1 E r ≃ FlowFiber (graphMolecule Q.ends) univ a b E r :=
  (Q.rootFiberEquiv a b hab r).trans (graphContractFiber Q.ends a b hab r).symm

/-- Included-atom indexing transports literally through the fixed atom realization. -/
@[expose, reducible] noncomputable def pullIndexing {X : VineType} {a b : A}
    (I : Indexing (graphMolecule Q.ends) X univ a b) : Indexing M X S (Q.atom a).1 (Q.atom b).1 where
  shape := I.shape
  atom := I.atom.trans (Q.erasedAtomEquiv a)
  lower := by
    change (Q.atom (I.atom I.shape.x0).1).1=(Q.atom b).1
    rw [I.lower]

/-- Pull back an already produced graph chart on the entire actual source fiber. -/
@[expose] noncomputable def pullChart {X : VineType} {a b : A}
    (F : FullVineChart (graphMolecule Q.ends) X univ a b) (hab : a ≠ b)
    {E : Type} [AddCommGroup E] (g r : E) :
    FlowFiber M S (Q.atom a).1 (Q.atom b).1 E r ≃ (Fin F.indexing.shape.n → E) :=
  (Q.contractFiber a b hab r).trans (F.chart g r)

/-- Exact actual labels of the pulled-back full inverse. -/
theorem pullChart_decode {X : VineType} {a b : A}
    (F : FullVineChart (graphMolecule Q.ends) X univ a b) (hab : a ≠ b)
    {E : Type} [AddCommGroup E] (g r : E) (x : Fin F.indexing.shape.n → E) (e : Bond M S) :
    ((Q.pullChart F hab g r).symm x).1 e=
      ((F.chart g r).symm x).1 (Q.contractEdge.symm e) := rfl

/-- Exact actual atom value at every transported included coordinate. -/
theorem pullIndexing_atom {X : VineType} {a b : A}
    (I : Indexing (graphMolecule Q.ends) X univ a b) (i : Fin I.shape.n) :
    ((Q.pullIndexing I).atom i).1=(Q.atom (I.atom i).1).1 := rfl

/-- Source graph and actual molecule resonances agree at every included
coordinate, with the same actual boundary correction at the joint. -/
theorem nodeResonance_pullChart {X : VineType} {a b : A}
    (F : FullVineChart (graphMolecule Q.ends) X univ a b) (hab : a ≠ b)
    (d : ℕ) (g r : Mom d) (x : Fin F.indexing.shape.n → Mom d) (i : Fin F.indexing.shape.n) :
    nodeResonance (Q.pullIndexing F.indexing) ((Q.pullChart F hab g r).symm x).1 g r i=
      nodeResonance F.indexing ((F.chart g r).symm x).1 g r i := by
  change energy M S ((Q.pullChart F hab g r).symm x).1 (Q.atom (F.indexing.atom i).1).1+
    (if i=F.indexing.shape.x0 then ‖g‖^2-‖g-r‖^2 else 0)=
    energy (graphMolecule Q.ends) univ ((F.chart g r).symm x).1 (F.indexing.atom i).1+
      (if i=F.indexing.shape.x0 then ‖g‖^2-‖g-r‖^2 else 0)
  rw [Q.energy_eq,graph_energy]
  congr 1
  apply congrArg (directedEnergy Q.ends (F.indexing.atom i).1)
  funext e
  rw [Q.pullChart_decode]
  change ((F.chart g r).symm x).1 (graphBondEquiv Q.ends (Q.edge.symm (Q.edge e)))=_
  rw [Equiv.symm_apply_apply]

/-- Origins commute with the fixed source bond realization. -/
theorem origin_pull {E : Type} [AddCommGroup E] (a b : A) (hab : a ≠ b)
    (g r : E) (k : FlowFiber M S (Q.atom a).1 (Q.atom b).1 E r)
    (p : Bond (graphMolecule Q.ends) univ ⊕ Fin 2) :
    origin M S k.1 g r (Sum.map Q.contractEdge id p)=
      origin (graphMolecule Q.ends) univ (Q.contractFiber a b hab r k).1 g r p := by
  cases p <;> rfl

/-- The source graph chart gives the exact full molecule chart, including
all actual-bond origins and every signed phase identity. -/
@[expose] noncomputable def pullFullChart {X : VineType} {a b : A}
    (F : FullVineChart (graphMolecule Q.ends) X univ a b) (hab : a ≠ b) :
    FullVineChart M X S (Q.atom a).1 (Q.atom b).1 where
  indexing := Q.pullIndexing F.indexing
  bond_count := by
    have h := Fintype.card_congr Q.contractEdge
    simp only [Fintype.card_coe] at h
    exact h.symm.trans F.bond_count
  junction := F.junction
  junction_type := F.junction_type
  rung_bonds := by
    intro j
    rw [Q.pullIndexing_atom,Q.pullIndexing_atom,Q.bondsBetween_eq_graph]
    exact F.rung_bonds j
  decodeFree := fun e i => F.decodeFree (Q.contractEdge.symm e) i
  decodeGap := fun e => F.decodeGap (Q.contractEdge.symm e)
  free_unit := fun e i => F.free_unit (Q.contractEdge.symm e) i
  chart := Q.pullChart F hab
  decode_eq := by
    intro E _ g r x e
    rw [Q.pullChart_decode]
    exact F.decode_eq g r x (Q.contractEdge.symm e)
  difference := by
    intro i
    obtain ⟨p,q,h⟩ := F.difference i
    refine ⟨Sum.map Q.contractEdge id p,Sum.map Q.contractEdge id q,?_⟩
    intro E _ g r k
    rw [Q.origin_pull a b hab g r k p,Q.origin_pull a b hab g r k q]
    exact h g r (Q.contractFiber a b hab r k)
  ζc := F.ζc
  ζ_unit := F.ζ_unit
  ζ_bad_nonzero := F.ζ_bad_nonzero
  coreLinear := F.coreLinear
  coreFirstSign := F.coreFirstSign
  coreSign := F.coreSign
  ξc := F.ξc
  ξ_unit := F.ξ_unit
  joint_phase := by
    intro d g r x
    rw [Q.nodeResonance_pullChart]
    exact F.joint_phase d g r x
  rung_t_phase := by
    intro d g r x j
    rw [Q.nodeResonance_pullChart]
    exact F.rung_t_phase d g r x j
  rung_s_phase := by
    intro d g r x j
    rw [Q.nodeResonance_pullChart]
    exact F.rung_s_phase d g r x j
  core_first_phase := by
    intro hn d g r x
    rw [Q.nodeResonance_pullChart]
    exact F.core_first_phase hn d g r x
  core_second_phase := by
    intro hn d g r x
    rw [Q.nodeResonance_pullChart]
    exact F.core_second_phase hn d g r x
  core_sum_phase := by
    intro hn d g r x
    simp_rw [Q.nodeResonance_pullChart]
    exact F.core_sum_phase hn d g r x

end WaveTurbulence.Vine.Param.DirectedBondModel
