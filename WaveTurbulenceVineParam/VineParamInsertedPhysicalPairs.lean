/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedPhysicalOrigins
public import WaveTurbulenceVineParam.VineParamNonreferenceInsertion
import Mathlib.Tactic

/-! # Explicit geometric origin pairs, uniform in all momentum labels -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Choose only a common geometric cap side of an old fixed difference.
This choice does not range over algebraically equivalent origin pairs. -/
@[expose] noncomputable def retainedDifferenceSide {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b) (hcap : P.CapSupported G.cap)
    (j : {j : Fin P.full.indexing.shape.n // j ≠ P.full.indexing.shape.x0}) : Bool :=
  Classical.choose (G.exists_common_admissible
    (P.differencePair j).1 (P.differencePair j).2 (hcap j))

/-- The selected side is admissible for both individually marked old bonds. -/
theorem retainedDifferenceSide_admissible {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b) (hcap : P.CapSupported G.cap)
    (j : {j : Fin P.full.indexing.shape.n // j ≠ P.full.indexing.shape.x0}) :
    G.AdmissibleSide (P.differencePair j).1 (G.retainedDifferenceSide P hcap j) ∧
      G.AdmissibleSide (P.differencePair j).2 (G.retainedDifferenceSide P hcap j) :=
  Classical.choose_spec (G.exists_common_admissible
    (P.differencePair j).1 (P.differencePair j).2 (hcap j))

/-- The exact retained representatives or the exact two local cell origins.
There is no label-dependent choice and no unused reference branch. -/
@[expose] noncomputable def insertedPhysicalPair {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b) (hcap : P.CapSupported G.cap) (hX : X ≠ .I)
    (i : {i : Fin (insertedShape P.full.indexing.shape hX).n //
      i ≠ (insertedShape P.full.indexing.shape hX).x0}) : SpliceEdge G.i G.j × SpliceEdge G.i G.j :=
  Sum.elim
    (fun j => (G.representative (P.differencePair j).1 (G.retainedDifferenceSide P hcap j),
      G.representative (P.differencePair j).2 (G.retainedDifferenceSide P hcap j)))
    (fun j => (.inr (insertedDifferenceOrigins G.pattern j).1,
      .inr (insertedDifferenceOrigins G.pattern j).2))
    (nonreferenceInsertionEquiv P.full.indexing.shape hX i)

/-- Every explicit geometric pair gives exactly its new coordinate on the
entire actual source fiber, for every additive momentum group. -/
theorem insertedPhysicalPair_eq {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b) (hcap : P.CapSupported G.cap)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (i : {i : Fin (insertedShape P.full.indexing.shape hX).n //
      i ≠ (insertedShape P.full.indexing.shape hX).x0})
    {E : Type} [AddCommGroup E] (g r : E)
    (k : FlowFiber (graphMolecule G.newEnds) univ (.inl a) (.inl b) E r) :
    G.insertedContractChart P.full P.distinct hX ha hb (decide (b ∈ G.cap)) g r k i.1=
      k.1 (graphBondEquiv G.newEnds (G.insertedPhysicalPair P hcap hX i).1)-
        k.1 (graphBondEquiv G.newEnds (G.insertedPhysicalPair P hcap hX i).2) := by
  have hv := nonreferenceInsertionEquiv_value P.full.indexing.shape hX i
  cases hi : nonreferenceInsertionEquiv P.full.indexing.shape hX i with
  | inl j =>
    rw [hi] at hv
    simp only [Sum.map_inl] at hv
    simp only [insertedPhysicalPair,hi,Sum.elim_inl]
    let kd := graphContractFiber G.newEnds (.inl a) (.inl b)
      (fun h => P.distinct (Sum.inl.inj h)) r k
    let C := G.anchoredInsertionChart a b P.distinct ha hb r
      (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 (decide (b ∈ G.cap))
    have hs := G.retainedDifferenceSide_admissible P hcap j
    have h := G.anchoredInsertionChart_difference_old a b P.distinct ha hb r
      (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 j.1 j.2
      (decide (b ∈ G.cap)) (P.differencePair j).1 (P.differencePair j).2
      (G.retainedDifferenceSide P hcap j) hs.1 hs.2
      (G.oldDirectedChart_difference P j g r) (C kd)
    rw [Equiv.symm_apply_apply] at h
    rw [G.insertedContractChart_forward,← hv]
    exact h
  | inr j =>
    rw [hi] at hv
    simp only [Sum.map_inr] at hv
    simp only [insertedPhysicalPair,hi,Sum.elim_inr]
    rw [G.insertedContractChart_forward,← hv]
    exact G.anchoredInsertionChart_difference_new a b P.distinct ha hb r
      (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 (decide (b ∈ G.cap))
      (graphContractFiber G.newEnds (.inl a) (.inl b)
        (fun h => P.distinct (Sum.inl.inj h)) r k) j

end WaveTurbulence.Vine.Param.RungSpliceGeometry
