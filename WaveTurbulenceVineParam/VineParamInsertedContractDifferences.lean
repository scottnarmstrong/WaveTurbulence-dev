/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamPhysicalChartSupport
public import WaveTurbulenceVineParam.VineParamInsertedDifferences
import Mathlib.Tactic

/-! # Fixed actual origins of every inserted contract coordinate -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- The full contract forward map is exactly the reindexed anchored source map. -/
theorem insertedContractChart_forward {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    {E : Type} [AddCommGroup E] (g r : E)
    (k : FlowFiber (graphMolecule G.newEnds) univ (.inl a) (.inl b) E r)
    (i : Fin (insertedShape F.indexing.shape hX).n) :
    G.insertedContractChart F hab hX ha hb anchor g r k i=
      G.anchoredInsertionChart a b hab ha hb r (G.oldDirectedChart F hab g r)
        F.indexing.shape.x0 anchor
        (graphContractFiber G.newEnds (.inl a) (.inl b) (fun h => hab (Sum.inl.inj h)) r k)
        (slotInsertionEquiv F.indexing.shape hX i) := rfl

/-- All new contract coordinates have fixed actual origins, provided the
constructed old physical differences have the geometric common-side support. -/
theorem insertedContractChart_difference {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b) (hcap : P.CapSupported G.cap)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (i : Fin (insertedShape P.full.indexing.shape hX).n) :
    ∃ p q : Bond (graphMolecule G.newEnds) univ ⊕ Fin 2,
      ∀ {E : Type} [AddCommGroup E] (g r : E)
        (k : FlowFiber (graphMolecule G.newEnds) univ (.inl a) (.inl b) E r),
        G.insertedContractChart P.full P.distinct hX ha hb (decide (b ∈ G.cap)) g r k i=
          origin (graphMolecule G.newEnds) univ k.1 g r p-
            origin (graphMolecule G.newEnds) univ k.1 g r q := by
  cases hi : slotInsertionEquiv P.full.indexing.shape hX i with
  | inl j =>
    by_cases hj : j=P.full.indexing.shape.x0
    · subst j
      refine ⟨.inr 0,.inl (graphBondEquiv G.newEnds
        (G.representative P.reference (decide (b ∈ G.cap)))),?_⟩
      intro E _ g r k
      let kd := graphContractFiber G.newEnds (.inl a) (.inl b)
        (fun h => P.distinct (Sum.inl.inj h)) r k
      let C := G.anchoredInsertionChart a b P.distinct ha hb r
        (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 (decide (b ∈ G.cap))
      have h := G.anchoredInsertionChart_difference_reference a b P.distinct ha hb g r
        (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 P.reference
        (G.physical_reference_admissible P) (G.oldDirectedChart_reference P g r) (C kd)
      rw [Equiv.symm_apply_apply] at h
      rw [G.insertedContractChart_forward,hi]
      exact h
    · obtain ⟨side,he,hf⟩ := G.exists_common_admissible
        (P.differencePair ⟨j,hj⟩).1 (P.differencePair ⟨j,hj⟩).2 (hcap ⟨j,hj⟩)
      refine ⟨.inl (graphBondEquiv G.newEnds (G.representative (P.differencePair ⟨j,hj⟩).1 side)),
        .inl (graphBondEquiv G.newEnds (G.representative (P.differencePair ⟨j,hj⟩).2 side)),?_⟩
      intro E _ g r k
      let kd := graphContractFiber G.newEnds (.inl a) (.inl b)
        (fun h => P.distinct (Sum.inl.inj h)) r k
      let C := G.anchoredInsertionChart a b P.distinct ha hb r
        (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 (decide (b ∈ G.cap))
      have h := G.anchoredInsertionChart_difference_old a b P.distinct ha hb r
        (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 j hj
        (decide (b ∈ G.cap)) (P.differencePair ⟨j,hj⟩).1 (P.differencePair ⟨j,hj⟩).2 side he hf
        (G.oldDirectedChart_difference P ⟨j,hj⟩ g r) (C kd)
      rw [Equiv.symm_apply_apply] at h
      rw [G.insertedContractChart_forward,hi]
      exact h
  | inr j =>
    refine ⟨.inl (graphBondEquiv G.newEnds (.inr (insertedDifferenceOrigins G.pattern j).1)),
      .inl (graphBondEquiv G.newEnds (.inr (insertedDifferenceOrigins G.pattern j).2)),?_⟩
    intro E _ g r k
    rw [G.insertedContractChart_forward,hi]
    exact G.anchoredInsertionChart_difference_new a b P.distinct ha hb r
      (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 (decide (b ∈ G.cap))
      (graphContractFiber G.newEnds (.inl a) (.inl b)
        (fun h => P.distinct (Sum.inl.inj h)) r k) j

end WaveTurbulence.Vine.Param.RungSpliceGeometry
