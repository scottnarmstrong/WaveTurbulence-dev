/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedContractDifferences
public import WaveTurbulenceVineParam.VineParamRepresentativeEndpoints
import Mathlib.Tactic

/-! # The strengthened physical origins survive one insertion -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- The new reference is g minus one fixed actual internal bond label. -/
theorem inserted_reference_eq {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b) (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    {E : Type} [AddCommGroup E] (g r : E)
    (k : FlowFiber (graphMolecule G.newEnds) univ (.inl a) (.inl b) E r) :
    G.insertedContractChart P.full P.distinct hX ha hb (decide (b ∈ G.cap)) g r k
      (insertedShape P.full.indexing.shape hX).x0=
      g-k.1 (graphBondEquiv G.newEnds (G.representative P.reference (decide (b ∈ G.cap)))) := by
  let kd := graphContractFiber G.newEnds (.inl a) (.inl b)
    (fun h => P.distinct (Sum.inl.inj h)) r k
  let C := G.anchoredInsertionChart a b P.distinct ha hb r
    (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 (decide (b ∈ G.cap))
  have h := G.anchoredInsertionChart_difference_reference a b P.distinct ha hb g r
    (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 P.reference
    (G.physical_reference_admissible P) (G.oldDirectedChart_reference P g r) (C kd)
  rw [Equiv.symm_apply_apply] at h
  rw [G.insertedContractChart_forward,slotInsertionEquiv_reference]
  exact h

/-- Every new nonreference coordinate has two fixed internal physical
origins; no boundary origin is needed. -/
theorem inserted_internal_difference {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b) (hcap : P.CapSupported G.cap)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (i : Fin (insertedShape P.full.indexing.shape hX).n)
    (hir : i ≠ (insertedShape P.full.indexing.shape hX).x0) :
    ∃ p q : SpliceEdge G.i G.j,
      ∀ {E : Type} [AddCommGroup E] (g r : E)
        (k : FlowFiber (graphMolecule G.newEnds) univ (.inl a) (.inl b) E r),
        G.insertedContractChart P.full P.distinct hX ha hb (decide (b ∈ G.cap)) g r k i=
          k.1 (graphBondEquiv G.newEnds p)-k.1 (graphBondEquiv G.newEnds q) := by
  cases hi : slotInsertionEquiv P.full.indexing.shape hX i with
  | inl j =>
    have hj : j ≠ P.full.indexing.shape.x0 := by
      intro h
      apply hir
      apply (slotInsertionEquiv P.full.indexing.shape hX).injective
      rw [hi,h,slotInsertionEquiv_reference]
    obtain ⟨side,he,hf⟩ := G.exists_common_admissible
      (P.differencePair ⟨j,hj⟩).1 (P.differencePair ⟨j,hj⟩).2 (hcap ⟨j,hj⟩)
    refine ⟨G.representative (P.differencePair ⟨j,hj⟩).1 side,
      G.representative (P.differencePair ⟨j,hj⟩).2 side,?_⟩
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
    refine ⟨.inr (insertedDifferenceOrigins G.pattern j).1,
      .inr (insertedDifferenceOrigins G.pattern j).2,?_⟩
    intro E _ g r k
    rw [G.insertedContractChart_forward,hi]
    exact G.anchoredInsertionChart_difference_new a b P.distinct ha hb r
      (G.oldDirectedChart P.full P.distinct g r) P.full.indexing.shape.x0 (decide (b ∈ G.cap))
      (graphContractFiber G.newEnds (.inl a) (.inl b)
        (fun h => P.distinct (Sum.inl.inj h)) r k) j

end WaveTurbulence.Vine.Param.RungSpliceGeometry
