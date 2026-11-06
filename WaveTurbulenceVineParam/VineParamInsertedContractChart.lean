/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphContractFiber
public import WaveTurbulenceVineParam.VineParamReflectedIndexing
public import WaveTurbulenceVineParam.VineParamFullInsertedDecoder
import Mathlib.Tactic

/-! # Whole contract source fiber and explicit inverse after a rung insertion

This is a composition helper for the source induction, not a proof of
VINEPARAM. It consumes a previously constructed full graph chart.
-/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- View a previously constructed graph chart on directed source labels. -/
@[expose] noncomputable def oldDirectedChart {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    {E : Type} [AddCommGroup E] (g r : E) :
    DirectedRootFiber G.ends a b r ≃ (Fin F.indexing.shape.n → E) :=
  (graphContractFiber G.ends a b hab r).symm.trans (F.chart g r)

/-- The actual new whole source fiber, in the exact consecutive contract
coordinate blocks. The anchor side is a finite geometric choice. -/
@[expose] noncomputable def insertedContractChart {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    {E : Type} [AddCommGroup E] (g r : E) :
    FlowFiber (graphMolecule G.newEnds) univ (.inl a) (.inl b) E r ≃
      (Fin (insertedShape F.indexing.shape hX).n → E) :=
  (graphContractFiber G.newEnds (.inl a) (.inl b) (fun h => hab (Sum.inl.inj h)) r).trans
    ((G.anchoredInsertionChart a b hab ha hb r (G.oldDirectedChart F hab g r)
      F.indexing.shape.x0 anchor).trans
        (Equiv.arrowCongr (slotInsertionEquiv F.indexing.shape hX).symm (Equiv.refl E)))

/-- Exact inverse of the old directed chart, on each individually marked bond. -/
theorem oldDirectedChart_decode {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    {E : Type} [AddCommGroup E] (g r : E) (x : Fin F.indexing.shape.n → E) (e : β) :
    ((G.oldDirectedChart F hab g r).symm x).1 e=
      g+(∑ i,F.decodeFree (graphBondEquiv G.ends e) i • x i)+
        F.decodeGap (graphBondEquiv G.ends e) • r :=
  F.decode_eq g r x (graphBondEquiv G.ends e)

/-- Actual labels in the inserted inverse are the full directed inverse
at precisely the reindexed contract coordinate vector. -/
theorem insertedContractChart_decode {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    {E : Type} [AddCommGroup E] (g r : E)
    (x : Fin (insertedShape F.indexing.shape hX).n → E)
    (e : SpliceEdge G.i G.j) :
    ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 (graphBondEquiv G.newEnds e)=
      ((G.anchoredInsertionChart a b hab ha hb r (G.oldDirectedChart F hab g r)
        F.indexing.shape.x0 anchor).symm
          (fun i => x ((slotInsertionEquiv F.indexing.shape hX).symm i))).1 e := by
  change ((G.anchoredInsertionChart a b hab ha hb r (G.oldDirectedChart F hab g r)
    F.indexing.shape.x0 anchor).symm
      (fun i => x ((slotInsertionEquiv F.indexing.shape hX).symm i))).1
        ((graphBondEquiv G.newEnds).symm (graphBondEquiv G.newEnds e))=_
  rw [Equiv.symm_apply_apply]

/-- The new actual-bond free matrix is a fixed integer matrix. -/
@[expose] noncomputable def contractInsertedFree {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hX : X ≠ .I) (anchor : Bool) :
    Matrix (Bond (graphMolecule G.newEnds) univ) (Fin (insertedShape F.indexing.shape hX).n) ℤ :=
  fun e i => G.insertedDecoderFree anchor
    (fun e i => F.decodeFree (graphBondEquiv G.ends e) i)
    ((graphBondEquiv G.newEnds).symm e) (slotInsertionEquiv F.indexing.shape hX i)

/-- The new actual-bond gap column remains integral. -/
@[expose] noncomputable def contractInsertedGap {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (anchor : Bool) :
    Bond (graphMolecule G.newEnds) univ → ℤ :=
  fun e => G.insertedDecoderGap anchor
    (fun e => F.decodeGap (graphBondEquiv G.ends e)) (G.gapSign a b)
    ((graphBondEquiv G.newEnds).symm e)

/-- Every entry of the reindexed actual free matrix is a unit coefficient. -/
theorem contractInsertedFree_unit {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hX : X ≠ .I) (anchor : Bool) :
    ∀ e i,UnitCoeff (G.contractInsertedFree F hX anchor e i) := by
  intro e i
  have hA : ∀ e i,F.decodeFree (graphBondEquiv G.ends e) i ∈ ({-1,0,1} : Finset ℤ) := by
    intro e i
    rcases F.free_unit (graphBondEquiv G.ends e) i with h | h | h <;> simp [h]
  have h := G.insertedDecoderFree_unit anchor _ hA
    ((graphBondEquiv G.newEnds).symm e) (slotInsertionEquiv F.indexing.shape hX i)
  rcases mem_insert.mp h with h | h
  · exact Or.inr (Or.inr h)
  · rcases mem_insert.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (mem_singleton.mp h))

/-- The uniform physical reference coefficient is preserved exactly. -/
theorem contractInsertedFree_reference {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hX : X ≠ .I) (anchor : Bool)
    (href : ∀ e,F.decodeFree e F.indexing.shape.x0= -1) :
    ∀ e,G.contractInsertedFree F hX anchor e (insertedShape F.indexing.shape hX).x0= -1 := by
  intro e
  unfold contractInsertedFree
  rw [slotInsertionEquiv_reference]
  exact G.insertedDecoderFree_reference anchor _ F.indexing.shape.x0
    (fun e => href (graphBondEquiv G.ends e)) _

/-- The complete inserted contract inverse has coefficient1 on g,
unit free coefficients, and the fixed integral gap column, for all groups. -/
theorem contractInserted_decode_eq {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (href : ∀ e,F.decodeFree e F.indexing.shape.x0= -1)
    {E : Type} [AddCommGroup E] (g r : E)
    (x : Fin (insertedShape F.indexing.shape hX).n → E)
    (e : Bond (graphMolecule G.newEnds) univ) :
    ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 e=
      g+(∑ i,G.contractInsertedFree F hX anchor e i • x i)+G.contractInsertedGap F anchor e • r := by
  obtain ⟨e,rfl⟩ := (graphBondEquiv G.newEnds).surjective e
  rw [G.insertedContractChart_decode]
  rw [G.full_inserted_decoder_of_old a b hab ha hb g r (G.oldDirectedChart F hab g r)
    F.indexing.shape.x0 anchor
    (fun e i => F.decodeFree (graphBondEquiv G.ends e) i)
    (fun e => F.decodeGap (graphBondEquiv G.ends e))
    (fun e => href (graphBondEquiv G.ends e)) (G.oldDirectedChart_decode F hab g r)]
  simp only [contractInsertedGap,contractInsertedFree,Equiv.symm_apply_apply]
  congr 2
  have h := (slotInsertionEquiv F.indexing.shape hX).sum_comp
    (fun i => G.insertedDecoderFree anchor
      (fun e i => F.decodeFree (graphBondEquiv G.ends e) i) e i •
        x ((slotInsertionEquiv F.indexing.shape hX).symm i))
  simpa only [Equiv.symm_apply_apply] using h.symm

end WaveTurbulence.Vine.Param.RungSpliceGeometry
