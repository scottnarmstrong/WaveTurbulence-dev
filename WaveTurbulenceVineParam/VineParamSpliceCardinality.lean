/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamContractCoordinates
public import WaveTurbulenceVineParam.VineParamTwoEdgeDecomposition
import Mathlib.Tactic

/-! # Exact bond and coordinate counts under one actual rung insertion -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Two old occurrences are replaced by six individually marked occurrences. -/
theorem spliceEdge_card {β : Type*} [Fintype β] [DecidableEq β] (i j : β) (hij : i ≠ j) :
    Fintype.card (SpliceEdge i j)=Fintype.card β+4 := by
  have h := sum_two_edge_rest i j hij (fun _ => (1 : ℕ))
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id] at h
  change Fintype.card ({e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6)=_
  rw [Fintype.card_sum,Fintype.card_fin]
  omega

/-- Appending one paired rung adds exactly two included atoms/coordinates. -/
theorem insertedShape_n {X : VineType} (A : VineParamContract.Shape X) (hX : X ≠ .I) :
    (insertedShape A hX).n=A.n+2 := by
  change 2*(A.m+1)+1+(if X.IsBad then 0 else 3)=
    (2*A.m+1+(if X.IsBad then 0 else 3))+2
  omega

/-- The exact 2n bond count is retained by a full paired insertion. -/
theorem spliceEdge_card_of_chart {β : Type*} [Fintype β] [DecidableEq β]
    {X : VineType} (A : VineParamContract.Shape X) (hX : X ≠ .I)
    (i j : β) (hij : i ≠ j) (hβ : Fintype.card β=2*A.n) :
    Fintype.card (SpliceEdge i j)=2*(insertedShape A hX).n := by
  rw [spliceEdge_card i j hij,hβ,insertedShape_n]
  omega

end WaveTurbulence.Vine.Param
