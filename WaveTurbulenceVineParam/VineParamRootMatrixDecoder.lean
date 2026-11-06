/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRootMatrixAnchor
import Mathlib.Tactic

/-! # The normalized source chart has the exact affine unit decoder -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Appending a fixed gap retains every actual free coordinate. -/
theorem attachGap_castSucc {E : Type*} [AddCommGroup E] {q : ℕ}
    (x : Fin q → E) (r : E) (i : Fin q) : attachGap x r i.castSucc=x i := by
  simp only [attachGap,Fin.val_castSucc,dite_eq_left i.2]

/-- The final appended coordinate is exactly the physical gap. -/
theorem attachGap_last {E : Type*} [AddCommGroup E] {q : ℕ}
    (x : Fin q → E) (r : E) : attachGap x r (Fin.last q)=r := by
  simp only [attachGap,Fin.val_last,lt_self_iff_false,dite_false]

namespace RootIntegerMatrix
variable {q : ℕ} (C : RootIntegerMatrix q)

/-- The free integer reconstruction columns. -/
@[expose] def decodeFree : Matrix (Fin (2*q)) (Fin q) ℤ := fun e i => C.inverse e (C.freeIndex i)

/-- The unrestricted integral coefficient of the prescribed root gap. -/
@[expose] def decodeGap : Fin (2*q) → ℤ := fun e => C.inverse e C.gapIndex

/-- The checked inverse has the full source free-coefficient bound. -/
theorem decodeFree_unit : ∀ e i,C.decodeFree e i ∈ ({-1,0,1} : Finset ℤ) := by
  intro e i
  exact C.free_bounds e i

/-- The physical reference coefficient is -1 on every actual bond label. -/
theorem decodeFree_reference : ∀ e,C.decodeFree e ⟨0,C.positive⟩= -1 := by
  intro e
  exact C.reference_column e

/-- Exact coefficient1 on g, ternary free coefficients, and an integer gap
column, over every additive momentum group. -/
theorem affineChart_decode_eq {E : Type*} [AddCommGroup E]
    (g r : E) (x : Fin q → E) (e : Fin (2*q)) :
    ((C.affineChart g r).symm x).1 e=g+(∑ i,C.decodeFree e i • x i)+C.decodeGap e • r := by
  rw [C.affineChart_decode,intEval_pack C.gap_lt C.inverse x r]
  have hf : ∀ i : Fin q,coordinateEmbedding C.gap_lt i.castSucc=C.freeIndex i := fun i => Fin.ext rfl
  have hg : coordinateEmbedding C.gap_lt (Fin.last q)=C.gapIndex := Fin.ext rfl
  simp only [intEval,reducedDecoder,Fin.sum_univ_castSucc,hf,hg,attachGap_castSucc,attachGap_last,
    decodeFree,decodeGap,add_assoc]

end RootIntegerMatrix
end WaveTurbulence.Vine.Param
