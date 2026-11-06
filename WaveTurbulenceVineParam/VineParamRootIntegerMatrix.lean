/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamConservationFiber
public import WaveTurbulenceVineParam.VineParamFiniteRootFiber
import Mathlib.Tactic

/-! # Integer certificates for the complete normalized graph source fiber

These are finite integer and incidence certificates. A concrete producer
must prove every field; this structure asserts no full-vine existence result.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- A normalized full source matrix on a balanced graph with two joints.
There are q free coordinates,2q actual bonds and q-1 interior source rows. -/
structure RootIntegerMatrix (q : ℕ) where
  positive : 0<q
  ends : Fin (2*q) → Fin (q+1)×Fin (q+1)
  a : Fin (q+1)
  b : Fin (q+1)
  distinct : a ≠ b
  interior : Fin (q-1) ≃ {v : Fin (q+1) // v ≠ a ∧ v ≠ b}
  balanced : ∀ v,(∑ e,-energySign ends v e)=0
  forward : Matrix (Fin (2*q)) (Fin (2*q)) ℤ
  inverse : Matrix (Fin (2*q)) (Fin (2*q)) ℤ
  forward_inverse : forward*inverse=1
  inverse_forward : inverse*forward=1
  gap_row : ∀ e,forward ⟨q,by omega⟩ e= -energySign ends b e
  interior_rows : ∀ v : Fin (q-1),∀ e,
    forward ⟨q+1+v.1,by have := v.2; omega⟩ e= -energySign ends (interior v).1 e
  reference_column : ∀ e,inverse e ⟨0,by omega⟩= -1
  free_bounds : ∀ e,∀ i : Fin q,inverse e ⟨i.1,by have := i.2; omega⟩ ∈ ({-1,0,1} : Finset ℤ)

namespace RootIntegerMatrix
variable {q : ℕ} (C : RootIntegerMatrix q)

/-- The fixed gap follows all free coordinates. -/
theorem gap_lt (C : RootIntegerMatrix q) : q<2*q := by have := C.positive; omega

/-- Embed the entire free-coordinate block in the full source matrix. -/
@[expose] def freeIndex (C : RootIntegerMatrix q) (i : Fin q) : Fin (2*q) := ⟨i.1,by have := i.2; have := C.positive; omega⟩

/-- The actual matrix gap index. -/
@[expose] def gapIndex (C : RootIntegerMatrix q) : Fin (2*q) := ⟨q,C.gap_lt⟩

/-- The actual matrix row of an interior source equation. -/
@[expose] def interiorIndex (_C : RootIntegerMatrix q) (v : Fin (q-1)) : Fin (2*q) := ⟨q+1+v.1,by have := v.2; omega⟩

/-- Every row after the gap is exactly one actual interior conservation row. -/
theorem later_index (i : Fin (2*q)) (hi : q < i.1) :
    ∃ v : Fin (q-1),i=C.interiorIndex v := by
  have hq := C.positive
  have hib := i.2
  refine ⟨⟨i.1-(q+1),by omega⟩,?_⟩
  apply Fin.ext
  change i.1=q+1+(i.1-(q+1))
  omega

/-- Uniform anchor subtraction preserves every source row. -/
theorem flow_sub_anchor {E : Type*} [AddCommGroup E] (k : Fin (2*q) → E) (g : E) (v : Fin (q+1)) :
    directedFlow C.ends v (fun e => k e-g)=directedFlow C.ends v k := by
  simp only [sub_eq_add_neg,directedFlow_translate,C.balanced,zero_zsmul,add_zero]

/-- The encoder gap row is the actual included-joint flow. -/
theorem eval_gap {E : Type*} [AddCommGroup E] (k : Fin (2*q) → E) :
    intEval C.forward k C.gapIndex=directedFlow C.ends C.b k := by
  simp only [intEval,directedFlow,gapIndex,C.gap_row]

/-- Every encoder tail row is an actual interior source equation. -/
theorem eval_interior {E : Type*} [AddCommGroup E] (k : Fin (2*q) → E) (v : Fin (q-1)) :
    intEval C.forward k (C.interiorIndex v)=directedFlow C.ends (C.interior v).1 k := by
  simp only [intEval,directedFlow,interiorIndex,C.interior_rows]

end RootIntegerMatrix
end WaveTurbulence.Vine.Param
