/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRootIntegerMatrix
public import WaveTurbulenceVineParam.VineParamProfileDegrees
import Mathlib.Tactic

/-! # Normalized full source matrix for vine II, profile 1, included joint 1

The integer tables are checked here by the Lean kernel. The reference is
minus the actual outgoing joint label after subtracting the uniform anchor.
-/

public section
namespace WaveTurbulence.Vine.Param.Normalized.J1II001

/-- The actual directed finite endpoint graph. -/
@[expose] def ends : Fin 6 → Fin 4×Fin 4 :=
  fun i => if i.1 < 3 then (if i.1 < 1 then (((2 : Fin 4),(0 : Fin 4))) else (if i.1 < 2 then (((0 : Fin 4),(3 : Fin 4))) else (((2 : Fin 4),(3 : Fin 4))))) else (if i.1 < 4 then (((3 : Fin 4),(2 : Fin 4))) else (if i.1 < 5 then (((1 : Fin 4),(2 : Fin 4))) else (((3 : Fin 4),(1 : Fin 4)))))

/-- Full coordinate, included-joint gap and actual interior flow rows. -/
@[expose] def forward : Matrix (Fin 6) (Fin 6) ℤ := fun i j => if i.1 < 3 then (if i.1 < 1 then (if j.1 < 3 then (if j.1 < 1 then (0) else (if j.1 < 2 then (0) else (0))) else (if j.1 < 4 then (0) else (if j.1 < 5 then (-1) else (0)))) else (if i.1 < 2 then (if j.1 < 3 then (if j.1 < 1 then (0) else (if j.1 < 2 then (0) else (1))) else (if j.1 < 4 then (0) else (if j.1 < 5 then (0) else (-1)))) else (if j.1 < 3 then (if j.1 < 1 then (0) else (if j.1 < 2 then (0) else (-1))) else (if j.1 < 4 then (1) else (if j.1 < 5 then (0) else (0)))))) else (if i.1 < 4 then (if j.1 < 3 then (if j.1 < 1 then (0) else (if j.1 < 2 then (0) else (0))) else (if j.1 < 4 then (0) else (if j.1 < 5 then (1) else (-1)))) else (if i.1 < 5 then (if j.1 < 3 then (if j.1 < 1 then (1) else (if j.1 < 2 then (0) else (1))) else (if j.1 < 4 then (-1) else (if j.1 < 5 then (-1) else (0)))) else (if j.1 < 3 then (if j.1 < 1 then (0) else (if j.1 < 2 then (-1) else (-1))) else (if j.1 < 4 then (1) else (if j.1 < 5 then (0) else (1))))))

/-- The explicit integer source reconstruction. -/
@[expose] def inverse : Matrix (Fin 6) (Fin 6) ℤ := fun i j => if i.1 < 3 then (if i.1 < 1 then (if j.1 < 3 then (if j.1 < 1 then (-1) else (if j.1 < 2 then (0) else (1))) else (if j.1 < 4 then (0) else (if j.1 < 5 then (1) else (0)))) else (if i.1 < 2 then (if j.1 < 3 then (if j.1 < 1 then (-1) else (if j.1 < 2 then (0) else (1))) else (if j.1 < 4 then (-1) else (if j.1 < 5 then (0) else (-1)))) else (if j.1 < 3 then (if j.1 < 1 then (-1) else (if j.1 < 2 then (1) else (0))) else (if j.1 < 4 then (-1) else (if j.1 < 5 then (0) else (0)))))) else (if i.1 < 4 then (if j.1 < 3 then (if j.1 < 1 then (-1) else (if j.1 < 2 then (1) else (1))) else (if j.1 < 4 then (-1) else (if j.1 < 5 then (0) else (0)))) else (if i.1 < 5 then (if j.1 < 3 then (if j.1 < 1 then (-1) else (if j.1 < 2 then (0) else (0))) else (if j.1 < 4 then (0) else (if j.1 < 5 then (0) else (0)))) else (if j.1 < 3 then (if j.1 < 1 then (-1) else (if j.1 < 2 then (0) else (0))) else (if j.1 < 4 then (-1) else (if j.1 < 5 then (0) else (0))))))

private theorem forward_inverse_row_0 : ∀ j : Fin 6,(forward*inverse) (0 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 0 j := by decide
private theorem forward_inverse_row_1 : ∀ j : Fin 6,(forward*inverse) (1 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 1 j := by decide
private theorem forward_inverse_row_2 : ∀ j : Fin 6,(forward*inverse) (2 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 2 j := by decide
private theorem forward_inverse_row_3 : ∀ j : Fin 6,(forward*inverse) (3 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 3 j := by decide
private theorem forward_inverse_row_4 : ∀ j : Fin 6,(forward*inverse) (4 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 4 j := by decide
private theorem forward_inverse_row_5 : ∀ j : Fin 6,(forward*inverse) (5 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 5 j := by decide

/-- Exact full integer inverse certificate. -/
theorem forward_inverse : forward*inverse=1 := by
  funext i j
  fin_cases i
  · exact forward_inverse_row_0 j
  · exact forward_inverse_row_1 j
  · exact forward_inverse_row_2 j
  · exact forward_inverse_row_3 j
  · exact forward_inverse_row_4 j
  · exact forward_inverse_row_5 j

private theorem inverse_forward_row_0 : ∀ j : Fin 6,(inverse*forward) (0 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 0 j := by decide
private theorem inverse_forward_row_1 : ∀ j : Fin 6,(inverse*forward) (1 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 1 j := by decide
private theorem inverse_forward_row_2 : ∀ j : Fin 6,(inverse*forward) (2 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 2 j := by decide
private theorem inverse_forward_row_3 : ∀ j : Fin 6,(inverse*forward) (3 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 3 j := by decide
private theorem inverse_forward_row_4 : ∀ j : Fin 6,(inverse*forward) (4 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 4 j := by decide
private theorem inverse_forward_row_5 : ∀ j : Fin 6,(inverse*forward) (5 : Fin 6) j=(1 : Matrix (Fin 6) (Fin 6) ℤ) 5 j := by decide

/-- Exact full integer inverse certificate. -/
theorem inverse_forward : inverse*forward=1 := by
  funext i j
  fin_cases i
  · exact inverse_forward_row_0 j
  · exact inverse_forward_row_1 j
  · exact inverse_forward_row_2 j
  · exact inverse_forward_row_3 j
  · exact inverse_forward_row_4 j
  · exact inverse_forward_row_5 j

/-- Every interior source atom occurs exactly once. -/
@[expose] noncomputable def interiorEquiv : Fin 2 ≃ {v : Fin 4 // v ≠ (0 : Fin 4) ∧ v ≠ (1 : Fin 4)} :=
  Equiv.ofBijective (fun v => ⟨⟨v.1+2,by have := v.2; omega⟩,by
    constructor <;> intro h <;> have he := congrArg Fin.val h
    all_goals dsimp only at he
    all_goals omega⟩) (by decide)

/-- Full source certificate with an integral, ternary free decoder. -/
@[expose] noncomputable def integerChart : RootIntegerMatrix 3 where
  positive := by decide
  ends := ends
  a := 0
  b := 1
  distinct := by decide
  interior := interiorEquiv
  balanced := by decide
  forward := forward
  inverse := inverse
  forward_inverse := forward_inverse
  inverse_forward := inverse_forward
  gap_row := by decide
  interior_rows := by decide
  reference_column := by decide
  free_bounds := by decide

/-- The endpoint graph is the exact normalized source orientation profile. -/
theorem ends_profile : List.ofFn (fun i => ((ends i).1.1,(ends i).2.1))=
    normalizedBaseEnds .II ⟨1,by decide⟩ := by decide

/-- The reference row selects the actual outgoing included-joint occurrence. -/
theorem reference_row : ∀ e : Fin 6,forward 0 e= -(if e=4 then 1 else 0) := by decide

end WaveTurbulence.Vine.Param.Normalized.J1II001
