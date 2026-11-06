/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRootIntegerMatrix
public import WaveTurbulenceVineParam.VineParamProfileDegrees
import Mathlib.Tactic

/-! # Normalized full source matrix for vine III, profile 7, included joint 1

The integer tables are checked here by the Lean kernel. The reference is
minus the actual outgoing joint label after subtracting the uniform anchor.
-/

public section
namespace WaveTurbulence.Vine.Param.Normalized.J1III007

/-- The actual directed finite endpoint graph. -/
@[expose] def ends : Fin 16 → Fin 9×Fin 9 :=
  fun i => if i.1 < 8 then (if i.1 < 4 then (if i.1 < 2 then (if i.1 < 1 then (((2 : Fin 9),(0 : Fin 9))) else (((0 : Fin 9),(3 : Fin 9)))) else (if i.1 < 3 then (((2 : Fin 9),(3 : Fin 9))) else (((3 : Fin 9),(2 : Fin 9))))) else (if i.1 < 6 then (if i.1 < 5 then (((5 : Fin 9),(4 : Fin 9))) else (((6 : Fin 9),(4 : Fin 9)))) else (if i.1 < 7 then (((5 : Fin 9),(6 : Fin 9))) else (((6 : Fin 9),(5 : Fin 9)))))) else (if i.1 < 12 then (if i.1 < 10 then (if i.1 < 9 then (((7 : Fin 9),(8 : Fin 9))) else (((7 : Fin 9),(8 : Fin 9)))) else (if i.1 < 11 then (((1 : Fin 9),(7 : Fin 9))) else (((8 : Fin 9),(1 : Fin 9))))) else (if i.1 < 14 then (if i.1 < 13 then (((4 : Fin 9),(2 : Fin 9))) else (((3 : Fin 9),(5 : Fin 9)))) else (if i.1 < 15 then (((4 : Fin 9),(7 : Fin 9))) else (((8 : Fin 9),(6 : Fin 9))))))

/-- Full coordinate, included-joint gap and actual interior flow rows. -/
@[expose] def forward : Matrix (Fin 16) (Fin 16) ℤ := fun i j => if i.1 < 8 then (if i.1 < 4 then (if i.1 < 2 then (if i.1 < 1 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (-1) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (-1)) else (if j.1 < 15 then (0) else (0)))))) else (if i.1 < 3 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (1)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (-1))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (-1) else (1))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0))))))) else (if i.1 < 6 then (if i.1 < 5 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (-1)) else (if j.1 < 11 then (0) else (1))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (1)) else (if j.1 < 15 then (0) else (0)))))) else (if i.1 < 7 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (-1) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (1)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (-1)))))))) else (if i.1 < 12 then (if i.1 < 10 then (if i.1 < 9 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (1) else (-1))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (1) else (0)) else (if j.1 < 3 then (1) else (-1))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (-1) else (0)) else (if j.1 < 15 then (0) else (0)))))) else (if i.1 < 11 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (-1)) else (if j.1 < 3 then (-1) else (1))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (1)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (-1)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (1) else (0)) else (if j.1 < 15 then (1) else (0))))))) else (if i.1 < 14 then (if i.1 < 13 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (1) else (0)) else (if j.1 < 7 then (1) else (-1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (-1)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (1)) else (if j.1 < 7 then (-1) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (-1)))))) else (if i.1 < 15 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (1) else (1)) else (if j.1 < 11 then (-1) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (-1) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (0) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (-1)) else (if j.1 < 11 then (0) else (1))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (1))))))))

/-- The explicit integer source reconstruction. -/
@[expose] def inverse : Matrix (Fin 16) (Fin 16) ℤ := fun i j => if i.1 < 8 then (if i.1 < 4 then (if i.1 < 2 then (if i.1 < 1 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (1))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (1)) else (if j.1 < 7 then (1) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (1)) else (if j.1 < 11 then (0) else (1))) else (if j.1 < 14 then (if j.1 < 13 then (2) else (1)) else (if j.1 < 15 then (1) else (1))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (1))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (1)) else (if j.1 < 7 then (1) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (-1) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (1) else (0)) else (if j.1 < 15 then (0) else (0)))))) else (if i.1 < 3 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (1)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (1)) else (if j.1 < 7 then (1) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (1) else (0)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (1)) else (if j.1 < 3 then (-1) else (1))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (1)) else (if j.1 < 7 then (1) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (1) else (0)) else (if j.1 < 15 then (0) else (0))))))) else (if i.1 < 6 then (if i.1 < 5 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (0)) else (if j.1 < 7 then (1) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (1) else (0)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (1)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (1) else (1)) else (if j.1 < 15 then (0) else (0)))))) else (if i.1 < 7 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (1)) else (if j.1 < 7 then (0) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (1) else (0)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (0)) else (if j.1 < 7 then (0) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0)))))))) else (if i.1 < 12 then (if i.1 < 10 then (if i.1 < 9 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (-1))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0)))))) else (if i.1 < 11 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (0) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (0) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0))))))) else (if i.1 < 14 then (if i.1 < 13 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (1)) else (if j.1 < 7 then (1) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (0) else (0)) else (if j.1 < 11 then (0) else (1))) else (if j.1 < 14 then (if j.1 < 13 then (2) else (1)) else (if j.1 < 15 then (1) else (1))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (1)) else (if j.1 < 7 then (1) else (1)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (1) else (0)) else (if j.1 < 15 then (0) else (0)))))) else (if i.1 < 15 then (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-2) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (-1) else (-1))))) else (if j.1 < 8 then (if j.1 < 4 then (if j.1 < 2 then (if j.1 < 1 then (-1) else (0)) else (if j.1 < 3 then (-1) else (0))) else (if j.1 < 6 then (if j.1 < 5 then (-1) else (0)) else (if j.1 < 7 then (0) else (0)))) else (if j.1 < 12 then (if j.1 < 10 then (if j.1 < 9 then (-1) else (0)) else (if j.1 < 11 then (0) else (0))) else (if j.1 < 14 then (if j.1 < 13 then (0) else (0)) else (if j.1 < 15 then (0) else (0))))))))

private theorem forward_inverse_row_0 : ∀ j : Fin 16,(forward*inverse) (0 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 0 j := by decide
private theorem forward_inverse_row_1 : ∀ j : Fin 16,(forward*inverse) (1 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 1 j := by decide
private theorem forward_inverse_row_2 : ∀ j : Fin 16,(forward*inverse) (2 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 2 j := by decide
private theorem forward_inverse_row_3 : ∀ j : Fin 16,(forward*inverse) (3 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 3 j := by decide
private theorem forward_inverse_row_4 : ∀ j : Fin 16,(forward*inverse) (4 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 4 j := by decide
private theorem forward_inverse_row_5 : ∀ j : Fin 16,(forward*inverse) (5 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 5 j := by decide
private theorem forward_inverse_row_6 : ∀ j : Fin 16,(forward*inverse) (6 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 6 j := by decide
private theorem forward_inverse_row_7 : ∀ j : Fin 16,(forward*inverse) (7 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 7 j := by decide
private theorem forward_inverse_row_8 : ∀ j : Fin 16,(forward*inverse) (8 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 8 j := by decide
private theorem forward_inverse_row_9 : ∀ j : Fin 16,(forward*inverse) (9 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 9 j := by decide
private theorem forward_inverse_row_10 : ∀ j : Fin 16,(forward*inverse) (10 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 10 j := by decide
private theorem forward_inverse_row_11 : ∀ j : Fin 16,(forward*inverse) (11 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 11 j := by decide
private theorem forward_inverse_row_12 : ∀ j : Fin 16,(forward*inverse) (12 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 12 j := by decide
private theorem forward_inverse_row_13 : ∀ j : Fin 16,(forward*inverse) (13 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 13 j := by decide
private theorem forward_inverse_row_14 : ∀ j : Fin 16,(forward*inverse) (14 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 14 j := by decide
private theorem forward_inverse_row_15 : ∀ j : Fin 16,(forward*inverse) (15 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 15 j := by decide

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
  · exact forward_inverse_row_6 j
  · exact forward_inverse_row_7 j
  · exact forward_inverse_row_8 j
  · exact forward_inverse_row_9 j
  · exact forward_inverse_row_10 j
  · exact forward_inverse_row_11 j
  · exact forward_inverse_row_12 j
  · exact forward_inverse_row_13 j
  · exact forward_inverse_row_14 j
  · exact forward_inverse_row_15 j

private theorem inverse_forward_row_0 : ∀ j : Fin 16,(inverse*forward) (0 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 0 j := by decide
private theorem inverse_forward_row_1 : ∀ j : Fin 16,(inverse*forward) (1 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 1 j := by decide
private theorem inverse_forward_row_2 : ∀ j : Fin 16,(inverse*forward) (2 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 2 j := by decide
private theorem inverse_forward_row_3 : ∀ j : Fin 16,(inverse*forward) (3 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 3 j := by decide
private theorem inverse_forward_row_4 : ∀ j : Fin 16,(inverse*forward) (4 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 4 j := by decide
private theorem inverse_forward_row_5 : ∀ j : Fin 16,(inverse*forward) (5 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 5 j := by decide
private theorem inverse_forward_row_6 : ∀ j : Fin 16,(inverse*forward) (6 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 6 j := by decide
private theorem inverse_forward_row_7 : ∀ j : Fin 16,(inverse*forward) (7 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 7 j := by decide
private theorem inverse_forward_row_8 : ∀ j : Fin 16,(inverse*forward) (8 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 8 j := by decide
private theorem inverse_forward_row_9 : ∀ j : Fin 16,(inverse*forward) (9 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 9 j := by decide
private theorem inverse_forward_row_10 : ∀ j : Fin 16,(inverse*forward) (10 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 10 j := by decide
private theorem inverse_forward_row_11 : ∀ j : Fin 16,(inverse*forward) (11 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 11 j := by decide
private theorem inverse_forward_row_12 : ∀ j : Fin 16,(inverse*forward) (12 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 12 j := by decide
private theorem inverse_forward_row_13 : ∀ j : Fin 16,(inverse*forward) (13 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 13 j := by decide
private theorem inverse_forward_row_14 : ∀ j : Fin 16,(inverse*forward) (14 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 14 j := by decide
private theorem inverse_forward_row_15 : ∀ j : Fin 16,(inverse*forward) (15 : Fin 16) j=(1 : Matrix (Fin 16) (Fin 16) ℤ) 15 j := by decide

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
  · exact inverse_forward_row_6 j
  · exact inverse_forward_row_7 j
  · exact inverse_forward_row_8 j
  · exact inverse_forward_row_9 j
  · exact inverse_forward_row_10 j
  · exact inverse_forward_row_11 j
  · exact inverse_forward_row_12 j
  · exact inverse_forward_row_13 j
  · exact inverse_forward_row_14 j
  · exact inverse_forward_row_15 j

/-- Every interior source atom occurs exactly once. -/
@[expose] noncomputable def interiorEquiv : Fin 7 ≃ {v : Fin 9 // v ≠ (0 : Fin 9) ∧ v ≠ (1 : Fin 9)} :=
  Equiv.ofBijective (fun v => ⟨⟨v.1+2,by have := v.2; omega⟩,by
    constructor <;> intro h <;> have he := congrArg Fin.val h
    all_goals dsimp only at he
    all_goals omega⟩) (by decide)

/-- Full source certificate with an integral, ternary free decoder. -/
@[expose] noncomputable def integerChart : RootIntegerMatrix 8 where
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
    normalizedBaseEnds .III ⟨7,by decide⟩ := by decide

/-- The reference row selects the actual outgoing included-joint occurrence. -/
theorem reference_row : ∀ e : Fin 16,forward 0 e= -(if e=10 then 1 else 0) := by decide

end WaveTurbulence.Vine.Param.Normalized.J1III007
