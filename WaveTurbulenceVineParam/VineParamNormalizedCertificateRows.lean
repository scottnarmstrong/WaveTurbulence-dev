/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedVineCertificate
import Mathlib.Tactic

/-! # Exact evaluation of normalized integer phase rows -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract
variable {X : VineType} {E : Type*} [NormedAddCommGroup E]

/-- A free phase row reads its actual normalized free coordinate. -/
theorem freePhaseRow_eval (A : Shape X) (x : Fin A.n → E) (r : E) (i : Fin A.n) :
    (∑ l,freePhaseRow A i l • attachGap x r l)=x i := by
  rw [show freePhaseRow A i=coordinateRow i.castSucc from rfl,coordinateRow_eval,attachGap_castSucc]

/-- The last reduced phase coordinate is exactly the physical gap. -/
theorem gapPhaseRow_eval (A : Shape X) (x : Fin A.n → E) (r : E) :
    (∑ l,gapPhaseRow A l • attachGap x r l)=r := by
  rw [show gapPhaseRow A=coordinateRow (Fin.last A.n) from rfl,coordinateRow_eval,attachGap_last]

/-- Every paired linear correction evaluates with the exact integer coefficients. -/
theorem pairCorrectionRow_eval (A : Shape X) (ζ : Fin A.m → Fin 3 → ℤ) (j : Fin A.m)
    (x : Fin A.n → E) (r : E) :
    (∑ l,pairCorrectionRow A ζ j l • attachGap x r l)=
      ζ j 0 • x (A.xSlot j)+ζ j 1 • x (A.ySlot j)+ζ j 2 • r := by
  simp only [pairCorrectionRow,add_smul,mul_smul,sum_add_distrib,← Finset.smul_sum,
    freePhaseRow_eval,gapPhaseRow_eval]

/-- The entire core correction evaluates in its three actual core coordinates. -/
theorem coreCorrectionRow_eval (A : Shape X) (hn : X.IsBad=false) (ξ : Fin 4 → ℤ)
    (x : Fin A.n → E) (r : E) :
    (∑ l,coreCorrectionRow A hn ξ l • attachGap x r l)=
      ξ 0 • x (A.uSlot hn 0)+ξ 1 • x (A.uSlot hn 1)+ξ 2 • x (A.uSlot hn 2)+ξ 3 • r := by
  simp only [coreCorrectionRow,add_smul,mul_smul,sum_add_distrib,← Finset.smul_sum,
    freePhaseRow_eval,gapPhaseRow_eval]

/-- Both source core alternatives have their literal normalized arguments. -/
theorem coreSecondArgumentRow_eval (A : Shape X) (hn : X.IsBad=false) (linear : Bool)
    (x : Fin A.n → E) (r : E) :
    (∑ l,coreSecondArgumentRow A hn linear l • attachGap x r l)=
      if linear then x (A.uSlot hn 0) else
        x (A.uSlot hn 0)+x (A.uSlot hn 1)-x (A.uSlot hn 2) := by
  cases linear <;> simp [coreSecondArgumentRow,sub_smul,add_smul,sum_sub_distrib,sum_add_distrib,freePhaseRow_eval]

end WaveTurbulence.Vine.Param
