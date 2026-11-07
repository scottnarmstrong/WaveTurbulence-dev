/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCosetTriples
import Mathlib.Tactic

/-! # Exact integer difference coordinates for two signed triples sharing one label -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- The shared variable is outer in profile zero and the middle variable
in profiles one and two. The second triple is reversed in profile two. -/
def appbStarShared (ζ : Fin 3) : Fin 5 := if ζ = 0 then 2 else 1

def appbStarSecond {K : Type*} (ζ : Fin 3) (q : Fin 5 → K) : K × K × K :=
  if ζ = 2 then (q 3,q (appbStarShared ζ),q 4) else (q (appbStarShared ζ),q 3,q 4)

def appbStarDifferences {K : Type*} [AddGroup K] (ζ : Fin 3) (q : Fin 5 → K) : K × K × K :=
  (q 0-q 1,q 2-q 1,if ζ = 2 then q 3-q (appbStarShared ζ) else q (appbStarShared ζ)-q 3)

/-- Two conserved momenta and the three displayed free differences
reconstruct all five actual integer labels. -/
theorem appb_star_differences_injective {d : ℕ} (ζ : Fin 3) (nk1 nk2 : Fin d → ℤ) :
    Set.InjOn (appbStarDifferences ζ) {q : Fin 5 → (Fin d → ℤ) |
      q 0-q 1+q 2 = nk1 ∧ (appbStarSecond ζ q).1-(appbStarSecond ζ q).2.1+
        (appbStarSecond ζ q).2.2 = nk2} := by
  intro q hq q' hq' he
  have hx := congrArg Prod.fst he
  have hy := congrArg (fun p => p.2.1) he
  have hz := congrArg (fun p => p.2.2) he
  funext i j
  have h1 := congrFun hq.1 j
  have h1' := congrFun hq'.1 j
  fin_cases ζ
  all_goals have h2 := congrFun hq.2 j
  all_goals have h2' := congrFun hq'.2 j
  all_goals have hxx := congrFun hx j
  all_goals have hyy := congrFun hy j
  all_goals have hzz := congrFun hz j
  all_goals dsimp [appbStarSecond,appbStarShared,appbStarDifferences] at h2 h2' hxx hyy hzz
  all_goals fin_cases i <;> dsimp at * <;> omega

end WaveTurbulence.Mole
