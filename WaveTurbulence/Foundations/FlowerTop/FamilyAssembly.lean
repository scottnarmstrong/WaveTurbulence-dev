/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.PlainOfFamily
public import WaveTurbulence.Foundations.FlowerTop.OwnerAdapters
public import WaveTurbulence.Foundations.FlowerTop.FC23Inputs

/-! The plain and cut1 clauses both come from the single FC23 uniform family input. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open Set LGSpine

/-- The plain clause from FC23's uniform family input (one production, shared with cut1). -/
theorem plain_of_family (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    (hFam : WTPrefixP (FC23UniformCut1Input C U)) : WTPrefixP (FlowerCaseAt CasePlain) := by
  have h := FC23.prefixP_small_moment hFam (fun _ _ _ => 1) (fun _ _ _ _ => one_pos)
  refine prefixP_map h ?_
  rintro Pm P ⟨H, _, hd, hν, hδ, hδ1, hL⟩
  exact flowerCasePlain_of_uniform C U hC hU (by omega) hν hδ hδ1 hL H

/-- **The frozen `layergardenFlower_v3` body** with the plain and cut1 clauses both produced from the single
FC23 family input `hFam`. Remaining binders: `hFam` (FC23), `hCut2`, `hCut2Zero` (C2-E-B), `hCouple`. -/
theorem layergardenFlower_v3_of_family (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p)
    (hFam : WTPrefixP (FC23UniformCut1Input C U))
    (hCut2 : WTPrefixP (FlowerCaseAt CaseCut2Pos))
    (hCut2Zero : WTPrefixP (FlowerCaseAt CaseCut2Zero))
    (hCouple : WTPrefixP CoupleHalfAt) : V2Chain.LayergardenFlowerV3Gate :=
  layergardenFlower_v3_of_inputs (plain_of_family C U hC hU hFam)
    (prefixP_map (fc23Cut1Prefix C U hC hU hFam) fun _ _ h => cut1_of_FC23 h) hCut2 hCut2Zero hCouple

end WaveTurbulence.FlowerTop
