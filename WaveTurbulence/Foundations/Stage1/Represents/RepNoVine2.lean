/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.Stage1.Represents.RepGap
import Mathlib.Tactic

/-!
# S2 REPRESENTS, vine-free case: transport of decorations along `G_sb = S`
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice

variable {w : ℕ} {S : Garden w}

/-- Transport of nodes along `(stSt S σ).G = S` (no unit spliced). -/
@[expose] def nodeCast {Mk : Set (Stage1.CLVine S)} (σ : Prescription S) (h : unitBlocks S σ Mk = [])
    (n : GNode (stSt S σ Mk).G.tree) : GNode S.tree :=
  (congrArg (fun G : Garden w => GNode G.tree) (stSt_G_eq_of_unitBlocks_emptyMk σ h)) ▸ n

/-- B1b (Mk-general form of `bondIndex_nodeCast`). -/
theorem bondIndex_nodeCastMk (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = []) {d : ℕ}
    (zS : GNode S.tree → (Fin d → ℤ)) (y : GardenDart (stSt (Mk := Mk) S σ).G) :
    bondIndex (stSt (Mk := Mk) S σ).G (fun n => zS (nodeCast σ h n)) y = bondIndex S zS ((stSt (Mk := Mk) S σ).M.od y) := by
  have key : ∀ st : SpState S, ∀ hst : st = SpState.init S, ∀ (y : GardenDart st.G),
      bondIndex st.G (fun n => zS ((congrArg (fun G : Garden w => GNode G.tree)
        (show st.G = S by rw [hst]; rfl)) ▸ n)) y = bondIndex S zS (st.M.od y) := by
    rintro st rfl y
    rfl
  exact key _ (stSt_eq_init_of_unitBlocks_emptyMk (Mk := Mk) σ h) y

theorem bondIndex_nodeCast (σ : Prescription S) (h : unitBlocks S σ = []) {d : ℕ}
    (zS : GNode S.tree → (Fin d → ℤ)) (y : GardenDart (stSt S σ).G) :
    bondIndex (stSt S σ).G (fun n => zS (nodeCast σ h n)) y = bondIndex S zS ((stSt S σ).M.od y) := bondIndex_nodeCastMk (Mk := ∅) σ h zS y

theorem splicedEpsilon_empty {d : ℕ} (G : Garden w) (z : GNode G.tree → (Fin d → ℤ)) :
    splicedEpsilon G ∅ z = epsDec G z := by
  unfold splicedEpsilon epsDec
  simp

end WaveTurbulence.Represents
