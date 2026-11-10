/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine3
public import WaveTurbulence.Foundations.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlot2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: transport lemmas for the vine-free piece `stage1PieceOf` (`G_sb = S`)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice

variable {w : ℕ} {S : Garden w}

theorem heq_cast_gapSpec (G' : Garden w) (e : G' = S)
    (gsp : (v : GBranch G'.tree) → Option (LocalGapSpecification G' v)) : HEq gsp (e ▸ gsp) := by
  subst e; rfl

/-- B1b (Mk-general form of `heq_layer`). -/
theorem heq_layerMk (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = []) (f : GBranch S.tree → ℕ) :
    HEq ((stSt (Mk := Mk) S σ).layer f) f := by
  have key : ∀ st : SpState S, st = SpState.init S → HEq (st.layer f) f := by
    rintro st rfl
    exact HEq.rfl
  exact key _ (stSt_eq_init_of_unitBlocks_emptyMk (Mk := Mk) σ h)

theorem heq_layer (σ : Prescription S) (h : unitBlocks S σ = []) (f : GBranch S.tree → ℕ) :
    HEq ((stSt S σ).layer f) f := heq_layerMk (Mk := ∅) σ h f

theorem cast_node_eq (G' : Garden w) (e : G' = S) (n : GNode G'.tree) :
    (e ▸ n : GNode S.tree) = (congrArg (fun G : Garden w => GNode G.tree) e) ▸ n := by
  subst e; rfl

theorem transport_gapIndicator {d : ℕ} (G' : Garden w) (e : G' = S) (D' : SplicedKernelData S d)
    (L γ η : ℝ) (base : Mom d) (z : GNode S.tree → (Fin d → ℤ)) :
    splicedGapIndicator S D' L γ η base z =
      splicedGapIndicator G' (e.symm ▸ D') L γ η base (fun n => z (e ▸ n)) := by
  subst e; rfl

theorem transport_gapSpec {d : ℕ} (G' : Garden w) (e : G' = S) (gsp : (v : GBranch G'.tree) →
    Option (LocalGapSpecification G' v)) (D' : SplicedKernelData S d) (h : D'.gapSpecification = e ▸ gsp) :
    (e.symm ▸ D' : SplicedKernelData G' d).gapSpecification = gsp := by
  subst e; exact h

end WaveTurbulence.Represents
