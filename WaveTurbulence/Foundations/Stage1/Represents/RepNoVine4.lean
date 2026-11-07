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

/-- The gap specification of the vine-free piece, over the skeleton. -/
noncomputable def gsCast (σ : Prescription S) (h : unitBlocks S σ = []) :
    (v : GBranch S.tree) → Option (LocalGapSpecification S v) :=
  (stSt_G_eq_of_unitBlocks_empty σ h) ▸ gapSpecification S σ

theorem heq_cast_gapSpec (G' : Garden w) (e : G' = S)
    (gsp : (v : GBranch G'.tree) → Option (LocalGapSpecification G' v)) : HEq gsp (e ▸ gsp) := by
  subst e; rfl

theorem heq_gapSpec (σ : Prescription S) (h : unitBlocks S σ = []) :
    HEq (gapSpecification S σ) (gsCast σ h) :=
  heq_cast_gapSpec (stSt S σ).G (stSt_G_eq_of_unitBlocks_empty σ h) _

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

open scoped Classical in
theorem hgsp_noVine (hM : S.molecule.IsMolecule) (hp : S.IsPlain) (σ : Prescription S)
    (h : unitBlocks S σ = []) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) :
    ∀ D' : SplicedKernelData S d, D'.gapSpecification = gsCast σ h → ∀ z : GenDecoration S d roots 0,
      splicedGapIndicator S D' L γ η base z.1 =
        if selOf (GroupPrescription.ofPrescription σ) L γ η base z.1 then 1 else 0 := by
  intro D' hD' z
  have e := stSt_G_eq_of_unitBlocks_empty σ h
  rw [transport_gapIndicator (stSt S σ).G e D']
  have hD'' := transport_gapSpec (stSt S σ).G e (gapSpecification S σ) D' hD'
  have := gapIndicator_noVine hM hp σ h hL γ η base roots z (e.symm ▸ D') hD''
  convert this using 2
  funext n
  exact congrArg (fun x => z.1 x) (cast_node_eq (stSt S σ).G e n)

end WaveTurbulence.Represents
