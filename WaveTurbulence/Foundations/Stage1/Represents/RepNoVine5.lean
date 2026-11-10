/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine4
public import WaveTurbulence.Foundations.Stage1.Represents.RepBr8
import Mathlib.Tactic

/-!
# S2 REPRESENTS: `RepresentsInt` of the vine-free Stage 1 piece `stage1PieceOf` (the case `𝒱_0 = ∅`)

For a regular reconstruction `D` of the skeleton `S` (with the original garden `LG = layeredReconstruction D ..`)
and a prescription `σ` with no spliced unit (`unitBlocks S σ = []`), the piece `stage1PieceOf` has
`G_sb = S`, no hinges, `b_sk = 0` and `g_sk = g_reg`, and its `RepresentsInt` is `represents_noVine_core`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice
  WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed

variable {R : ℕ}

/-- B1b (Mk-general form of `unitIngredients_noVine`). -/
theorem unitIngredients_noVineMk {S : Garden (2 * R)} (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = []) :
    unitIngredients (Mk := Mk) S σ = ∅ := by
  ext T
  simp [unitIngredients, h]

/-- B1b (Mk-general form of `bskOf_noVine`). -/
theorem bskOf_noVineMk {S : Garden (2 * R)} (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = []) :
    bskOf (Mk := Mk) S σ = 0 := by
  unfold bskOf
  rw [unitIngredients_noVineMk (Mk := Mk) σ h]
  simp

theorem bskOf_noVine {S : Garden (2 * R)} (σ : Prescription S) (h : unitBlocks S σ = []) :
    bskOf S σ = 0 := bskOf_noVineMk (Mk := ∅) σ h

/-- B1b (Mk-general form of `gskOf_noVine`). -/
theorem gskOf_noVineMk {S : Garden (2 * R)} (g : ℕ) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = [])
    (l : GBranch S.tree → ℕ) : gskOf (Mk := Mk) g S σ l = g := by
  unfold gskOf
  have : (Set.toFinite (unitIngredients (Mk := Mk) S σ)).toFinset = ∅ := by
    ext T; simp [unitIngredients_noVineMk (Mk := Mk) σ h]
  rw [this]
  simp

theorem gskOf_noVine {S : Garden (2 * R)} (g : ℕ) (σ : Prescription S) (h : unitBlocks S σ = [])
    (l : GBranch S.tree → ℕ) : gskOf g S σ l = g := gskOf_noVineMk (Mk := ∅) g σ h l

theorem gregOf_eq_sum_slotIncoh {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    gregOf D hS (RegRed.layeredReconstruction D hS layer hLayer) = ∑ s, slotIncoh D hS layer hLayer s := by
  rw [Fintype.sum_sum_type]
  unfold gregOf
  congr 1
  · exact Finset.sum_congr rfl fun p _ => couple_incoherency_eq D hS layer hLayer p
  · exact Finset.sum_congr rfl fun b _ => tree_incoherency_eq D hS layer hLayer b

end WaveTurbulence.Represents
