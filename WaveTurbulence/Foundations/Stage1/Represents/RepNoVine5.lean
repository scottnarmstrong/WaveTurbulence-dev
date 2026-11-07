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

theorem unitIngredients_noVine {S : Garden (2 * R)} (σ : Prescription S) (h : unitBlocks S σ = []) :
    unitIngredients S σ = ∅ := unitIngredients_noVineMk (Mk := ∅) σ h

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

open scoped Classical in
/-- **`RepresentsInt` of the vine-free piece** (TARGET (redvine2)-(redvine3), L1950-L1976, for `𝒱_0 = ∅`).
The piece is `stage1PieceOf` at the parameter record `{Pg with C₁ := C}` (finding F-CONST: the gates are used at
the gate constant `Pg.C₁`, the piece at any `C ≥ Cmin`). -/
theorem represents_noVine (Pg : WTParams) (E : GateEnv Pg) :
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ Cmin = CminF Pg.d Pg.η Pg.C₁ ∧ ∀ (C : ℝ), Cmin ≤ C →
      ∀ {R : ℕ} {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
        (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
        p < Pg.D → D.size ≤ Pg.N (p + 1) ^ 4 →
        IsCanonGC (p + 1) (RegRed.layeredReconstruction D hS layer hLayer) →
        ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
        ∀ (F : LeafFamily { Pg with C₁ := C } (2 * R)),
        F.Controlled (RegRed.layeredReconstruction D hS layer hLayer) →
        ∀ (base : Mom Pg.d) (roots : Fin (2 * R) → (Fin Pg.d → ℤ)) (σ : Prescription S),
        unitBlocks S σ = [] → S.molecule.IsMolecule →
        ∀ (n : ℕ) (s : ℝ), F.size (RegRed.layeredReconstruction D hS layer hLayer) ≤ s →
        n - S.order = D.size →
        Stage1Piece.RepresentsInt (P := { Pg with C₁ := C })
          (stage1PieceOf Pg.d hS (RegRed.layeredReconstruction D hS layer hLayer) (D.garden_decodes hS) σ)
          n tt base roots s
          (F.valueSel tt base roots (RegRed.layeredReconstruction D hS layer hLayer)
            (fun κ => selOf (GroupPrescription.ofPrescription σ) Pg.L Pg.γ Pg.η base
              (collapseGenDecoration D hS κ).1)) := by
  obtain ⟨Cmin, hC1, hCe, hcore⟩ := represents_noVine_core Pg E
  refine ⟨Cmin, hC1, hCe, fun C hC R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs
    hnrest => ?_⟩
  have hL : Pg.L ≠ 0 := by have := E.hL1; positivity
  refine hcore C hC D hS layer hLayer p hp hN hcan tt htt F hctrl base roots (gsCast σ hσ)
    (fun z => selOf (GroupPrescription.ofPrescription σ) Pg.L Pg.γ Pg.η base z.1)
    (hgsp_noVine hM hS σ hσ hL Pg.γ Pg.η base roots)
    (stage1PieceOf Pg.d hS (RegRed.layeredReconstruction D hS layer hLayer) (D.garden_decodes hS) σ)
    (stSt_G_eq_of_unitBlocks_empty σ hσ)
    (stSt_hinges_eq_empty σ hσ) ?_ (heq_gapSpec σ hσ) ?_ ?_ n s hs hnrest
  · have e : RegRed.coreLayer (RegRed.layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS) =
        fun b => layer (D.coreBranch hS b).toNode := rfl
    show HEq ((stSt S σ).layer (RegRed.coreLayer (RegRed.layeredReconstruction D hS layer hLayer) D hS
      (D.garden_decodes hS))) _
    rw [e]
    exact heq_layer σ hσ _
  · exact bskOf_noVine σ hσ
  · show gskOf _ S σ _ = _
    rw [gskOf_noVine _ σ hσ, gregOf_eq_sum_slotIncoh D hS layer hLayer]

end WaveTurbulence.Represents
