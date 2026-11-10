/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG14
import Mathlib.Tactic

/-!
# S2 REPRESENTS, the V5-KIND (R74) discharge of `hb1`, `hb2`, `hqle` of `g1_units`

With `qOutOf` defined through `outNode` (V5-KIND, R74), the unit-interval index of a branch lower child is the layer of its
core (`lay_branch_child`), and the output indices of the lower children are bounded by the layer of the core of the lower joint
(`layer_outNode_le`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS2 WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 VineParamContract WaveTurbulence.RegRedLeaf

variable {w : ℕ} {S : Garden w}

/-- B1b (Mk-general form of `qOut_one_eq_lay`). -/
theorem qOut_one_eq_layMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (c : GBranch (stSt (Mk := Mk) S σ).G.tree)
    (hc : nodeClk (stSt (Mk := Mk) S σ).G ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 2) = Sum.inr c) :
    qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 1 =
      (stSt (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
        (RD.garden_decodes hG)) c := by
  obtain ⟨hb, h⟩ := lay_branch_childMk (Mk := Mk) hM σ j RD hG layer hLayer 2 c hc
  rw [h]
  have hb' : ((unitBlkMk (Mk := Mk) hM σ j).lower.child (regionOf (unitBlkMk (Mk := Mk) hM σ j)).positive).1.2 ∈
      (S.tree ((unitBlkMk (Mk := Mk) hM σ j).lower.child (regionOf (unitBlkMk (Mk := Mk) hM σ j)).positive).1.1).branching := hb
  show layer (outNode RD hG ((unitBlkMk (Mk := Mk) hM σ j).lower.child (regionOf (unitBlkMk (Mk := Mk) hM σ j)).positive)) = _
  unfold outNode
  simp only [hb', ↓reduceDIte]
  rfl

theorem qOut_one_eq_lay (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (c : GBranch (stSt S σ).G.tree)
    (hc : nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 2) = Sum.inr c) :
    qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 1 =
      (stSt S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
        (RD.garden_decodes hG)) c := qOut_one_eq_layMk (Mk := ∅) hM σ j RD hG layer hLayer c hc

/-- B1b (Mk-general form of `qOut_two_eq_lay`). -/
theorem qOut_two_eq_layMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (c : GBranch (stSt (Mk := Mk) S σ).G.tree)
    (hc : nodeClk (stSt (Mk := Mk) S σ).G ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 3) = Sum.inr c) :
    qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 2 =
      (stSt (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
        (RD.garden_decodes hG)) c := by
  obtain ⟨hb, h⟩ := lay_branch_childMk (Mk := Mk) hM σ j RD hG layer hLayer 3 c hc
  rw [h]
  have hb' : ((unitBlkMk (Mk := Mk) hM σ j).lower.child (regionOf (unitBlkMk (Mk := Mk) hM σ j)).negative).1.2 ∈
      (S.tree ((unitBlkMk (Mk := Mk) hM σ j).lower.child (regionOf (unitBlkMk (Mk := Mk) hM σ j)).negative).1.1).branching := hb
  show layer (outNode RD hG ((unitBlkMk (Mk := Mk) hM σ j).lower.child (regionOf (unitBlkMk (Mk := Mk) hM σ j)).negative)) = _
  unfold outNode
  simp only [hb', ↓reduceDIte]
  rfl

theorem qOut_two_eq_lay (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (c : GBranch (stSt S σ).G.tree)
    (hc : nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 3) = Sum.inr c) :
    qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 2 =
      (stSt S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
        (RD.garden_decodes hG)) c := qOut_two_eq_layMk (Mk := ∅) hM σ j RD hG layer hLayer c hc

/-- B1b (Mk-general form of `qOut_le_core`). -/
theorem qOut_le_coreMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) :
    qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 1 ≤
        layer (RD.coreBranch hG (unitBlkMk (Mk := Mk) hM σ j).lower).toNode ∧
      qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 2 ≤
        layer (RD.coreBranch hG (unitBlkMk (Mk := Mk) hM σ j).lower).toNode :=
  ⟨layer_outNode_le RD hG layer hLayer _ _, layer_outNode_le RD hG layer hLayer _ _⟩

/-- B1b (Mk-general form of `hqle_units`). -/
theorem hqle_unitsMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) :
    qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 0 :=
  qOut_le_qOut_zeroMk (Mk := Mk) hM σ j RD hG layer hLayer (qOut_le_coreMk (Mk := Mk) hM σ j RD hG layer hLayer)

theorem hqle_units (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) :
    qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 0 := hqle_unitsMk (Mk := ∅) hM σ j RD hG layer hLayer

end WaveTurbulence.Represents
