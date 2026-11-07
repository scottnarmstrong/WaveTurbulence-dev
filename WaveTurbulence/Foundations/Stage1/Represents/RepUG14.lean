/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG13
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG8
import Mathlib.Tactic

/-!
# S2 REPRESENTS, G1 in the shape of `exists_hinge_data_units_leaf_w`

`leafFlag σ hM j : Fin 3 → Prop`: coordinate `i ∈ {1, 2}` of unit `j` is flagged when its lower child has a root time as `G_sb`
clock (a leaf).  `g1_units`: the hypothesis `G1` of `exists_hinge_data_units_leaf_w` for the units of `stSt S σ`, with the dummy
time `td j i = qOutOf … i`.  Its V5-side inputs (named, owner V5-KIND, R74): `qOut i = lay c` for a branch lower child `c`
(`lay_branch_child` computes `lay c` as the layer of the core), and `qOut 1, qOut 2 ≤ qOut 0`.
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

/-- The flagged (leaf lower child) clock coordinates of unit `j`. -/
def leafFlag {Mk : Set (Stage1.CLVine S)} (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (j : Fin (unitBlocks S σ Mk).length) : Fin 3 → Prop :=
  fun i => (i = 1 ∧ ∃ r, nodeClk (stSt S σ Mk).G ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j 2) = Sum.inl r) ∨
    (i = 2 ∧ ∃ r, nodeClk (stSt S σ Mk).G ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j 3) = Sum.inl r)

/-- B1b (Mk-general form of `leafFlag_zero`). -/
theorem leafFlag_zeroMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length) :
    ¬ leafFlag hM σ j 0 := by
  unfold leafFlag
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem leafFlag_zero (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) :
    ¬ leafFlag hM σ j 0 := leafFlag_zeroMk (Mk := ∅) hM σ j

/-- B1b (Mk-general form of `leafFlag_one`). -/
theorem leafFlag_oneMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length) :
    leafFlag hM σ j 1 ↔ ∃ r, nodeClk (stSt (Mk := Mk) S σ).G ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 2) = Sum.inl r := by
  unfold leafFlag
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h (by decide)
  · intro h; exact Or.inl ⟨rfl, h⟩

theorem leafFlag_one (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) :
    leafFlag hM σ j 1 ↔ ∃ r, nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 2) = Sum.inl r := leafFlag_oneMk (Mk := ∅) hM σ j

/-- B1b (Mk-general form of `leafFlag_two`). -/
theorem leafFlag_twoMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length) :
    leafFlag hM σ j 2 ↔ ∃ r, nodeClk (stSt (Mk := Mk) S σ).G ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 3) = Sum.inl r := by
  unfold leafFlag
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd h (by decide)
    · exact h
  · intro h; exact Or.inr ⟨rfl, h⟩

theorem leafFlag_two (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) :
    leafFlag hM σ j 2 ↔ ∃ r, nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 3) = Sum.inl r := leafFlag_twoMk (Mk := ∅) hM σ j

open scoped Classical in
/-- B1b (Mk-general form of `g1_units`). -/
theorem g1_unitsMk (P : WTParams) (hM : S.molecule.IsMolecule) (σ : Prescription S) (hM9 : VINEPARAM)
    {Mk : Set (Stage1.CLVine _)} {n₀ : Fin (unitBlocks (Mk := Mk) S σ).length → ℕ}
    {B₀ : ∀ j, CLChainAssembly S (regionOf (unitBlkMk (Mk := Mk) hM σ j)) (n₀ j)}
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (base : Mom P.d) (tt : Fin w → ℝ)
    (roots : Fin w → (Fin P.d → ℤ)) (selSk : GenDecoration (stSt (Mk := Mk) S σ).G P.d roots 0 → Prop)
    (centre : Fin (unitBlocks (Mk := Mk) S σ).length → (Fin 4 → Fin P.d → ℤ) → Fin 4 → Mom P.d)
    (hb1 : ∀ j c, nodeClk (stSt (Mk := Mk) S σ).G ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 2) = Sum.inr c →
      qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 1 =
        (stSt (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG)) c)
    (hb2 : ∀ j c, nodeClk (stSt (Mk := Mk) S σ).G ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j 3) = Sum.inr c →
      qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 2 =
        (stSt (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG)) c)
    (hqle : ∀ j, qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 0) :
    ∀ κ : GenDecoration (stSt (Mk := Mk) S σ).G P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain (stSt (Mk := Mk) S σ).G
        ((stSt (Mk := Mk) S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG))) tt, ∀ j (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape (Mk := Mk) hM σ).hmom (unitBlkMk_disj (Mk := Mk) hM σ) j i))) - latPt P.d (c i)‖ ≤ 1) →
        (fun i => if leafFlag hM σ j i then
            ((qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) i : ℕ) : ℝ)
          else clockOf (stSt (Mk := Mk) S σ).G tt τ ((stShape (Mk := Mk) hM σ).hclk (unitBlkMk_disj (Mk := Mk) hM σ) j i)) ∈
          outBoxW (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) := by
  intro κ _ τ hτ j c _
  refine g1_weak (stShape (Mk := Mk) hM σ) (unitBlkMk_disj (Mk := Mk) hM σ) j tt _ hτ
    (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) ?_ (hb1 j) (hb2 j) (hqle j).1 (hqle j).2
    (leafFlag hM σ j) (leafFlag_zeroMk (Mk := Mk) hM σ j) (leafFlag_oneMk (Mk := Mk) hM σ j) (leafFlag_twoMk (Mk := Mk) hM σ j)
  exact (lay_hingeMk (Mk := Mk) hM σ j RD hG layer hLayer).symm

open scoped Classical in
theorem g1_units (P : WTParams) (hM : S.molecule.IsMolecule) (σ : Prescription S) (hM9 : VINEPARAM)
    {n₀ : Fin (unitBlocks S σ).length → ℕ}
    {B₀ : ∀ j, CLChainAssembly S (regionOf (unitBlk hM σ j)) (n₀ j)}
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (base : Mom P.d) (tt : Fin w → ℝ)
    (roots : Fin w → (Fin P.d → ℤ)) (selSk : GenDecoration (stSt S σ).G P.d roots 0 → Prop)
    (centre : Fin (unitBlocks S σ).length → (Fin 4 → Fin P.d → ℤ) → Fin 4 → Mom P.d)
    (hb1 : ∀ j c, nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 2) = Sum.inr c →
      qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 1 =
        (stSt S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG)) c)
    (hb2 : ∀ j c, nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 3) = Sum.inr c →
      qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 2 =
        (stSt S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG)) c)
    (hqle : ∀ j, qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 0) :
    ∀ κ : GenDecoration (stSt S σ).G P.d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain (stSt S σ).G
        ((stSt S σ).layer (RegRed.coreLayer (layeredReconstruction RD hG layer hLayer) RD hG
          (RD.garden_decodes hG))) tt, ∀ j (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i))) - latPt P.d (c i)‖ ≤ 1) →
        (fun i => if leafFlag hM σ j i then
            ((qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) i : ℕ) : ℝ)
          else clockOf (stSt S σ).G tt τ ((stShape hM σ).hclk (unitBlk_disj hM σ) j i)) ∈
          outBoxW (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) := g1_unitsMk (Mk := ∅) P hM σ hM9 RD hG layer hLayer base tt roots selSk centre hb1 hb2 hqle

/-- B1b (Mk-general form of `qOut_le_qOut_zero`). -/
theorem qOut_le_qOut_zeroMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (j : Fin (unitBlocks (Mk := Mk) S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer)
    (hb : qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 1 ≤
        layer (RD.coreBranch hG (unitBlkMk (Mk := Mk) hM σ j).lower).toNode ∧
      qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 2 ≤
        layer (RD.coreBranch hG (unitBlkMk (Mk := Mk) hM σ j).lower).toNode) :
    qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlkMk (Mk := Mk) hM σ j).upper (unitBlkMk (Mk := Mk) hM σ j).lower (regionOf (unitBlkMk (Mk := Mk) hM σ j)) 0 := by
  have hle := layer_core_le_upper (unitBlkMk (Mk := Mk) hM σ j) RD hG layer hLayer (unitBlkMk (Mk := Mk) hM σ j).lower
    (unitBlkMk (Mk := Mk) hM σ j).isBlock.2.2.1
  exact ⟨hb.1.trans hle, hb.2.trans hle⟩

/-- `qOut 1, qOut 2 ≤ qOut 0` from the V5 fact that the output layers of the lower children are at most the layer of the core
of the lower joint (`layer_outNode_le` in the R74 box) and the monotonicity of core layers along the unit. -/
theorem qOut_le_qOut_zero (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length)
    (RD : ReconstructionData S) (hG : S.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer)
    (hb : qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 1 ≤
        layer (RD.coreBranch hG (unitBlk hM σ j).lower).toNode ∧
      qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 2 ≤
        layer (RD.coreBranch hG (unitBlk hM σ j).lower).toNode) :
    qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 1 ≤
        qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 0 ∧
      qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 2 ≤
        qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 0 := qOut_le_qOut_zeroMk (Mk := ∅) hM σ j RD hG layer hLayer hb

end WaveTurbulence.Represents
