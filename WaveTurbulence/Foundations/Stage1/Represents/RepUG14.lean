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
def leafFlag (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) : Fin 3 → Prop :=
  fun i => (i = 1 ∧ ∃ r, nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 2) = Sum.inl r) ∨
    (i = 2 ∧ ∃ r, nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 3) = Sum.inl r)

theorem leafFlag_zero (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) :
    ¬ leafFlag hM σ j 0 := by
  unfold leafFlag
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem leafFlag_one (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) :
    leafFlag hM σ j 1 ↔ ∃ r, nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 2) = Sum.inl r := by
  unfold leafFlag
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h (by decide)
  · intro h; exact Or.inl ⟨rfl, h⟩

theorem leafFlag_two (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) :
    leafFlag hM σ j 2 ↔ ∃ r, nodeClk (stSt S σ).G ((stShape hM σ).hmom (unitBlk_disj hM σ) j 3) = Sum.inl r := by
  unfold leafFlag
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd h (by decide)
    · exact h
  · intro h; exact Or.inr ⟨rfl, h⟩

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
          outBoxW (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) := by
  intro κ _ τ hτ j c _
  refine g1_weak (stShape hM σ) (unitBlk_disj hM σ) j tt _ hτ
    (unitD hM9 (B₀ j) RD hG layer hLayer (centre j c) base) ?_ (hb1 j) (hb2 j) (hqle j).1 (hqle j).2
    (leafFlag hM σ j) (leafFlag_zero hM σ j) (leafFlag_one hM σ j) (leafFlag_two hM σ j)
  exact (lay_hinge hM σ j RD hG layer hLayer).symm

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
        qOutOf RD hG layer (unitBlk hM σ j).upper (unitBlk hM σ j).lower (regionOf (unitBlk hM σ j)) 0 := by
  have hle := layer_core_le_upper (unitBlk hM σ j) RD hG layer hLayer (unitBlk hM σ j).lower
    (unitBlk hM σ j).isBlock.2.2.1
  exact ⟨hb.1.trans hle, hb.2.trans hle⟩

end WaveTurbulence.Represents
