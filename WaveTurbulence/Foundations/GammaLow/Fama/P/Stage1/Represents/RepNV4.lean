/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepNV4` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV3
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceSlotCounts
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepNV4
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS: `RepresentsInt` of a vine-free piece from the per-slot bounds

The remaining bookkeeping: the slot count is `2 n_sb + R`, the branch count and the node ball count are `n_sb`,
the constants are absorbed in `C₁^{n_sb + 2R}` for `Cχ b K² ≤ C₁`, `|sign| ≤ 1` (the D8 hypothesis, R40) and
`F.size ≤ s`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf WaveTurbulence.RegRed

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
open scoped ENNReal WaveTurbulence.GammaLow.FinalCount


open scoped Classical in
theorem representsInt_of_slots {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (F : LeafFamily P (2 * R)) (hctrl : F.Controlled (layeredReconstruction D hS layer hLayer))
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
    (selSk : GenDecoration S P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData S P.d, D'.gapSpecification = gs → ∀ z : GenDecoration S P.d roots 0,
      splicedGapIndicator S D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (π : Stage1PieceG P R) (hG : π.Gsb = S) (hh : π.Cs.hinges = ∅)
    (hlay : HEq π.layer (fun b => layer (D.coreBranch hS b).toNode))
    (hgs : HEq π.gapSpecification gs)
    (K : ℝ) (hK : 1 ≤ K) (hCbig : Cchi P.d * (nodeBallCard P.d : ℝ) * K ^ 2 ≤ P.C₁)
    (hx0 : 0 ≤ P.C₁ * Real.sqrt P.δ)
    (n : ℕ) (s : ℝ) (hs : F.size (layeredReconstruction D hS layer hLayer) ≤ s)
    (hbsk : π.bsk = 0) (hnrest : n - S.order = D.size)
    (hslots : ∀ i, ∃ Rep : SlotRep S hS P.d (fun b => layer (D.coreBranch hS b).toNode) tt,
      Rep.Fn = slotFn D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i) layer hLayer ∧
      ∃ (sz g : ReplacementSlot S → ℕ) (lf : ReplacementSlot S → ℝ), (∀ s, 0 ≤ lf s) ∧
        (∀ s, Rep.μ s ≤ ENNReal.ofReal (K * (P.C₁ * Real.sqrt P.δ) ^ (sz s) *
          P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf s)) ∧
        ∏ s, lf s = leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i) ∧
        ∑ s, sz s = D.size ∧ ∑ s, g s = π.gsk) :
    π.RepresentsInt n tt base roots s
      (F.valueSel tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hb1 : (1 : ℝ) ≤ nodeBallCard P.d := by exact_mod_cast nodeBallCard_pos P.d
  have hC1 : 1 ≤ P.C₁ := by
    calc (1 : ℝ) ≤ Cchi P.d * (nodeBallCard P.d : ℝ) * K ^ 2 := by
          have h1 : 1 ≤ Cchi P.d * (nodeBallCard P.d : ℝ) := one_le_mul_of_one_le_of_one_le hCge hb1
          nlinarith
      _ ≤ P.C₁ := hCbig
  obtain ⟨Gsb, Cs, lad, play, gsp, gsk, bsk⟩ := π
  simp only at hG hh hlay hgs hbsk hslots
  subst hG
  have hcore := repIntC_core2 hd1 hL1 D hS layer hLayer F hctrl tt base roots gs selSk hgsp
    ⟨Gsb, Cs, lad, play, gsp, gsk, bsk⟩ rfl hh hlay hgs K (P.C₁ * Real.sqrt P.δ) (P.η ^ 8) hK hx0
    D.size gsk hslots
  refine RepIntC.toRepresentsInt hcore n s ?_
  letI := F.fin (layeredReconstruction D hS layer hLayer)
  have hbr : Fintype.card (GBranch Gsb.tree) = Gsb.order := WaveTurbulence.Mole.card_gbranch Gsb.tree
  have hpairs := sourcePair_card_twice Gsb hS
  have hslotsc : Fintype.card (ReplacementSlot Gsb) = 2 * Gsb.order + R := by
    unfold ReplacementSlot
    rw [Fintype.card_sum, hbr]
    omega
  have hord : ∑ j, (Gsb.tree j).order = Gsb.order := rfl
  rw [hbr, hslotsc, hord]
  show _ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - Gsb.order) * P.C₁ ^ (Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (gsk : ℝ) - P.η ^ 2 / 2 * (bsk : ℝ) + P.η ^ 7 * (Cs.hinges.card : ℝ)) * s
  rw [hnrest, hbsk, hh]
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero, add_zero]
  have hcabs := const_absorb (Cchi P.d) (nodeBallCard P.d : ℝ) K P.C₁ Gsb.order R hCge hb1 hK hCbig
  push_cast
  have hA : 0 ≤ (P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ)) :=
    mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg hL0.le _)
  have hK0 : 0 ≤ K := by linarith
  have hleaf : ∀ i, 0 ≤ leafSizeProduct (layeredReconstruction D hS layer hLayer)
      (F.B (layeredReconstruction D hS layer hLayer) i) :=
    fun i => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hsum : ∑ i, |F.sign (layeredReconstruction D hS layer hLayer) i| *
      (K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ)) *
        leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i)) ≤
      K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) *
        F.size (layeredReconstruction D hS layer hLayer) := by
    unfold LeafFamily.size
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h0 : 0 ≤ K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size *
        P.L ^ (-P.η ^ 8 * (gsk : ℝ)) * leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i) := by
      have := hleaf i
      have : 0 ≤ K ^ (2 * Gsb.order + R) := pow_nonneg hK0 _
      positivity
    calc _ ≤ 1 * (K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size *
          P.L ^ (-P.η ^ 8 * (gsk : ℝ)) * leafSizeProduct (layeredReconstruction D hS layer hLayer)
            (F.B (layeredReconstruction D hS layer hLayer) i)) :=
          mul_le_mul_of_nonneg_right (F.sign_abs_le _ i) h0
      _ = _ := by ring
  have hCh : 0 ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order := by
    have : 0 ≤ Cchi P.d := by linarith
    positivity
  calc _ ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order *
        (K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) *
          F.size (layeredReconstruction D hS layer hLayer)) := by
        exact mul_le_mul_of_nonneg_left hsum hCh
    _ ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order *
        (K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) * s) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by positivity)) hCh
    _ = (Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order * K ^ (2 * Gsb.order + R)) *
        (((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) * s) := by ring
    _ ≤ P.C₁ ^ (Gsb.order + 2 * R) * (((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) * s) := by
        refine mul_le_mul_of_nonneg_right hcabs ?_
        have : 0 ≤ s := le_trans (Finset.sum_nonneg fun i _ => hleaf i) hs
        positivity
    _ = _ := by ring

end WaveTurbulence.GammaLow.Fama.Represents
