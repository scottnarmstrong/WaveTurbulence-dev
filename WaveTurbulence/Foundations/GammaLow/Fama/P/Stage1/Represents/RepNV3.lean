/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepNV3` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.Stage1.Represents.RepNum1
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepNV3
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS: the core representation with the numerical slot bounds

Per-slot mass bounds `μ_s ≤ K x^{sz_s} L^{-e g_s} lf_s` with `∏ lf_s` the leaf size of the profile, `∑ sz_s = nrest`,
`∑ g_s = gsum` give the mass bound `Cχ^{#branches} ballCard^{order} K^{#slots} x^{nrest} L^{-e gsum} ∑_i |sign_i| leaf_i`.
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
theorem repIntC_core2 {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
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
    (K x e : ℝ) (hK : 1 ≤ K) (hx0 : 0 ≤ x) (nrest gsum : ℕ)
    (hslots : ∀ i, ∃ Rep : SlotRep S hS P.d (fun b => layer (D.coreBranch hS b).toNode) tt,
      Rep.Fn = slotFn D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i) layer hLayer ∧
      ∃ (sz g : ReplacementSlot S → ℕ) (lf : ReplacementSlot S → ℝ), (∀ s, 0 ≤ lf s) ∧
        (∀ s, Rep.μ s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-e * (g s : ℝ)) * lf s)) ∧
        ∏ s, lf s = leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i) ∧
        ∑ s, sz s = nrest ∧ ∑ s, g s = gsum) :
    RepIntC π tt base roots
      (F.valueSel tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)))
      (Cchi P.d ^ Fintype.card (GBranch S.tree) * ((nodeBallCard P.d ^ ∑ j, (S.tree j).order : ℕ) : ℝ) *
        @Finset.sum (F.ι (layeredReconstruction D hS layer hLayer)) ℝ _
          (@Finset.univ _ (F.fin (layeredReconstruction D hS layer hLayer)))
          fun i => |F.sign (layeredReconstruction D hS layer hLayer) i| *
            (K ^ Fintype.card (ReplacementSlot S) * x ^ nrest * P.L ^ (-e * (gsum : ℝ)) *
              leafSizeProduct (layeredReconstruction D hS layer hLayer)
                (F.B (layeredReconstruction D hS layer hLayer) i))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  choose Rep hFn sz g lf hlf hμ hprod hsz hg using hslots
  refine repIntC_core hd1 hL1 D hS layer hLayer F hctrl tt base roots gs selSk hgsp π hG hh hlay hgs
    (fun i => K ^ Fintype.card (ReplacementSlot S) * x ^ nrest * P.L ^ (-e * (gsum : ℝ)) *
      leafSizeProduct (layeredReconstruction D hS layer hLayer)
        (F.B (layeredReconstruction D hS layer hLayer) i)) (fun i => ?_)
    (fun i => ⟨Rep i, hFn i, ?_⟩)
  · have : 0 ≤ leafSizeProduct (layeredReconstruction D hS layer hLayer)
        (F.B (layeredReconstruction D hS layer hLayer) i) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hK0 : 0 ≤ K := by linarith
    positivity
  · have hm : ∀ s, 0 ≤ K * x ^ (sz i s) * P.L ^ (-e * (g i s : ℝ)) * lf i s :=
      fun s => by have := hlf i s; positivity
    calc ∏ s, (Rep i).μ s ≤ ∏ s, ENNReal.ofReal (K * x ^ (sz i s) * P.L ^ (-e * (g i s : ℝ)) * lf i s) :=
          Finset.prod_le_prod (fun s _ => hμ i s)
      _ = ENNReal.ofReal (∏ s, (K * x ^ (sz i s) * P.L ^ (-e * (g i s : ℝ)) * lf i s)) :=
          (ENNReal.ofReal_prod_of_nonneg fun s _ => hm s).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.prod_mul_distrib, hprod i, ← hsz i, ← hg i]
          have hK0 : 0 ≤ K := by linarith
          have hleaf : 0 ≤ leafSizeProduct (layeredReconstruction D hS layer hLayer)
              (F.B (layeredReconstruction D hS layer hLayer) i) :=
            Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
          have := prod_slot_masses (fun s => K * x ^ (sz i s) * P.L ^ (-e * (g i s : ℝ))) (sz i) (g i) K x P.L e
            hK hx0 hL0 (fun s => ⟨by positivity, le_rfl⟩)
          exact mul_le_mul_of_nonneg_right this hleaf

end WaveTurbulence.GammaLow.Fama.Represents
