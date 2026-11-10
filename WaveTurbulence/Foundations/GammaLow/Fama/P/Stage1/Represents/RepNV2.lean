/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepNV2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Represents.RepNV1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepNV2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepNoVine2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS: the core representation of a vine-free piece from per-slot superpositions

`repIntC_core`: for a leaf family `F` controlled on `LG = layeredReconstruction D hS layer hLayer` and per-slot
superpositions (`SlotRep`) of the slot kernels `slotFn` of every profile `F.H LG i`, the family value
`F.valueSel … (sel ∘ collapse)` is a count-measure representation by spliced kernels of the piece with
`π.Gsb = S`, no hinges, layer and gap data those of the skeleton.
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
theorem repIntC_core {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
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
    (Bi : F.ι (layeredReconstruction D hS layer hLayer) → ℝ) (hBi : ∀ i, 0 ≤ Bi i)
    (hslots : ∀ i, ∃ Rep : SlotRep S hS P.d (fun b => layer (D.coreBranch hS b).toNode) tt,
      Rep.Fn = slotFn D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i) layer hLayer ∧
      ∏ s, Rep.μ s ≤ ENNReal.ofReal (Bi i)) :
    RepIntC π tt base roots
      (F.valueSel tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)))
      (Cchi P.d ^ Fintype.card (GBranch S.tree) * ((nodeBallCard P.d ^ ∑ j, (S.tree j).order : ℕ) : ℝ) *
        @Finset.sum (F.ι (layeredReconstruction D hS layer hLayer)) ℝ _
          (@Finset.univ _ (F.fin (layeredReconstruction D hS layer hLayer)))
          fun i => |F.sign (layeredReconstruction D hS layer hLayer) i| * Bi i) := by
  obtain ⟨Gsb, Cs, lad, play, gsp, gsk, bsk⟩ := π
  simp only at hG hh hlay hgs
  subst hG
  have hlay' := eq_of_heq hlay
  have hgs' := eq_of_heq hgs
  subst hlay' hgs'
  letI := F.fin (layeredReconstruction D hS layer hLayer)
  obtain ⟨hCge, hCspec⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  rw [LeafFamily.valueSel_skeleton_reduction F D hS layer hLayer hctrl hd1 hL1 tt base roots selSk]
  refine RepIntC.mono (RepIntC.finset_sum (Finset.univ) _ (fun i =>
    ‖((F.sign (layeredReconstruction D hS layer hLayer) i : ℝ) : ℂ)‖ *
      (Cchi P.d ^ Fintype.card (GBranch Gsb.tree) * ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ) * Bi i))
    (fun i _ => by have := hBi i; positivity) (fun i _ => ?_)) (le_of_eq ?_)
  · obtain ⟨Rep, hFn, hmass⟩ := hslots i
    let A := asmOf hS hd1 P.L hL0 P.γ P.δ P.η base roots tt (fun b => layer (D.coreBranch hS b).toNode) gsp selSk hgsp
      (Cchi P.d) hCpos (hCspec) Rep
    have hskel : ∀ (κ : GenDecoration Gsb P.d roots 0) (τ : GBranch Gsb.tree → ℝ), A.skel κ τ = reducedStarProductLeaves D hS P.L P.γ P.δ
        (F.H (layeredReconstruction D hS layer hLayer) i) layer hLayer tt base κ.1 τ := by
      intro κ τ
      show ∏ s, Rep.Fn s (slotTs hS tt τ s) (base + latticePoint P.L (κ.1 (slotNode hS s))) = _
      rw [hFn]
      exact prod_slotFn D hS P.L P.γ P.δ _ layer hLayer tt base κ.1 τ
    refine RepIntC.smul (repIntC_of_asm _ A tt base roots
      (Cchi P.d ^ Fintype.card (GBranch Gsb.tree) * ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ) * Bi i)
      hh rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ _ ?_) _
    · have := hBi i; positivity
    · have hμ := asmOf_mass hS hd1 P.L hL0 P.γ P.δ P.η base roots tt (fun b => layer (D.coreBranch hS b).toNode)
        gsp selSk hgsp (Cchi P.d) hCpos hCspec Rep
      show ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch Gsb.tree)) * ((∏ s, ∑' l,
        ENNReal.ofReal (A.fam.w s l)) * ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ≥0∞)) ≤ _
      calc ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch Gsb.tree)) * ((∏ s, ∑' l,
          ENNReal.ofReal (A.fam.w s l)) * ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ≥0∞))
          ≤ ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch Gsb.tree)) * (ENNReal.ofReal (Bi i) *
            ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ≥0∞)) := by
            gcongr
            exact hμ.trans hmass
        _ = _ := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by have := hBi i; positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; push_cast; ring
    · show _ = (coupling P.d P.L P.γ P.δ : ℂ) ^ Gsb.order * Gsb.zeta * ∑' κ : GenDecoration Gsb P.d roots 0,
        (if selSk κ then ((epsDec Gsb κ.1 : ℝ) : ℂ) * ∫ τ, (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
          (fun τ => phaseProd P.L P.γ P.δ Gsb (cosetDecoration Gsb P.L base κ.1) τ * A.skel κ τ) τ else 0)
      refine congrArg _ (tsum_congr fun κ => ?_)
      split_ifs
      · congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only [Set.indicator]
        split_ifs
        · rw [hskel κ τ]
        · rfl
      · rfl
  · simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end WaveTurbulence.GammaLow.Fama.Represents
