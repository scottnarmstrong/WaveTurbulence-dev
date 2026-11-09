/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepRep1` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm11
public import WaveTurbulence.Foundations.Spine.Stage1Interface
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.ProductFubini
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep1
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel


/-!
# S2 REPRESENTS: `RepresentsInt` of a piece from an assembly context (vine-free, hinge-free)

For a piece `π` with `π.Cs.hinges = ∅` and an assembly context `A` for `π.Gsb` whose layer and gap data are those
of `π`, the value of the skeleton expression is the count-measure integral of the spliced kernels of the
assembled modes (`AsmCtx.value_eq`), with `hingeAmplitude := fun _ => 1` and weight `ζ(G_sb) · constW`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
open scoped ENNReal WaveTurbulence.GammaLow.FinalCount


/-- The bound of `RepresentsInt`. -/
noncomputable def repBound (P : WTParams) {R : ℕ} (π : Stage1PieceG P R) (n : ℕ) (s : ℝ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * s


/-- The count-measure form of `RepresentsInt`, with explicit mass bound `B`. -/
def RepIntC {P : WTParams} {R : ℕ} (π : Stage1PieceG P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (val : ℂ) (B : ℝ) : Prop :=
  ∃ (Ξ : Type) (_ : Countable Ξ) (w : Ξ → ℂ) (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Summable (fun ξ => ‖w ξ * splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖) ∧
    val = ∑' ξ, w ξ * splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∧
    Summable (fun ξ => ‖w ξ‖) ∧ ∑' ξ, ‖w ξ‖ ≤ B ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

theorem RepIntC.toRepresentsInt {P : WTParams} {R : ℕ} {π : Stage1PieceG P R} {tt : Fin (2 * R) → ℝ}
    {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {val : ℂ} {B : ℝ}
    (h : RepIntC π tt base roots val B) (n : ℕ) (s : ℝ) (hB : B ≤ repBound P π n s) :
    π.RepresentsInt n tt base roots s val := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  let _ : MeasurableSpace Ξ := ⊤
  have : MeasurableSingletonClass Ξ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨hint, hint2⟩ := integral_count_eq_tsum _ h1
  obtain ⟨hint', hint2'⟩ := integral_count_real_eq_tsum _ h3.norm
  refine ⟨Ξ, inferInstance, Measure.count, w, ctr, edge, hinge, freq, hint, ?_, hint', ?_, h5⟩
  · rw [hint2]; exact h2
  · rw [hint2']; exact h4.trans hB

open scoped Classical in
theorem repIntC_of_asm {P : WTParams} {R : ℕ} (π : Stage1PieceG P R) (A : AsmCtx π.Gsb P.d)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (B : ℝ)
    (hh : π.Cs.hinges = ∅) (hlay : A.layer0 = π.layer) (hgs : A.gs = π.gapSpecification)
    (hL : A.L = P.L) (hγ : A.γ = P.γ) (hη : A.η = P.η) (hδ : A.δ = P.δ)
    (hbase : A.base = base) (hroots : A.roots = roots) (htt : A.tt = tt)
    (hB : 0 ≤ B)
    (hmass : ENNReal.ofReal (A.Cχ ^ Fintype.card (GBranch π.Gsb.tree)) *
      ((∏ s, ∑' l, ENNReal.ofReal (A.fam.w s l)) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal B)
    (val : ℂ)
    (hval : val = (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0, (if A.selSk κ then ((epsDec π.Gsb κ.1 : ℝ) : ℂ) *
        ∫ τ, (coreTimeDomainW A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * A.skel κ τ) τ else 0)) :
    RepIntC π tt base roots val B := by
  have hcnt : ∀ s, Countable (A.fam.Λ s) := A.fam.cnt
  have hv := A.value_eq
  rw [← hval] at hv
  -- summability of the weights
  have hw_sum : Summable fun ξ : XiT A.fam => ‖π.Gsb.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ := by
    have h1 : ∑' ξ : XiT A.fam, ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top A.mass_ne_top (by simp))) A.tsum_constW_le
    have h2 := ENNReal.summable_toReal h1
    refine h2.congr fun ξ => ?_
    rw [norm_mul, norm_zeta, one_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  -- summability of the values
  have hdbl := (sum_integral_sum_swap (volume : Measure (GBranch π.Gsb.tree → ℝ)) A.gI
    A.meas_gI A.sum_lintegral_ne_top).2
  have hKs : Summable fun ξ : XiT A.fam => ‖π.Gsb.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ *
      splicedKernel π.Gsb (A.D ξ) A.L A.γ A.η A.δ A.base A.roots‖ := by
    have h1 := hdbl.prod
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_)
      (h1.mul_left (‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖))
    calc ‖π.Gsb.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ *
          splicedKernel π.Gsb (A.D ξ) A.L A.γ A.η A.δ A.base A.roots‖
        = ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ *
          splicedKernel π.Gsb (A.D ξ) A.L A.γ A.η A.δ A.base A.roots‖ := by
          rw [mul_assoc, norm_mul, norm_zeta, one_mul]
      _ = ‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖ *
          ‖∑' κ : GenDecoration π.Gsb P.d A.roots 0, ∫ τ, A.gI ξ κ τ‖ := by
          rw [← A.tsum_int_gI ξ, norm_mul]
      _ ≤ ‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖ *
          ∑' κ : GenDecoration π.Gsb P.d A.roots 0, ‖∫ τ, A.gI ξ κ τ‖ := by
          gcongr
          exact norm_tsum_le_tsum_norm (hdbl.prod_factor ξ)
  have hD : ∀ ξ : XiT A.fam, π.data tt (fun x => cenS A.fam ξ (slotOfDart A.hS x))
      (edgeS A.fam A.hS A.Cχ ξ) (fun _ => 1) (freqS A.fam A.hS ξ) = A.D ξ := by
    intro ξ
    have h1 : π.data tt (fun x => cenS A.fam ξ (slotOfDart A.hS x))
        (edgeS A.fam A.hS A.Cχ ξ) (fun _ => 1) (freqS A.fam A.hS ξ) =
        ⟨π.layer, π.Cs.hinges, fun x => cenS A.fam ξ (slotOfDart A.hS x),
          edgeS A.fam A.hS A.Cχ ξ, fun _ => 1, π.gapSpecification, freqS A.fam A.hS ξ, tt⟩ := rfl
    rw [h1, data_eq_asm π.Cs.hinges hh]
    unfold AsmCtx.D asmData
    rw [← hlay, ← hgs, ← htt]
  have hK : ∀ ξ : XiT A.fam, splicedKernel π.Gsb (π.data tt (fun x => cenS A.fam ξ (slotOfDart A.hS x))
      (edgeS A.fam A.hS A.Cχ ξ) (fun _ => 1) (freqS A.fam A.hS ξ)) P.L P.γ P.η P.δ base roots =
      splicedKernel π.Gsb (A.D ξ) A.L A.γ A.η A.δ A.base A.roots := by
    intro ξ
    rw [hD ξ, hL, hγ, hη, hδ, hbase, hroots]
  have hF : Summable fun ξ : XiT A.fam => ‖π.Gsb.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ *
      splicedKernel π.Gsb (π.data tt (fun x => cenS A.fam ξ (slotOfDart A.hS x))
        (edgeS A.fam A.hS A.Cχ ξ) (fun _ => 1) (freqS A.fam A.hS ξ)) P.L P.γ P.η P.δ base roots‖ := by
    simp_rw [hK]; exact hKs
  refine ⟨XiT A.fam, inferInstance,
    fun ξ => π.Gsb.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ,
    fun ξ x => cenS A.fam ξ (slotOfDart A.hS x), fun ξ => edgeS A.fam A.hS A.Cχ ξ, fun _ _ => 1,
    fun ξ => freqS A.fam A.hS ξ, hF, ?_, hw_sum, ?_, fun ξ => ?_⟩
  · rw [hv]
    exact tsum_congr fun ξ => by rw [hK]
  · have h1 : ENNReal.ofReal (∑' ξ : XiT A.fam, ‖π.Gsb.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖) =
        ∑' ξ : XiT A.fam, ENNReal.ofReal ‖π.Gsb.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ :=
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hw_sum
    have h2 : ∑' ξ : XiT A.fam, ENNReal.ofReal ‖π.Gsb.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ ≤
        ENNReal.ofReal B := by
      calc _ = ∑' ξ : XiT A.fam, ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ :=
            tsum_congr fun ξ => by rw [norm_mul, norm_zeta, one_mul]
        _ ≤ _ := A.tsum_constW_le
        _ ≤ _ := hmass
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 (h1 ▸ h2)
  · rw [hD ξ]; exact splicedAmplitudeBounds_asm A.fam A.hS A.hd A.Cχ A.hC A.hCpos A.layer0 A.gs A.tt ξ

end WaveTurbulence.GammaLow.Fama.Represents
