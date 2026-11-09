/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepH13` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Represents.RepH12
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
public import WaveTurbulence.Foundations.Stage1.Represents.RepH13
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
# S2 REPRESENTS, VINE-D (13): `RepIntC` of a vine piece from the assembly with vine factors

`splicedKernel_congr_data`: the spliced kernel depends on the data only through the layers, hinges, edge amplitudes,
gap specification, frequencies, root times and the values of the hinge amplitude at bond momenta (the centres do not
enter).  `repIntC_of_asmH`: for a Stage 1 piece `π` whose spliced garden, hinges, layering and gap specification are those
of the assembly context `A`, the outer form (`value_eqH`'s left-hand side) has a countable superposition by spliced
kernels of `π` with total weight at most `B` whenever the explicit mass bound is `≤ B`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal WaveTurbulence.GammaLow.FinalCount

variable {w d : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]


open scoped Classical in
theorem repIntC_of_asmH {P : WTParams} {R : ℕ} (π : Stage1PieceG P R) (A : AsmCtxH π.Gsb P.d)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hh : A.hinges = π.Cs.hinges) (hlay : A.layer0 = π.layer) (hgs : A.gs = π.gapSpecification)
    (hL : A.L = P.L) (hγ : A.γ = P.γ) (hη : A.η = P.η) (hδ : A.δ = P.δ)
    (hbase : A.base = base) (hroots : A.roots = roots) (htt : A.tt = tt)
    (B : ℝ) (hB : 0 ≤ B)
    (hmass : ENNReal.ofReal (A.Cχ ^ Fintype.card (GBranch π.Gsb.tree)) *
      ((∏ s, ∑' l, ENNReal.ofReal (A.fam.w s l)) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ≥0∞)) * ∏ j, ENNReal.ofReal (A.Mh j) ≤
        ENNReal.ofReal B)
    (val : ℂ)
    (hval : val = (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0,
        (if A.selSk κ then ((splicedEpsilon π.Gsb A.hinges κ.1 : ℝ) : ℂ) else 0) *
          ∫ τ, (splicedTimeDomain π.Gsb A.layer0 A.tt).indicator (fun τ =>
            phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ) :
    RepIntC π tt base roots val B := by
  have hv := A.value_eqH
  rw [← hval] at hv
  -- the transported data of an assembled mode
  let toP : HingeDarts π.Gsb A.hinges → HingeDarts π.Gsb π.Cs.hinges := fun x => ⟨x.1, by rw [← hh]; exact x.2⟩
  let toA : HingeDarts π.Gsb π.Cs.hinges → HingeDarts π.Gsb A.hinges := fun x => ⟨x.1, by rw [hh]; exact x.2⟩
  let hingeT : A.Xi → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ :=
    fun ξh K => A.hingeAmp ξh (fun x => K (toP x))
  have hK : ∀ ξh : A.Xi, splicedKernel π.Gsb (π.data tt (fun x => cenS A.fam ξh.1 (slotOfDart A.hS x))
      (edgeS A.fam A.hS A.Cχ ξh.1) (hingeT ξh) (A.freqH ξh)) P.L P.γ P.η P.δ base roots =
      splicedKernel π.Gsb (A.DH ξh) A.L A.γ A.η A.δ A.base A.roots := by
    intro ξh
    rw [hL, hγ, hη, hδ, hbase, hroots]
    refine splicedKernel_congr_data π.Gsb _ _ _ _ _ _ _ _ hlay.symm hh.symm rfl hgs.symm rfl htt.symm
      fun k => rfl
  -- summability of the weights
  have hw_sum : Summable fun ξh : A.Xi => ‖π.Gsb.zeta * A.constWH ξh‖ := by
    have h1 : ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top A.toAsmCtx.mass_ne_top (by simp)))
        (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)) A.tsum_norm_constWH_le
    refine (ENNReal.summable_toReal h1).congr fun ξh => ?_
    rw [norm_mul, norm_zeta, one_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  -- summability of the values
  have hdbl := (sum_integral_sum_swap (volume : Measure (GBranch π.Gsb.tree → ℝ)) A.gIH
    A.meas_gIH A.sum_lintegral_gIH_ne_top).2
  have hKs : Summable fun ξh : A.Xi => ‖π.Gsb.zeta * A.constWH ξh *
      splicedKernel π.Gsb (A.DH ξh) A.L A.γ A.η A.δ A.base A.roots‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξh => ?_)
      (hdbl.prod.mul_left (‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖))
    calc ‖π.Gsb.zeta * A.constWH ξh * splicedKernel π.Gsb (A.DH ξh) A.L A.γ A.η A.δ A.base A.roots‖
        = ‖A.constWH ξh * splicedKernel π.Gsb (A.DH ξh) A.L A.γ A.η A.δ A.base A.roots‖ := by
          rw [mul_assoc, norm_mul, norm_zeta, one_mul]
      _ = ‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖ *
          ‖∑' κ : GenDecoration π.Gsb P.d A.roots 0, ∫ τ, A.gIH ξh κ τ‖ := by
          rw [← A.tsum_int_gIH ξh, norm_mul]
      _ ≤ ‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖ *
          ∑' κ : GenDecoration π.Gsb P.d A.roots 0, ‖∫ τ, A.gIH ξh κ τ‖ := by
          gcongr
          exact norm_tsum_le_tsum_norm (hdbl.prod_factor ξh)
  refine ⟨A.Xi, inferInstance, fun ξh => π.Gsb.zeta * A.constWH ξh,
    fun ξh x => cenS A.fam ξh.1 (slotOfDart A.hS x), fun ξh => edgeS A.fam A.hS A.Cχ ξh.1, hingeT,
    fun ξh => A.freqH ξh, ?_, ?_, hw_sum, ?_, fun ξh => ?_⟩
  · simp_rw [hK]; exact hKs
  · rw [hv]
    exact tsum_congr fun ξh => by rw [hK]
  · have h1 : ENNReal.ofReal (∑' ξh : A.Xi, ‖π.Gsb.zeta * A.constWH ξh‖) =
        ∑' ξh : A.Xi, ENNReal.ofReal ‖π.Gsb.zeta * A.constWH ξh‖ :=
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hw_sum
    have h2 : ∑' ξh : A.Xi, ENNReal.ofReal ‖π.Gsb.zeta * A.constWH ξh‖ ≤ ENNReal.ofReal B := by
      calc _ = ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ :=
            tsum_congr fun ξh => by rw [norm_mul, norm_zeta, one_mul]
        _ ≤ _ := A.tsum_norm_constWH_le
        _ ≤ _ := hmass
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 (h1 ▸ h2)
  · -- amplitude bounds of the transported data
    have hb := A.splicedAmplitudeBounds_DH ξh
    refine ⟨hb.1, hb.2.1, fun K => A.norm_hingeAmp_le ξh _, fun K ⟨x, hx⟩ => ?_⟩
    exact hb.2.2.2 (fun y => K (toP y)) ⟨toA x, hx⟩

end WaveTurbulence.GammaLow.Fama.Represents
