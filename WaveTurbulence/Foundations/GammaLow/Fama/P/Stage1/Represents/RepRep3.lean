/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepRep3` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepRep1
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep3
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
# S2 REPRESENTS: closure properties of the count-measure representation `RepIntC`

Zero, scalar multiples by `|c| ≤ 1`, binary and finite sums, and monotonicity in the mass bound.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine MeasureTheory WaveTurbulence.GammaLow.FinalCount
open scoped ENNReal WaveTurbulence.GammaLow.FinalCount

variable {P : WTParams} {R : ℕ} {π : Stage1PieceG P R} {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
  {roots : Fin (2 * R) → (Fin P.d → ℤ)}

theorem RepIntC.mono {val : ℂ} {B B' : ℝ} (h : RepIntC π tt base roots val B) (hB : B ≤ B') :
    RepIntC π tt base roots val B' := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4.trans hB, h5⟩

theorem RepIntC.zero {B : ℝ} (hB : 0 ≤ B) : RepIntC π tt base roots 0 B := by
  refine ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, ?_, ?_, ?_, ?_, fun e => e.elim⟩
  · exact (hasSum_fintype _).summable
  · simp
  · exact (hasSum_fintype _).summable
  · simpa using hB

theorem RepIntC.smul {val : ℂ} {B : ℝ} (h : RepIntC π tt base roots val B) (c : ℂ) :
    RepIntC π tt base roots (c * val) (‖c‖ * B) := by
  obtain ⟨Ξ, hcnt, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hcnt, fun ξ => c * w ξ, ctr, edge, hinge, freq, ?_, ?_, ?_, ?_, h5⟩
  · simp_rw [mul_assoc]
    refine (h1.mul_left ‖c‖).congr fun ξ => ?_
    simp only [norm_mul]
  · rw [h2, ← tsum_mul_left]; exact tsum_congr fun ξ => by ring
  · simp_rw [norm_mul]; exact h3.mul_left _
  · simp_rw [norm_mul]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)

theorem RepIntC.add {v₁ v₂ : ℂ} {B₁ B₂ : ℝ} (h₁ : RepIntC π tt base roots v₁ B₁)
    (h₂ : RepIntC π tt base roots v₂ B₂) : RepIntC π tt base roots (v₁ + v₂) (B₁ + B₂) := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, a1, a2, a3, a4, a5⟩ := h₁
  obtain ⟨Ξ', hc', w', ctr', edge', hinge', freq', b1, b2, b3, b4, b5⟩ := h₂
  refine ⟨Ξ ⊕ Ξ', inferInstance, Sum.elim w w', Sum.elim ctr ctr', Sum.elim edge edge',
    Sum.elim hinge hinge', Sum.elim freq freq', ?_, ?_, ?_, ?_, ?_⟩
  · refine Summable.sum _ ?_ ?_
    · exact a1
    · exact b1
  · rw [Summable.tsum_sum (f := fun ξ => (Sum.elim w w' ξ) * splicedKernel π.Gsb
      (π.data tt (Sum.elim ctr ctr' ξ) (Sum.elim edge edge' ξ) (Sum.elim hinge hinge' ξ)
        (Sum.elim freq freq' ξ)) P.L P.γ P.η P.δ base roots) a1.of_norm b1.of_norm]
    rw [a2, b2]; rfl
  · refine Summable.sum _ ?_ ?_
    · exact a3
    · exact b3
  · rw [Summable.tsum_sum (f := fun ξ => ‖Sum.elim w w' ξ‖) a3 b3]
    exact add_le_add a4 b4
  · rintro (ξ | ξ)
    · exact a5 ξ
    · exact b5 ξ

theorem RepIntC.finset_sum {ι : Type*} (s : Finset ι) (val : ι → ℂ) (B : ι → ℝ) (hB : ∀ i ∈ s, 0 ≤ B i)
    (h : ∀ i ∈ s, RepIntC π tt base roots (val i) (B i)) :
    RepIntC π tt base roots (∑ i ∈ s, val i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RepIntC.zero (π := π) (tt := tt) (base := base) (roots := roots) le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hB i (Finset.mem_insert_of_mem hi)) (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end WaveTurbulence.GammaLow.Fama.Represents
