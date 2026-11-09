/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.Slots3` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots2
public import WaveTurbulence.Foundations.LayerCnt.BondExp
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.Slots3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Slots


/-!
# CLASSCOUNT: the slot distances are the bond exponent of the skeleton molecule

`Σ_s slotDist` (the `2^{|q-q'|}` factors of `layerreg2`) is at most `bondExp M(S) f` plus `p` for each root
(trees at root branches and couples with a root leaf have parent layer `p` and no bond).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree LayerCnt WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

variable {S : Garden w}

open Classical in
open Classical in
/-- **B1 class bound.**  Layered gardens decoded by `D` with common slot incoherencies `gs`:
`#A ≤ (2^{9p})^{Σ gs} 2^{|D|} 2^{p w} Σ_f 2^{bondExp M(S) f}` over the core layerings `f` of `A`. -/
theorem card_class_le_bond (D : ReconstructionData S) (hS : S.IsPlain) (p : ℕ) (gs : ReplacementSlot S → ℕ)
    (A : Finset (LayeredGarden w))
    (hA : ∀ LG ∈ A, LG.CanonCriterion p ∧ LG.garden.IsPlain ∧ D.Decodes hS LG.garden ∧
      ∀ s, slotInc D hS LG s = gs s) :
    (A.card : ℝ) ≤ (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size * 2 ^ (p * rootThings hS) *
      ∑ f ∈ A.image (coreOf D hS), (2 : ℝ) ^ bondExp S.molecule Finset.univ f := by
  classical
  refine (card_class_le D hS p gs A hA).trans ?_
  have : ∀ f ∈ A.image (coreOf D hS), (2 : ℝ) ^ (∑ s, slotDist hS p f s) ≤
      2 ^ (p * rootThings hS) * (2 : ℝ) ^ bondExp S.molecule Finset.univ f := by
    intro f hf
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨hc, hpl, hd, -⟩ := hA LG hLG
    have hle : ∀ b, coreOf D hS LG b ≤ p := by
      intro b; rw [coreOf_eq D hS hd]; exact hc.1 _
    have := slotDist_sum_le hS p (coreOf D hS LG) hle
    calc (2 : ℝ) ^ (∑ s, slotDist hS p (coreOf D hS LG) s) ≤ 2 ^ (bondExp S.molecule Finset.univ (coreOf D hS LG) + p * rootThings hS) :=
          pow_le_pow_right₀ (by norm_num) this
      _ = _ := by rw [pow_add]; ring
  calc (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size * ∑ f ∈ A.image (coreOf D hS), (2 : ℝ) ^ (∑ s, slotDist hS p f s)
      ≤ (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size * ∑ f ∈ A.image (coreOf D hS),
          (2 ^ (p * rootThings hS) * (2 : ℝ) ^ bondExp S.molecule Finset.univ f) := by
        gcongr with f hf
        exact this f hf
    _ = _ := by rw [← Finset.mul_sum]; ring

end WaveTurbulence.GammaLow.Famc.ClassCount
