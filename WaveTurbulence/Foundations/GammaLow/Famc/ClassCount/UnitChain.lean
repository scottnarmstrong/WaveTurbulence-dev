/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitChain` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.FinalCount.S1Erase
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# CLASSCOUNT: every unit is a vine chain of the molecule of the skeleton

`unit_chain`: for `u ∈ unitBlocks γ G σ` there is `n` with `Src.Chain γ G.molecule u.atoms u.upper u.lower n`.  The runs of a skip
decomposition live in the molecule with the deleted bond `e` of an HVC; the bond `e` is not inside a run, so chains and
blocks of the erased molecule are chains and blocks of `M` (converse of `S1Erase.chain_eraseBond`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem isBlock_of_eraseBond {S : Finset V} {a b : V} (e : D) (hB : (Molecule.eraseBond M e).IsBlock S a b)
    (he : ¬ M.InGroup S e) : M.IsBlock S a b := by
  obtain ⟨hS, ha, hb, hne, ho1, hi1, ho2, hi2, hint, hconn⟩ := hB
  have hdeg : ∀ v, (Molecule.eraseBond M e).degIn S v = M.degIn S v := by
    intro v
    have h1 : (Molecule.eraseBond M e).degIn S v =
        (((M.dartsAt v).filter (M.InGroup S)) \ {e, M.mate e}).card :=
      Mole.eraseBond_degIn M e S v
    rw [h1]
    unfold Molecule.degIn
    congr 1
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    rw [Finset.disjoint_right]
    intro x hx hxv
    have hxg := (Finset.mem_filter.mp hxv).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact he hxg
    · exact he (by simpa only [M.mate_mate] using inGroup_mate' hxg)
  have hori : ∀ v (c : Bool), (((Molecule.eraseBond M e).dartsAt v).filter
      (fun x => (Molecule.eraseBond M e).InGroup S x ∧ (Molecule.eraseBond M e).out x = c)).card =
      ((M.dartsAt v).filter (fun x => M.InGroup S x ∧ M.out x = c)).card :=
    fun v c => Mole.eraseBond_orientedIn M e S v c he
  refine ⟨hS, ha, hb, hne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hori a true).symm.trans ho1
  · exact (hori a false).symm.trans (by
      have := hi1
      unfold Molecule.inIn at this
      simpa using this)
  · exact (hori b true).symm.trans ho2
  · exact (hori b false).symm.trans (by
      have := hi2
      unfold Molecule.inIn at this
      simpa using this)
  · intro v hv h1 h2
    exact (hdeg v).symm.trans (hint v hv h1 h2)
  · intro u hu v hv
    refine Relation.EqvGen.mono ?_ u v (hconn u hu v hv)
    rintro p q ⟨x, hx, hxp, hxq⟩
    exact ⟨x.1, hx, hxp, hxq⟩

theorem chain_of_eraseBond {S : Finset V} {a b : V} {n : ℕ} (e : D)
    (h : Src.Chain γ (Molecule.eraseBond M e) S a b n) (he : ¬ M.InGroup S e) : Src.Chain γ M S a b n := by
  induction h with
  | single hv =>
    exact Src.Chain.single (isSomeVine_of_eraseBond e hv he)
  | @append S' T a b c n hS hT hi hne ih =>
    refine Src.Chain.append (ih (fun h' => he (inGroup_mono subset_union_left h'))) (isSomeVine_of_eraseBond e hT
      (fun h' => he (inGroup_mono subset_union_right h'))) hi hne

end WaveTurbulence.GammaLow.Famc.ClassCount
