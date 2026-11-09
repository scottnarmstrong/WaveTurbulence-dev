/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitCL` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.Molecule.BlockTypes
public import WaveTurbulence.Foundations.Molecule.BlockParent
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitCL
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: every ingredient of a (CL) vine Fama.chain is a (CL) vine, oriented from the upper to the lower joint

`ing_cl`: if `U` is a Fama.chain with `CLParentPattern G U a b` then each ingredient `A` with joints `x, y` (in Fama.chain order)
has `CLParentPattern G A x y`.  The proof peels off the last vine `T` (joints `b, c`): the parent of `c` lies in `T`
(`group_split` on the parent dart), so `block_parent_patterns` leaves only the pattern `CL(b, c)`; then the parent of the
joint `b` is not in `T`, hence in `S`, which gives `CL(S, a, b)` for the induction hypothesis.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]


theorem cl_split (hM : G.molecule.IsMolecule) {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hU : G.molecule.IsBlock (S ∪ T) a c)
    (hi : S ∩ T = {b}) (hbc : b ≠ c) (hCL : CLParentPattern G (S ∪ T) a c) :
    CLParentPattern G T b c ∧ CLParentPattern G S a b := by
  have hcT := intPar_of_union hM hS hT hU hi hbc hCL.2
  have hTCL : CLParentPattern G T b c := by
    rcases block_parent_patterns G hT with h | h | h
    · exact h
    · exact absurd hcT h.1
    · exact absurd hcT h.2
  refine ⟨hTCL, ?_, ?_⟩
  · intro hpa
    exact hCL.1 ⟨hpa.1, Finset.mem_union_left _ hpa.2⟩
  · have hab : a ≠ b := hS.2.2.2.1
    have hbS : b ∈ S := hS.2.2.1
    have hdU : G.molecule.degIn (S ∪ T) b = 4 :=
      hU.2.2.2.2.2.2.2.2.1 b (Finset.mem_union_left _ hbS) hab.symm hbc
    obtain ⟨hne, hp⟩ := full_internal_has_parent G hdU
    refine ⟨hne, ?_⟩
    rcases Finset.mem_union.mp hp with h | h
    · exact h
    · exact absurd ⟨hne, h⟩ hTCL.1

/-- **Every ingredient of a (CL) Fama.chain is (CL), oriented in the Fama.chain order.** -/
theorem ing_cl (hM : G.molecule.IsMolecule) {U A : Finset (GBranch G.tree)} {a b x y : GBranch G.tree} {n : ℕ}
    (h : ChainIngredientG γ G.molecule U a b n A x y) :
    G.molecule.IsBlock U a b → CLParentPattern G U a b → CLParentPattern G A x y := by
  induction h with
  | single hv => intro _ hCL; exact hCL
  | @append_left S T A a b c x y n hI hT hi hne ih =>
    intro hU hCL
    have hY := hT
    have hSpec := chainIngredientG_spec hI
    have hBS := chain_prefix_isBlock G.molecule hM hSpec.1 hY hi hU
    have hbc : b ≠ c := (Src.isBlock_of_isSomeVine hY).2.2.2.1
    exact ih hBS (cl_split hM hBS (Src.isBlock_of_isSomeVine hY) hU hi hbc hCL).2
  | @append_last S T a b c n hS hT hi hne =>
    intro hU hCL
    have hY := hT
    have hBS := chain_prefix_isBlock G.molecule hM hS hY hi hU
    have hbc : b ≠ c := (Src.isBlock_of_isSomeVine hY).2.2.2.1
    exact (cl_split hM hBS (Src.isBlock_of_isSomeVine hY) hU hi hbc hCL).1

end WaveTurbulence.GammaLow.Famc.ClassCount
