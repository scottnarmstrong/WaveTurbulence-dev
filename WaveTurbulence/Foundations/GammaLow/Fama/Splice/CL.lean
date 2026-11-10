/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceCL` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module

public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.FinalCount.RedSpliceCL
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): a run of (CL) vines is a (CL) block

TARGET `blockchainprop` (DH23 Cor 4.13): if a block chain has only (CL) ingredients then its parent pattern is
(CL).  Proof: the end joint of the last ingredient carries the parent, because a shared joint cannot have its
parent in both ingredients (their intersection is the joint itself, and a parent is a different atom).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ}

/-- A block chain all of whose ingredients are (CL) carries an internal parent at one of its end joints. -/
theorem chain_cl_end_parent (hM : G.molecule.IsMolecule) {L : Finset (GBranch G.tree)} {a x : GBranch G.tree}
    {m : ℕ} (h : Src.Chain γ G.molecule L a x m)
    (hcl : ∀ A p q, ChainIngredientG γ G.molecule L a x m A p q →
      CLParentPattern G A p q ∨ CLParentPattern G A q p)
    (hB : G.molecule.IsBlock L a x) : InternalParent G L a ∨ InternalParent G L x := by
  induction h with
  | @single S a b hv =>
    have hc := hcl S a b (.single hv)
    rcases hc with hc | hc
    · exact Or.inr hc.2
    · exact Or.inl hc.2
  | @append S T a b c n hS hT hi hne ih =>
    have hSB : G.molecule.IsBlock S a b := chain_prefix_isBlock G.molecule hM hS hT hi hB
    have hclS : ∀ A p q, ChainIngredientG γ G.molecule S a b n A p q →
        CLParentPattern G A p q ∨ CLParentPattern G A q p := fun A p q hI =>
      hcl A p q (.append_left hI hT hi hne)
    have hclT := hcl T b c (.append_last hS hT hi hne)
    rcases ih hclS hSB with hp | hp
    · exact Or.inl (RedSplice.internalParent_mono subset_union_left hp)
    · rcases hclT with hc | hc
      · exact Or.inr (RedSplice.internalParent_mono subset_union_right hc.2)
      · exact absurd (RedSplice.not_internalParent_of_inter hi hp hc.2) id


end WaveTurbulence.GammaLow.Fama
