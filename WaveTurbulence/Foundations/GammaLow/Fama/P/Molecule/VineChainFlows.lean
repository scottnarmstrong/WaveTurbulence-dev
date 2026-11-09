/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Molecule.VineChainFlows` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.Molecule.VineJointFlows
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts


/-! # All ingredient gaps equal the source chain gap up to orientation -/

public section
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount
variable {V D E : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
    [AddCommGroup E] [Module ℝ E]



/-- TARGET defdiff/subsetvc: every ordered ingredient in an actual chain
has initial flow equal to the initial chain flow, and final flow its negative.
Only source conservation at degree-four atoms is assumed. -/
theorem chainIngredient_flow_eq (M : Molecule V D) (hM : M.IsMolecule)
    (k : D → E) (hk : ∀ d,k (M.mate d)=k d)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ d ∈ M.dartsAt v,M.dartSign d • k d=0)
    {U A : Finset V} {a b x y : V} {n : ℕ} (h : ChainIngredientG γ M U a b n A x y) :
    M.IsBlock U a b →
      groupFlow M A k x=groupFlow M U k a ∧ groupFlow M A k y=-groupFlow M U k a := by
  induction h with
  | single _h =>
    intro hU
    exact ⟨rfl,by rw [block_jointFlow_neg M hM hU k hk hc,neg_neg]⟩
  | @append_left S T A a b c x y n hI hT hi _hne ih =>
    intro hU
    have hX := hT
    have hS := chain_prefix_isBlock M hM (chainIngredientG_spec hI).1 hX hi hU
    have he := nested_groupFlow_eq M (show S ⊆ S ∪ T from Finset.subset_union_left) a
      ((Mole.block_joint_degrees M hS).1.trans (Mole.block_joint_degrees M hU).1.symm) k
    obtain ⟨hl,hr⟩ := ih hS
    exact ⟨hl.trans he,hr.trans (congrArg Neg.neg he)⟩
  | append_last _hS hT _hi _hne =>
    intro hU
    have hX := hT
    have he := terminal_block_initialFlow M hM (Src.isBlock_of_isSomeVine hX) hU Finset.subset_union_right k hk hc
    exact ⟨he,by rw [← he,block_jointFlow_neg M hM (Src.isBlock_of_isSomeVine hX) k hk hc,neg_neg]⟩

end WaveTurbulence.GammaLow.Fama
