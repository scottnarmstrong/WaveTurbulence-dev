/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineChainFlows`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # All ingredient gaps equal the source chain gap up to orientation -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [AddCommGroup E] [Module ℝ E]

/-- TARGET defdiff/subsetvc: every ordered ingredient in an actual chain
has initial flow equal to the initial chain flow, and final flow its negative.
Only source conservation at degree-four atoms is assumed. -/
theorem chainIngredient_flow_eq (M : Molecule V D) (hM : M.IsMolecule)
    (k : D → E) (hk : ∀ d,k (M.mate d)=k d)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ d ∈ M.dartsAt v,M.dartSign d • k d=0)
    {U A : Finset V} {a b x y : V} {n : ℕ} (h : ChainIngredient M U a b n A x y) :
    M.IsBlock U a b →
      groupFlow M A k x=groupFlow M U k a ∧ groupFlow M A k y=-groupFlow M U k a := by
  induction h with
  | single _h =>
    intro hU
    exact ⟨rfl,by rw [block_jointFlow_neg M hM hU k hk hc,neg_neg]⟩
  | @append_left S T A a b c x y n hI hT hi _hne ih =>
    intro hU
    have hX := hT
    have hS := chain_prefix_isBlock M hM (chainIngredient_spec hI).1 hX hi hU
    have he := nested_groupFlow_eq M (show S ⊆ S ∪ T from Finset.subset_union_left) a
      ((Mole.block_joint_degrees M hS).1.trans (Mole.block_joint_degrees M hU).1.symm) k
    obtain ⟨hl,hr⟩ := ih hS
    exact ⟨hl.trans he,hr.trans (congrArg Neg.neg he)⟩
  | append_last _hS hT _hi _hne =>
    intro hU
    have hX := hT
    have he := terminal_block_initialFlow M hM hX.block hU Finset.subset_union_right k hk hc
    exact ⟨he,by rw [← he,block_jointFlow_neg M hM hX.block k hk hc,neg_neg]⟩

end WaveTurbulence.GammaLow.FinalCount.H
