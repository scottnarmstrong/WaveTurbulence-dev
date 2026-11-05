/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.Molecule.VineJointFlows
import Mathlib.Tactic

/-! # All ingredient gaps equal the source chain gap up to orientation -/

public section
namespace WaveTurbulence.Vine
variable {V D E : Type*} [DecidableEq V] [Fintype D]
    [AddCommGroup E] [Module ℝ E]

/-- Equal nested degrees identify the actual signed internal dart flows. -/
theorem nested_groupFlow_eq (M : Molecule V D) {S U : Finset V} (hSU : S ⊆ U)
    (v : V) (hd : M.degIn S v=M.degIn U v) (k : D → E) :
    groupFlow M S k v=groupFlow M U k v := by
  unfold groupFlow
  rw [internal_darts_eq_of_nested_degree M hSU v hd]

/-- A terminal block has the same initial signed gap as its containing
block when full-degree atoms conserve momentum. -/
theorem terminal_block_initialFlow (M : Molecule V D) (hM : M.IsMolecule)
    {T U : Finset V} {a b c : V} (hT : M.IsBlock T b c) (hU : M.IsBlock U a c)
    (hTU : T ⊆ U) (k : D → E) (hk : ∀ d,k (M.mate d)=k d)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ d ∈ M.dartsAt v,M.dartSign d • k d=0) :
    groupFlow M T k b=groupFlow M U k a := by
  have he := nested_groupFlow_eq M hTU c
    ((Mole.block_joint_degrees M hT).2.trans (Mole.block_joint_degrees M hU).2.symm) k
  have ht := block_jointFlow_neg M hM hT k hk hc
  have hu := block_jointFlow_neg M hM hU k hk hc
  exact ht.trans ((congrArg Neg.neg he).trans hu.symm)

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
    obtain ⟨X,hX⟩ := hT
    have hS := chain_prefix_isBlock M hM (chainIngredient_spec hI).1 hX hi hU
    have he := nested_groupFlow_eq M (show S ⊆ S ∪ T from Finset.subset_union_left) a
      ((Mole.block_joint_degrees M hS).1.trans (Mole.block_joint_degrees M hU).1.symm) k
    obtain ⟨hl,hr⟩ := ih hS
    exact ⟨hl.trans he,hr.trans (congrArg Neg.neg he)⟩
  | append_last _hS hT _hi _hne =>
    intro hU
    obtain ⟨X,hX⟩ := hT
    have he := terminal_block_initialFlow M hM hX.1 hU Finset.subset_union_right k hk hc
    exact ⟨he,by rw [← he,block_jointFlow_neg M hM hX.1 k hk hc,neg_neg]⟩

end WaveTurbulence.Vine
