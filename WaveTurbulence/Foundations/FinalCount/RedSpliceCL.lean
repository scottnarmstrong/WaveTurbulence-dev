/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLCN
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSplit
public import WaveTurbulence.Foundations.FinalCount.RedSpliceIter
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
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole WaveTurbulence.Vine

variable {w : ℕ} {G : Garden w}

theorem parent_ne_self (v : GBranch G.tree) (h : v.1.2 ≠ []) : GNode.parent v.toNode h ≠ v := by
  intro heq
  have h1 := congrArg (fun u : GBranch G.tree => u.1.2.length) heq
  simp only [GNode.parent, GBranch.toNode] at h1
  have : v.1.2.dropLast.length < v.1.2.length := by
    rw [List.length_dropLast]
    have := List.length_pos_of_ne_nil h
    omega
  omega

theorem not_internalParent_of_inter {S T : Finset (GBranch G.tree)} {b : GBranch G.tree} (hi : S ∩ T = {b})
    (hS : InternalParent G S b) (hT : InternalParent G T b) : False := by
  obtain ⟨h, hp⟩ := hS
  obtain ⟨h', hp'⟩ := hT
  have : GNode.parent b.toNode h ∈ S ∩ T := mem_inter.mpr ⟨hp, hp'⟩
  rw [hi] at this
  exact parent_ne_self b h (mem_singleton.mp this)

theorem internalParent_mono {S T : Finset (GBranch G.tree)} (hST : S ⊆ T) {v : GBranch G.tree}
    (h : InternalParent G S v) : InternalParent G T v := ⟨h.1, hST h.2⟩

/-- A block chain all of whose ingredients are (CL) carries an internal parent at one of its end joints. -/
theorem chain_cl_end_parent (hM : G.molecule.IsMolecule) {L : Finset (GBranch G.tree)} {a x : GBranch G.tree}
    {m : ℕ} (h : Chain G.molecule L a x m)
    (hcl : ∀ A p q, ChainIngredient G.molecule L a x m A p q →
      CLParentPattern G A p q ∨ CLParentPattern G A q p)
    (hB : G.molecule.IsBlock L a x) : InternalParent G L a ∨ InternalParent G L x := by
  induction h with
  | @single S a b hv =>
    have hc := hcl S a b (.single hv)
    rcases hc with hc | hc
    · exact Or.inr hc.2
    · exact Or.inl hc.2
  | @append S T a b c n hS hT hi hne ih =>
    obtain ⟨X, hX⟩ := hT
    have hSB : G.molecule.IsBlock S a b := chain_prefix_isBlock G.molecule hM hS hX hi hB
    have hclS : ∀ A p q, ChainIngredient G.molecule S a b n A p q →
        CLParentPattern G A p q ∨ CLParentPattern G A q p := fun A p q hI =>
      hcl A p q (.append_left hI ⟨X, hX⟩ hi hne)
    have hT' : IsSomeVine G.molecule T b c := ⟨X, hX⟩
    have hclT := hcl T b c (.append_last hS hT' hi hne)
    rcases ih hclS hSB with hp | hp
    · exact Or.inl (internalParent_mono subset_union_left hp)
    · rcases hclT with hc | hc
      · exact Or.inr (internalParent_mono subset_union_right hc.2)
      · exact absurd (not_internalParent_of_inter hi hp hc.2) id


/-- A block chain of (CL) ingredients is a (CL) block, with joints `a, x` in one of the two orders. -/
theorem chain_clPattern (hM : G.molecule.IsMolecule) {L : Finset (GBranch G.tree)} {a x : GBranch G.tree}
    {m : ℕ} (h : Chain G.molecule L a x m)
    (hcl : ∀ A p q, ChainIngredient G.molecule L a x m A p q →
      CLParentPattern G A p q ∨ CLParentPattern G A q p)
    (hB : G.molecule.IsBlock L a x) :
    CLParentPattern G L a x ∨ CLParentPattern G L x a := by
  rcases block_parent_patterns G hB with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rcases chain_cl_end_parent hM h hcl hB with hp | hp
    · exact h1.1 hp
    · exact h1.2 hp

/-- The `CLBlock` of a (CL) pattern run. -/
@[expose] noncomputable def clBlockOfPattern {L : Finset (GBranch G.tree)} {a x : GBranch G.tree}
    (hB : G.molecule.IsBlock L a x) (hp : CLParentPattern G L a x ∨ CLParentPattern G L x a) : CLBlock G := by
  classical exact if h : CLParentPattern G L a x then ⟨L, a, x, hB, h⟩
  else ⟨L, x, a, block_swap_joints G.molecule hB, hp.resolve_left h⟩

end WaveTurbulence.RedSplice
