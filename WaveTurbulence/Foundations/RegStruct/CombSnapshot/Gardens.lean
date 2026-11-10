/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Structure

/-! # Pair cancellation and signature balance (TARGET L632–L643) -/

public section

namespace WaveTurbulence.Comb
open TTree Finset

variable {w : ℕ} {G : Garden w}

/-- On unmarked leaves the pairing has no fixed points (TARGET L632). -/
theorem pair_ne_of_unmarked {ℓ : GLeaf G.tree} (h : G.mark ℓ = none) : G.pair ℓ ≠ ℓ :=
  fun he => ((G.pair_eq_iff ℓ).mp he) h

/-- Every plain garden has a fixed-point-free pairing. -/
theorem pair_ne_of_plain (h : G.IsPlain) (ℓ : GLeaf G.tree) : G.pair ℓ ≠ ℓ :=
  pair_ne_of_unmarked (h ℓ)

/-- A completely paired finite set has cancellation of every paired-constant labelling. -/
theorem sum_signed_completelyPaired {V : Type*} [AddCommGroup V]
    {S : Finset (GLeaf G.tree)} (hS : G.CompletelyPaired S)
    (κ : GNode G.tree → V) (hp : ∀ ℓ, κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    ∑ ℓ ∈ S, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • κ ℓ.toNode = 0 := by
  classical
  refine Finset.sum_involution (fun ℓ _ => G.pair ℓ) (fun ℓ hℓ => ?_)
    (fun ℓ hℓ _ => (hS ℓ hℓ).1) (fun ℓ hℓ => (hS ℓ hℓ).2) (fun ℓ _ => G.pair_pair ℓ)
  rw [G.pair_sign ℓ (hS ℓ hℓ).1, ← hp ℓ, Units.val_neg, neg_smul, add_neg_cancel]

/-- All leaves of a plain garden are completely paired. -/
theorem completelyPaired_univ (h : G.IsPlain) : G.CompletelyPaired Finset.univ :=
  fun ℓ _ => ⟨pair_ne_of_plain h ℓ, Finset.mem_univ _⟩

/-- The leaf sets of the roots partition all leaves, so the signed root sum
is the signed leaf sum (TARGET L641–L643). -/
theorem sum_roots_eq_sum_leaves {V : Type*} [AddCommGroup V]
    (κ : GNode G.tree → V)
    (hκ : ∀ b : GBranch G.tree, κ b.toNode = κ (b.child 0) - κ (b.child 1) + κ (b.child 2)) :
    ∑ j, ((G.sig j : ℤˣ) : ℤ) • κ (GNode.root G.tree j) =
      ∑ ℓ : GLeaf G.tree, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • κ ℓ.toNode := by
  classical
  have hr : ∀ j, ((G.sig j : ℤˣ) : ℤ) • κ (GNode.root G.tree j) =
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ : GLeaf G.tree => ℓ.1.1 = j),
        ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • κ ℓ.toNode := by
    intro j
    have h := sum_rule G.sig κ hκ (GNode.root G.tree j)
    simpa [nodeSign, GNode.root, pathSign, GNode.leavesBelow, GNode.IsDesc, GLeaf.toNode, eq_comm] using h
  simp_rw [hr]
  exact Finset.sum_fiberwise Finset.univ (fun ℓ : GLeaf G.tree => ℓ.1.1) _

/-- The signed root values of a plain garden sum to zero (TARGET L643). -/
theorem sum_signed_roots_eq_zero (hG : G.IsPlain) {V : Type*} [AddCommGroup V]
    {κ : GNode G.tree → V} (hκ : IsDecoration G κ) :
    ∑ j, ((G.sig j : ℤˣ) : ℤ) • κ (GNode.root G.tree j) = 0 := by
  rw [sum_roots_eq_sum_leaves κ hκ.1]
  exact sum_signed_completelyPaired (completelyPaired_univ hG) κ hκ.2

/-- Equal numbers of positive and negative root signs are forced by pairing (TARGET L632). -/
theorem balanced_of_plain (hG : G.IsPlain) : G.IsBalanced := by
  have hκ : IsDecoration G (fun _ => (1 : ℤ)) := ⟨fun _ => by norm_num, fun _ => rfl⟩
  have h := sum_signed_roots_eq_zero hG hκ
  simpa only [Garden.IsBalanced, smul_eq_mul, mul_one] using h

/-- A decoration is determined by its leaf values (TARGET L641). -/
theorem decoration_ext {V : Type*} [AddCommGroup V]
    {κ κ' : GNode G.tree → V} (hκ : IsDecoration G κ) (hκ' : IsDecoration G κ')
    (h : ∀ ℓ : GLeaf G.tree, κ ℓ.toNode = κ' ℓ.toNode) : κ = κ' := by
  funext a
  apply sub_eq_zero.mp
  apply eq_zero_of_leaves_zero (fun a => κ a - κ' a) (a := a)
  · intro b
    rw [hκ.1 b, hκ'.1 b]
    abel
  · intro ℓ _
    exact sub_eq_zero.mpr (h ℓ)

end WaveTurbulence.Comb
