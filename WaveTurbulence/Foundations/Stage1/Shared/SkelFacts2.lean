/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.SkelFacts1
import Mathlib.Tactic

/-!
# SKEL-FACTS 2: the skeleton of a decoded irreducible garden has positive order unless `G` is a regular couple

A trivial prime skeleton (all trees leaves) that is irreducible has width `2`; then `G` is a couple (signature
`(+,-)`), and a couple has trivial prime skeleton exactly when it is regular (DH21 Proposition 4.13,
`couple_regular_iff_prime_skeleton_trivial`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Reg.Skeleton
open TTree WaveTurbulence.Comb

/-- An irreducible trivial garden of positive width has width `2`. -/
theorem IsTrivialGarden.width_eq_two {w : ℕ} {S : Garden w} (hT : IsTrivialGarden S) (hI : S.Irreducible)
    (hw : 1 ≤ w) : w = 2 := by
  classical
  let j0 : Fin w := ⟨0, hw⟩
  let A : Finset (Fin w) := {j0, hT.rootPartner j0}
  have hA : A = Finset.univ := by
    by_contra hne
    apply hI A ⟨j0, by simp [A]⟩ hne
    intro ℓ hℓ
    have hl : ℓ.1.1 ∈ A := (Finset.mem_filter.mp hℓ).2
    refine ⟨Comb.pair_ne_of_plain hT.1 ℓ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hp : (S.pair ℓ).1.1 = hT.rootPartner ℓ.1.1 := by
      have := hT.leaf_eq_rootLeaf ℓ
      conv_lhs => rw [this]
      rfl
    rw [hp]
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
    rcases hl with h | h
    · right; rw [h]
    · left; rw [h]; exact hT.rootPartner_involutive j0
  have hc : (Finset.univ : Finset (Fin w)).card ≤ 2 := by
    rw [← hA]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have h2 : (Finset.univ : Finset (Fin w)).card = w := by simp
  have : w ≤ 2 := h2 ▸ hc
  have hw2 : 2 ≤ w := by
    by_contra hlt
    have hw1 : w = 1 := by omega
    subst hw1
    exact hT.rootPartner_ne j0 (Subsingleton.elim _ _)
  omega

/-- `1 ≤ S.order` for the prime skeleton of an irreducible decoded garden which is not a regular couple. -/
theorem ReconstructionData.order_pos_of_decodes {R : ℕ} (hR : 1 ≤ R) {S G : Garden (2 * R)}
    (D : ReconstructionData S) (hP : IsPrimeGarden S) (hd : D.Decodes hP.1 G) (hG : G.Irreducible)
    (hsig : ∀ _ : 2 * R = 2, ∀ j, G.sig j = (-1) ^ (j : ℕ))
    (hnc : ∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ G)) : 1 ≤ S.order := by
  by_contra h0
  have h0 : S.order = 0 := by omega
  have hleaf : ∀ j, S.tree j = .leaf := by
    intro j
    have hj : (S.tree j).order = 0 :=
      (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_univ j)
    cases ht : S.tree j with
    | leaf => rfl
    | node l m r => rw [ht] at hj; simp [TTree.order] at hj
  have hT : IsTrivialGarden S := ⟨hP.1, hleaf⟩
  have hI := D.irreducible_of_decodes hP.1 hd hG
  have h2 : 2 * R = 2 := by have := hT.width_eq_two hI (by omega); omega
  obtain rfl : R = 1 := by omega
  have hrec : Reconstructs (rawOfGarden S) (rawOfGarden G) :=
    (reconstructs_iff_exists_reconstructionData S G hP.1 hd.1).mpr ⟨D, hd⟩
  have hcpl : IsCouple (G : Garden 2) := by
    refine ⟨hd.1, ?_⟩
    funext j
    rw [hsig rfl j]
    fin_cases j <;> rfl
  exact hnc rfl ((couple_regular_iff_prime_skeleton_trivial G S hcpl hP hrec).mpr hT)

end WaveTurbulence.Reg.Skeleton
