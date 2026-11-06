/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootModifiedProfiles
public import WaveTurbulence.Foundations.Spine.RootWeightCount
/-! The exact root-weight expansion has C^width times geometric-in-order many terms. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def rootLeafSlotsEquiv {w : ℕ} (G : Garden w) (j : Fin w) :
    RootLeafSlots G j ≃ {p : TTree.Path // p ∈ (G.tree j).leaves} where
  toFun l := ⟨l.1.1.2, by
    have hm : l.1 ∈ (GNode.root G.tree j).leavesBelow := l.2
    have hr : (GNode.root G.tree j).IsDesc l.1.toNode := (mem_filter.mp hm).2
    have hleaf := l.1.2
    have hj : j = l.1.1.1 := hr.1
    rw [← hj] at hleaf
    exact hleaf⟩
  invFun p := ⟨⟨(j, p.1), p.2⟩, mem_filter.mpr ⟨mem_univ _, rfl, List.nil_prefix⟩⟩
  left_inv l := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hm : l.1 ∈ (GNode.root G.tree j).leavesBelow := l.2
      exact (mem_filter.mp hm).2.1
    · rfl
  right_inv _ := rfl

theorem card_rootLeafSlots {w : ℕ} (G : Garden w) (j : Fin w) :
    Fintype.card (RootLeafSlots G j) = 2 * (G.tree j).order + 1 := by
  rw [Fintype.card_congr (rootLeafSlotsEquiv G j), Fintype.card_coe, Comb.card_leaves]

/-- All choice-count losses are independent of the decoration and can be absorbed with
one high-order constant per root and one fixed geometric factor per branching node. -/
theorem exists_root_weight_choices_bound (d m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (w : ℕ) (G : Garden w),
      (Fintype.card (RootWeightChoices G d m) : ℝ) ≤ C ^ w * 2 ^ G.order := by
  obtain ⟨C, hC, hb⟩ := exists_root_weight_count_bound d m
  refine ⟨C, hC, ?_⟩
  intro w G
  have hcard := card_root_weight_choices (fun j : Fin w => RootLeafSlots G j) d m
  simp_rw [card_rootLeafSlots] at hcard
  have hreal : (Fintype.card (RootWeightChoices G d m) : ℝ) =
      ∏ j, (1 + (d : ℝ) * (2 * ((G.tree j).order : ℝ) + 1) ^ 2) ^ m := by
    rw [hcard]
    simp only [Nat.cast_prod, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    apply prod_congr rfl
    intro j _
    congr 1
    ring
  rw [hreal]
  simpa only [Fintype.card_fin, Garden.order] using
    root_weight_count_product_bound d m C hb (fun j => (G.tree j).order)

end WaveTurbulence.LGSpine
