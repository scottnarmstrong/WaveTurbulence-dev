/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.Flower.MkDefs.CardBound

/-! # C5b COMP-MK: the protected set of a capped component has at most `25R` nodes

B0 SCOPE §2 ("`|Π| ≤ 5·(R + 3R + R) = 25R` by A1's `protectedCardBound`"), proved: with `|J| = R` cap trees that are
single leaves,
* the non-cap roots number `R`;
* the pinned branches number at most `3R`: at most `R` capped flower parents (each is the parent of a capped flower,
  and a capped flower is determined by its cap), at most `R` pinned roots, and at most one pattern pin
  (`dParent`/`dChild`) per capped flower parent;
* the selected vertices number at most `R` (at most one per non-cap tree). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.CompMK

variable {w : ℕ}

theorem not_mem_of_branch (LG : LayeredGarden w) (J : Finset (Fin w))
    (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (b : GBranch LG.garden.tree) : b.1.1 ∉ J := by
  intro hb
  have h2 := b.2
  rw [hleaf _ hb] at h2
  simp [TTree.branching] at h2

theorem card_nonCap (J : Finset (Fin w)) : (univ.filter fun j : Fin w => j ∉ J).card = w - J.card := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin w))) (fun j => j ∈ J)
  have h1 : (univ.filter fun j : Fin w => j ∈ J) = J := by ext j; simp
  rw [h1, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- Two branches of one tree whose paths are `x ++ [i]` and `x' ++ [i']` with `x ++ [i] = x' ++ [i']` have `x = x'`. -/
theorem path_eq_of_append_single {x x' : TTree.Path} {i i' : Fin 3} (h : x ++ [i] = x' ++ [i']) : x = x' :=
  (List.append_inj' h (by simp)).1

theorem branch_ext {tree : Fin w → TTree} {b b' : GBranch tree} (h1 : b.1.1 = b'.1.1) (h2 : b.1.2 = b'.1.2) : b = b' :=
  Subtype.ext (Prod.ext h1 h2)

/-- At most `|J|` capped flower parents. -/
theorem card_capFlowerParent_le (LG : LayeredGarden w) (J : Finset (Fin w))
    (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) :
    (univ.filter (IsCapFlowerParent LG J)).card ≤ J.card := by
  let f : GBranch LG.garden.tree → Fin w := fun c =>
    if hc : IsCapFlowerParent LG J c then (LG.garden.pair (Classical.choose hc)).1.1 else c.1.1
  have hf : ∀ c (hc : IsCapFlowerParent LG J c), f c = (LG.garden.pair (Classical.choose hc)).1.1 := by
    intro c hc; simp only [f, dif_pos hc]
  refine Finset.card_le_card_of_injOn f (fun c hc => ?_) (fun c₁ hc₁ c₂ hc₂ heq => ?_)
  · have hc' : IsCapFlowerParent LG J c := (mem_filter.1 hc).2
    rw [hf c hc']
    exact (Classical.choose_spec hc').1.2
  · have h1 : IsCapFlowerParent LG J c₁ := (mem_filter.1 hc₁).2
    have h2 : IsCapFlowerParent LG J c₂ := (mem_filter.1 hc₂).2
    rw [hf c₁ h1, hf c₂ h2] at heq
    set ℓ₁ := Classical.choose h1 with hℓ₁
    set ℓ₂ := Classical.choose h2 with hℓ₂
    have s1 := Classical.choose_spec h1
    have s2 := Classical.choose_spec h2
    rw [← hℓ₁] at s1
    rw [← hℓ₂] at s2
    -- the pairs are the unique leaf of the same cap tree
    have hJ : (LG.garden.pair ℓ₁).1.1 ∈ J := s1.1.2
    have hroot : ∀ ℓ : GLeaf LG.garden.tree, ℓ.1.1 ∈ J → ℓ.1.2 = [] := by
      intro ℓ hℓ
      have := ℓ.2
      rw [hleaf _ hℓ] at this
      simpa [TTree.leaves] using this
    have hpp : LG.garden.pair ℓ₁ = LG.garden.pair ℓ₂ := by
      refine Subtype.ext (Prod.ext heq ?_)
      rw [hroot _ hJ, hroot _ (heq ▸ hJ)]
    have hℓ : ℓ₁ = ℓ₂ := by
      have := congrArg LG.garden.pair hpp
      rwa [LG.garden.pair_pair, LG.garden.pair_pair] at this
    obtain ⟨-, ht1, i₁, hp1⟩ := s1
    obtain ⟨-, ht2, i₂, hp2⟩ := s2
    rw [hℓ] at ht1 hp1
    exact branch_ext (ht1.symm.trans ht2) (path_eq_of_append_single (hp1.symm.trans hp2))

/-- At most `#{non-cap trees}` pinned roots (a root that is a branch lies in a non-cap tree). -/
theorem card_rootBranch_le (LG : LayeredGarden w) (J : Finset (Fin w))
    (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) :
    (univ.filter fun b : GBranch LG.garden.tree => b.1.2 = []).card ≤ (univ.filter fun j : Fin w => j ∉ J).card := by
  refine Finset.card_le_card_of_injOn (fun b => b.1.1) (fun b _ => ?_) (fun b₁ hb₁ b₂ hb₂ heq => ?_)
  · simpa using not_mem_of_branch LG J hleaf b
  · have h1 : b₁.1.2 = [] := (mem_filter.1 hb₁).2
    have h2 : b₂.1.2 = [] := (mem_filter.1 hb₂).2
    exact branch_ext heq (h1.trans h2.symm)

/-- The pattern-pin relation: `b` is pinned by the pattern of its tree relative to the capped flower parent `c`. -/
def PatPinOf (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (b c : GBranch LG.garden.tree) :
    Prop :=
  IsCapFlowerParent LG J c ∧ ((pat b.1.1 = FixPat.dParent ∧ c.IsChildOf b) ∨
    (∃ i, pat b.1.1 = FixPat.dChild i ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i]))

theorem patPinOf_inj (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat)
    {b₁ b₂ c : GBranch LG.garden.tree} (h1 : PatPinOf LG J pat b₁ c) (h2 : PatPinOf LG J pat b₂ c) : b₁ = b₂ := by
  obtain ⟨-, ⟨hp1, ht1, i₁, hc1⟩ | ⟨i₁, hp1, ht1, hc1⟩⟩ := h1 <;>
    obtain ⟨-, ⟨hp2, ht2, i₂, hc2⟩ | ⟨i₂, hp2, ht2, hc2⟩⟩ := h2
  · exact branch_ext (ht1.symm.trans ht2) (path_eq_of_append_single (hc1.symm.trans hc2))
  · have : b₁.1.1 = b₂.1.1 := ht1.symm.trans ht2.symm
    rw [this, hp2] at hp1; cases hp1
  · have : b₁.1.1 = b₂.1.1 := ht1.trans ht2
    rw [this, hp2] at hp1; cases hp1
  · have hb : b₁.1.1 = b₂.1.1 := ht1.trans ht2.symm
    rw [hb, hp2] at hp1
    cases hp1
    exact branch_ext hb (hc1.trans hc2.symm)

/-- **At most `3R` pinned branches.** -/
theorem card_pinned_le (LG : LayeredGarden w) (J : Finset (Fin w)) (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf)
    (pat : Fin w → FixPat) (t s : ℝ) :
    (univ.filter fun b : GBranch LG.garden.tree => (fixCap LG J pat t s b).isSome).card ≤
      J.card + (univ.filter fun j : Fin w => j ∉ J).card + J.card := by
  set CFP := univ.filter (IsCapFlowerParent LG J)
  set RP := univ.filter fun b : GBranch LG.garden.tree => b.1.2 = []
  set PP := univ.filter fun b : GBranch LG.garden.tree => ∃ c, PatPinOf LG J pat b c
  have hsub : (univ.filter fun b : GBranch LG.garden.tree => (fixCap LG J pat t s b).isSome) ⊆ CFP ∪ RP ∪ PP := by
    intro b hb
    have hb' : (fixCap LG J pat t s b).isSome := (mem_filter.1 hb).2
    by_cases hc : IsCapFlowerParent LG J b
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨mem_univ _, hc⟩))
    unfold fixCap at hb'
    rw [if_neg hc] at hb'
    rcases hpat : pat b.1.1 with _ | _ | _ | i
    · rw [hpat] at hb'; simp at hb'
    · rw [hpat] at hb'
      by_cases hr : b.1.2 = []
      · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨mem_univ _, hr⟩))
      · simp [hr] at hb'
    · rw [hpat] at hb'
      by_cases he : ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.IsChildOf b
      · obtain ⟨c, hc1, hc2⟩ := he
        exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, c, hc1, Or.inl ⟨hpat, hc2⟩⟩)
      · simp [he] at hb'
    · rw [hpat] at hb'
      by_cases he : ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i]
      · obtain ⟨c, hc1, hc2, hc3⟩ := he
        exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, c, hc1, Or.inr ⟨i, hpat, hc2, hc3⟩⟩)
      · simp [he] at hb'
  have hPP : PP.card ≤ CFP.card := by
    let f : GBranch LG.garden.tree → GBranch LG.garden.tree := fun b =>
      if hb : ∃ c, PatPinOf LG J pat b c then Classical.choose hb else b
    refine Finset.card_le_card_of_injOn f (fun b hb => ?_) (fun b₁ hb₁ b₂ hb₂ heq => ?_)
    · have hb' : ∃ c, PatPinOf LG J pat b c := (mem_filter.1 hb).2
      have : f b = Classical.choose hb' := dif_pos hb'
      rw [this]
      exact mem_filter.2 ⟨mem_univ _, (Classical.choose_spec hb').1⟩
    · have h1 : ∃ c, PatPinOf LG J pat b₁ c := (mem_filter.1 hb₁).2
      have h2 : ∃ c, PatPinOf LG J pat b₂ c := (mem_filter.1 hb₂).2
      have e1 : f b₁ = Classical.choose h1 := dif_pos h1
      have e2 : f b₂ = Classical.choose h2 := dif_pos h2
      have s1 := Classical.choose_spec h1
      have s2 := Classical.choose_spec h2
      rw [← e1] at s1
      rw [← e2, ← heq] at s2
      exact patPinOf_inj LG J pat s1 s2
  have hCFP : CFP.card ≤ J.card := card_capFlowerParent_le LG J hleaf
  have hRP : RP.card ≤ (univ.filter fun j : Fin w => j ∉ J).card := card_rootBranch_le LG J hleaf
  calc _ ≤ (CFP ∪ RP ∪ PP).card := Finset.card_le_card hsub
    _ ≤ CFP.card + RP.card + PP.card := by
        refine (Finset.card_union_le _ _).trans ?_
        have := Finset.card_union_le CFP RP
        omega
    _ ≤ _ := by omega

/-- **At most `#{non-cap trees}` selected vertices.** -/
theorem card_selSetCap_le (LG : LayeredGarden w) (J : Finset (Fin w)) (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf)
    (kSel : Fin w → Option ℕ) :
    (selSetCap LG J kSel).card ≤ (univ.filter fun j : Fin w => j ∉ J).card := by
  have htree : ∀ b ∈ selSetCap LG J kSel, ∀ j, selCap LG J kSel j = some b → b.1.1 = j := by
    intro b _ j hj
    unfold selCap at hj
    rcases hk : kSel j with _ | k
    · rw [hk] at hj; simp at hj
    · rw [hk] at hj
      simp only [Option.bind_some] at hj
      unfold stemAt at hj
      split_ifs at hj with hc
      · cases hj
        have hmem := Classical.choose_spec (Finset.card_eq_one.mp hc)
        have hin : Classical.choose (Finset.card_eq_one.mp hc) ∈
            ({Classical.choose (Finset.card_eq_one.mp hc)} : Finset (GBranch LG.garden.tree)) :=
          mem_singleton_self _
        rw [← hmem] at hin
        exact (mem_filter.1 (mem_filter.1 hin).1).2.1
  refine Finset.card_le_card_of_injOn (fun b => b.1.1) (fun b _ => ?_) (fun b₁ hb₁ b₂ hb₂ heq => ?_)
  · simpa using not_mem_of_branch LG J hleaf b
  · obtain ⟨j₁, hj₁⟩ := (mem_filter.1 hb₁).2
    obtain ⟨j₂, hj₂⟩ := (mem_filter.1 hb₂).2
    have e1 := htree b₁ hb₁ j₁ hj₁
    have e2 := htree b₂ hb₂ j₂ hj₂
    have hj : j₁ = j₂ := e1.symm.trans (heq.trans e2)
    rw [hj, hj₂] at hj₁
    exact (Option.some_injective _ hj₁).symm

/-- **`|Π| ≤ 25R`** for a capped component of width `2R` with `|J| = R` single-leaf caps. -/
theorem card_protI_le {R : ℕ} (LG : LayeredGarden (2 * R)) (J : Finset (Fin (2 * R))) (hJ : J.card = R)
    (hleaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) : (protI LG J pat t s kSel).card ≤ 25 * R := by
  have h0 := protectedCardBound LG J (fixCap LG J pat t s) (selSetCap LG J kSel)
  have h1 := card_nonCap J
  rw [hJ] at h1
  have h2 := card_pinned_le LG J hleaf pat t s
  have h3 := card_selSetCap_le LG J hleaf kSel
  unfold protI
  omega

end WaveTurbulence.Flower.CompMK
