/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Defs
/-! # FL-FACE: the number of faces

Each selected node has at most one parent and at most three branching children, hence at most `2 + 1 + 3 = 6`
endpoints, and `faces S` has at most `6 ^ #S ≤ 8 ^ #S` elements (supplement Lemma 9.1: "at most `8^a` individual
faces"). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset

variable {w : ℕ} {T : Fin w → TTree}

/-- A branching child has a strictly longer path, so it differs from its parent. -/
theorem IsChildOf.ne {b' b : GBranch T} (h : b'.IsChildOf b) : b' ≠ b := by
  rintro rfl
  obtain ⟨i, hi⟩ := h.2
  have := congrArg List.length hi
  simp at this

theorem card_parents_le_one (v : GBranch T) : (parents v).card ≤ 1 := by
  refine card_le_one.2 fun q hq q' hq' => ?_
  simp only [parents, mem_filter, mem_univ, true_and] at hq hq'
  obtain ⟨h1, i, hi⟩ := hq
  obtain ⟨h1', i', hi'⟩ := hq'
  have h2 : q.1.2 = q'.1.2 := by
    have := congrArg List.dropLast (hi.symm.trans hi')
    simpa using this
  exact Subtype.ext (Prod.ext (h1.symm.trans h1') h2)

theorem card_children_le_three (v : GBranch T) : (children v).card ≤ 3 := by
  let f : GBranch T → Fin 3 := fun c =>
    if h : ∃ i : Fin 3, c.1.2 = v.1.2 ++ [i] then h.choose else 0
  have hf : ∀ c ∈ children v, c.1.1 = v.1.1 ∧ c.1.2 = v.1.2 ++ [f c] := by
    intro c hc
    simp only [children, mem_filter, mem_univ, true_and] at hc
    obtain ⟨h1, h2⟩ := hc
    refine ⟨h1, ?_⟩
    simp only [f, h2, ↓reduceDIte]
    exact h2.choose_spec
  have hinj : Set.InjOn f (children v) := by
    intro c hc c' hc' he
    obtain ⟨h1, h2⟩ := hf c hc
    obtain ⟨h1', h2'⟩ := hf c' hc'
    exact Subtype.ext (Prod.ext (h1.trans h1'.symm) (by rw [h2, h2', he]))
  have := card_le_card_of_injOn f (fun c _ => mem_univ (f c)) hinj
  simpa using this

theorem card_upSet_le (v : GBranch T) : (upSet v).card ≤ 2 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ (card_image_le.trans (card_parents_le_one v)))

theorem card_lowSet_le (v : GBranch T) : (lowSet v).card ≤ 4 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ (card_image_le.trans (card_children_le_three v)))

theorem card_endChoices_le (v : GBranch T) : (endChoices v).card ≤ 6 :=
  (card_union_le _ _).trans (by have := card_upSet_le v; have := card_lowSet_le v; omega)

/-- The faces at `S` number at most `6 ^ #S`. -/
theorem faceCount_le_six (S : Finset (GBranch T)) : (faces S).card ≤ 6 ^ S.card := by
  rw [faces, Fintype.card_piFinset]
  have h : ∀ b : GBranch T, (if b ∈ S then endChoices b else {FaceEnd.top}).card =
      if b ∈ S then (endChoices b).card else 1 := fun b => by
    split_ifs <;> simp
  simp_rw [h]
  rw [prod_ite_mem, univ_inter]
  exact prod_le_pow_card S _ 6 fun b _ => card_endChoices_le b

/-- **Face count** (supplement Lemma 9.1): at most `8 ^ a` faces for `a` selected nodes. -/
theorem faceCount_le (S : Finset (GBranch T)) : (faces S).card ≤ 8 ^ S.card :=
  (faceCount_le_six S).trans (Nat.pow_le_pow_left (by norm_num) _)

end WaveTurbulence.Flower.FlFace
