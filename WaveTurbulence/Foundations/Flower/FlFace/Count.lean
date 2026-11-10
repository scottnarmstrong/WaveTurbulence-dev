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

end WaveTurbulence.Flower.FlFace
