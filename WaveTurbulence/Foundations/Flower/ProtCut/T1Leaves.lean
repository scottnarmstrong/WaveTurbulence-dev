/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Dec

/-! # D2c-3 PROT-CUT: the leaves of a type-1 couple

Both roots of a type-1 couple are branching, so every leaf lies in one of the three sub-couples:
`T1Data.t1Leaf : GLeaf G₁ ⊕ (GLeaf G₂ ⊕ GLeaf G₃) → GLeaf G` is a bijection. All four gardens are plain and the
placements keep signs, so the input leaves (sign `+`, unmarked) split as well: **`T1Data.prod_inputLeaves_t1`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {G G₁ G₂ G₃ : Garden 2} (h : T1Data c Q₁ Q₂ Q₃ G G₁ G₂ G₃)
include h

/-- The leaves of the three sub-couples, placed in the couple. -/
def lfA (x : GLeaf G₁.tree) : GLeaf G.tree := ⟨t1A c x.1, (h.memT_A x.1).2.1.mpr x.2⟩
def lfB (x : GLeaf G₂.tree) : GLeaf G.tree := ⟨t1B x.1, (h.memT_B x.1).2.1.mpr x.2⟩
def lfC (x : GLeaf G₃.tree) : GLeaf G.tree := ⟨t1C c x.1, (h.memT_C x.1).2.1.mpr x.2⟩

theorem lfA_toNode (x : GLeaf G₁.tree) : (h.lfA x).toNode = h.ιA x.toNode := rfl
theorem lfB_toNode (x : GLeaf G₂.tree) : (h.lfB x).toNode = h.ιB x.toNode := rfl
theorem lfC_toNode (x : GLeaf G₃.tree) : (h.lfC x).toNode = h.ιC x.toNode := rfl

/-- **The leaves of a type-1 couple.** -/
def t1Leaf : GLeaf G₁.tree ⊕ (GLeaf G₂.tree ⊕ GLeaf G₃.tree) → GLeaf G.tree
  | .inl x => h.lfA x
  | .inr (.inl x) => h.lfB x
  | .inr (.inr x) => h.lfC x

theorem t1Leaf_injective : Function.Injective h.t1Leaf := by
  intro z z' he
  have hv : (h.t1Leaf z).1 = (h.t1Leaf z').1 := by rw [he]
  rcases z with x | x | x <;> rcases z' with x' | x' | x'
  · exact congrArg Sum.inl (Subtype.ext (t1A_injective c hv))
  · simp only [t1Leaf, lfA, lfB, t1A, t1B, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1, hv.2.1⟩ (t1_hAB c _ _)
  · simp only [t1Leaf, lfA, lfC, t1A, t1C, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1, hv.2.1⟩ (t1_hAC c _ _)
  · simp only [t1Leaf, lfA, lfB, t1A, t1B, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1.symm, hv.2.1.symm⟩ (t1_hAB c _ _)
  · exact congrArg (fun t => Sum.inr (Sum.inl t)) (Subtype.ext (t1B_injective hv))
  · simp only [t1Leaf, lfB, lfC, t1B, t1C, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1, hv.2.1⟩ (t1_hBC c _ _)
  · simp only [t1Leaf, lfA, lfC, t1A, t1C, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1.symm, hv.2.1.symm⟩ (t1_hAC c _ _)
  · simp only [t1Leaf, lfB, lfC, t1B, t1C, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1.symm, hv.2.1.symm⟩ (t1_hBC c _ _)
  · exact congrArg (fun t => Sum.inr (Sum.inr t)) (Subtype.ext (t1C_injective c hv))

theorem t1Leaf_surjective : Function.Surjective h.t1Leaf := by
  rintro ⟨⟨t, p⟩, hl⟩
  rcases p with _ | ⟨i, q⟩
  · exact absurd (h.root_mem t) (TTree.not_mem_branching_of_mem_leaves _ hl)
  rcases t1_cover c t i with ⟨t', ht'⟩ | ⟨t', ht'⟩ | ⟨t', ht'⟩
  · have e : t1A c (t', q) = (t, i :: q) := by
      simp only [t1A]; rw [Prod.mk.injEq] at ht' ⊢; exact ⟨ht'.1, by rw [ht'.2]⟩
    have hq : q ∈ (G₁.tree t').leaves := (h.memT_A (t', q)).2.1.mp (by rw [e]; exact hl)
    exact ⟨.inl ⟨(t', q), hq⟩, Subtype.ext e⟩
  · have e : t1B (t', q) = (t, i :: q) := by
      simp only [t1B]; rw [Prod.mk.injEq] at ht' ⊢; exact ⟨ht'.1, by rw [ht'.2]⟩
    have hq : q ∈ (G₂.tree t').leaves := (h.memT_B (t', q)).2.1.mp (by rw [e]; exact hl)
    exact ⟨.inr (.inl ⟨(t', q), hq⟩), Subtype.ext e⟩
  · have e : t1C c (t', q) = (t, i :: q) := by
      simp only [t1C]; rw [Prod.mk.injEq] at ht' ⊢; exact ⟨ht'.1, by rw [ht'.2]⟩
    have hq : q ∈ (G₃.tree t').leaves := (h.memT_C (t', q)).2.1.mp (by rw [e]; exact hl)
    exact ⟨.inr (.inr ⟨(t', q), hq⟩), Subtype.ext e⟩

theorem t1Leaf_bijective : Function.Bijective h.t1Leaf := ⟨h.t1Leaf_injective, h.t1Leaf_surjective⟩

omit h in
theorem prod_inputLeaves_plain {w : ℕ} {G' : Garden w} (hp : G'.IsPlain) {M : Type*} [CommMonoid M]
    (g : GLeaf G'.tree → M) :
    ∏ ℓ ∈ inputLeaves G', g ℓ = ∏ ℓ, if G'.sign ℓ.toNode = 1 then g ℓ else 1 := by
  classical
  rw [← Finset.prod_filter]
  congr 1
  ext ℓ
  simp [inputLeaves, hp ℓ]

/-- **The input leaves of a type-1 couple.** -/
theorem prod_inputLeaves_t1 {M : Type*} [CommMonoid M] (f : Fin 2 × Path → M) :
    ∏ ℓ ∈ inputLeaves G, f ℓ.1 =
      (∏ ℓ ∈ inputLeaves G₁, f (t1A c ℓ.1)) *
        ((∏ ℓ ∈ inputLeaves G₂, f (t1B ℓ.1)) * ∏ ℓ ∈ inputLeaves G₃, f (t1C c ℓ.1)) := by
  classical
  rw [prod_inputLeaves_plain h.plain, prod_inputLeaves_plain h.dec₁.1.1, prod_inputLeaves_plain h.dec₂.1.1,
    prod_inputLeaves_plain h.dec₃.1.1, ← (Equiv.ofBijective _ h.t1Leaf_bijective).prod_comp]
  simp only [Fintype.prod_sum_type, Equiv.ofBijective_apply, t1Leaf]
  congr 1
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [h.lfA_toNode, h.sign_ιA]; rfl
  congr 1
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [h.lfB_toNode, h.sign_ιB]; rfl
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [h.lfC_toNode, h.sign_ιC]; rfl

theorem lfA_input (ℓ : GLeaf G₁.tree) (hℓ : ℓ ∈ inputLeaves G₁) : h.lfA ℓ ∈ inputLeaves G := by
  rw [mem_inputLeaves] at hℓ ⊢
  exact ⟨by rw [h.lfA_toNode, h.sign_ιA]; exact hℓ.1, h.plain _⟩

theorem lfB_input (ℓ : GLeaf G₂.tree) (hℓ : ℓ ∈ inputLeaves G₂) : h.lfB ℓ ∈ inputLeaves G := by
  rw [mem_inputLeaves] at hℓ ⊢
  exact ⟨by rw [h.lfB_toNode, h.sign_ιB]; exact hℓ.1, h.plain _⟩

theorem lfC_input (ℓ : GLeaf G₃.tree) (hℓ : ℓ ∈ inputLeaves G₃) : h.lfC ℓ ∈ inputLeaves G := by
  rw [mem_inputLeaves] at hℓ ⊢
  exact ⟨by rw [h.lfC_toNode, h.sign_ιC]; exact hℓ.1, h.plain _⟩

end T1Data

end WaveTurbulence.Flower.ProtCut
