/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Card
/-! **Ghost assembly, part 1: the matching number** (the bank of the NC charges; design: `CHAIN-DESIGN.md`).

The bank of the run is the matching number of the NC graph: an NC triangle step deletes both endpoints of an edge
(`matchNum_erase_edge`: the number drops by one, paying the `L^{5η}` charge), and a creation step adds edges that are all
covered by `k` new vertices (`matchNum_le_add_cover`: the number grows by at most `k`, paid by the cone gain
`L^{-5ηk}`). -/
@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.Ghost

variable {V : Type*} [DecidableEq V]

/-- A matching of the relation `E` inside `S`: ordered pairs that are `E`-edges of distinct atoms of `S`, pairwise
vertex-disjoint. -/
def IsMatching (E : V → V → Prop) (S : Finset V) (m : Finset (V × V)) : Prop :=
  (∀ e ∈ m, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 ∧ E e.1 e.2) ∧
    ∀ e ∈ m, ∀ f ∈ m, e ≠ f → e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2

/-- **The matching number** of `E` on `S`. -/
noncomputable def matchNum (E : V → V → Prop) (S : Finset V) : ℕ := by
  classical
  exact ((S ×ˢ S).powerset.filter (IsMatching E S)).sup Finset.card

theorem IsMatching.subset_prod {E : V → V → Prop} {S : Finset V} {m : Finset (V × V)} (h : IsMatching E S m) :
    m ⊆ S ×ˢ S := fun e he => mem_product.2 ⟨(h.1 e he).1, (h.1 e he).2.1⟩

theorem isMatching_empty (E : V → V → Prop) (S : Finset V) : IsMatching E S ∅ :=
  ⟨fun e he => absurd he (notMem_empty e), fun e he => absurd he (notMem_empty e)⟩

theorem card_le_matchNum {E : V → V → Prop} {S : Finset V} {m : Finset (V × V)} (h : IsMatching E S m) :
    m.card ≤ matchNum E S := by
  classical
  unfold matchNum
  convert Finset.le_sup (f := Finset.card) (mem_filter.2 ⟨mem_powerset.2 h.subset_prod, h⟩)

theorem exists_matching_eq (E : V → V → Prop) (S : Finset V) :
    ∃ m, IsMatching E S m ∧ m.card = matchNum E S := by
  classical
  have hne : ((S ×ˢ S).powerset.filter (IsMatching E S)).Nonempty :=
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, isMatching_empty E S⟩⟩
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  refine ⟨m, (mem_filter.1 hm).2, ?_⟩
  unfold matchNum
  convert he.symm

/-- A matching of a sub-relation on a sub-set is a matching. -/
theorem IsMatching.mono {E E' : V → V → Prop} {S S' : Finset V} {m : Finset (V × V)} (h : IsMatching E S m)
    (hE : ∀ x y, x ∈ S → y ∈ S → E x y → E' x y) (hS : S ⊆ S') : IsMatching E' S' m := by
  refine ⟨fun e he => ?_, h.2⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.1 e he
  exact ⟨hS h1, hS h2, h3, hE _ _ h1 h2 h4⟩

theorem matchNum_mono {E E' : V → V → Prop} {S S' : Finset V} (hE : ∀ x y, x ∈ S → y ∈ S → E x y → E' x y)
    (hS : S ⊆ S') : matchNum E S ≤ matchNum E' S' := by
  obtain ⟨m, hm, he⟩ := exists_matching_eq E S
  rw [← he]
  exact card_le_matchNum (hm.mono hE hS)

/-- **Deleting both endpoints of an edge lowers the matching number by at least one.** -/
theorem matchNum_erase_edge {E : V → V → Prop} {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hE : E x y) : matchNum E ((S.erase x).erase y) + 1 ≤ matchNum E S := by
  obtain ⟨m, hm, he⟩ := exists_matching_eq E ((S.erase x).erase y)
  have hnot : ∀ e ∈ m, e.1 ≠ x ∧ e.1 ≠ y ∧ e.2 ≠ x ∧ e.2 ≠ y := by
    intro e he'
    obtain ⟨h1, h2, -⟩ := hm.1 e he'
    simp only [mem_erase] at h1 h2
    exact ⟨h1.2.1, h1.1, h2.2.1, h2.1⟩
  have hxym : (x, y) ∉ m := fun h => (hnot _ h).1 rfl
  have hM : IsMatching E S (insert (x, y) m) := by
    refine ⟨fun e he' => ?_, fun e he' f hf hef => ?_⟩
    · rcases mem_insert.1 he' with rfl | he'
      · exact ⟨hx, hy, hxy, hE⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hm.1 e he'
        exact ⟨(mem_erase.1 (mem_erase.1 h1).2).2, (mem_erase.1 (mem_erase.1 h2).2).2, h3, h4⟩
    · rcases mem_insert.1 he' with rfl | he' <;> rcases mem_insert.1 hf with rfl | hf
      · exact absurd rfl hef
      · obtain ⟨a1, a2, a3, a4⟩ := hnot f hf
        exact ⟨Ne.symm a1, Ne.symm a3, fun h => a2 h.symm, fun h => a4 h.symm⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hnot e he'
        exact ⟨a1, a2, a3, a4⟩
      · exact hm.2 e he' f hf hef
  have := card_le_matchNum hM
  rw [card_insert_of_notMem hxym, he] at this
  exact this

/-- **New edges covered by `C` raise the matching number by at most `|C|`.** Every `E'`-edge of `S'` is an `E`-edge of
`S` or has an endpoint in `C`. -/
theorem matchNum_le_add_cover {E E' : V → V → Prop} {S S' : Finset V} (C : Finset V)
    (hC : ∀ x y, x ∈ S' → y ∈ S' → x ≠ y → E' x y → (x ∈ S ∧ y ∈ S ∧ E x y) ∨ x ∈ C ∨ y ∈ C) :
    matchNum E' S' ≤ matchNum E S + C.card := by
  classical
  obtain ⟨m, hm, he⟩ := exists_matching_eq E' S'
  rw [← he]
  set m₁ := m.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S ∧ E e.1 e.2) with hm₁
  set m₂ := m.filter (fun e => ¬ (e.1 ∈ S ∧ e.2 ∈ S ∧ E e.1 e.2)) with hm₂
  have hsplit : m.card = m₁.card + m₂.card := by
    rw [hm₁, hm₂]; exact (Finset.card_filter_add_card_filter_not _).symm
  have h1 : m₁.card ≤ matchNum E S := by
    refine card_le_matchNum ⟨fun e he' => ?_, fun e he' f hf hef => hm.2 e (mem_filter.1 he').1 f (mem_filter.1 hf).1 hef⟩
    obtain ⟨-, a1, a2, a3⟩ := mem_filter.1 he'
    exact ⟨a1, a2, (hm.1 e (mem_filter.1 he').1).2.2.1, a3⟩
  have h2 : m₂.card ≤ C.card := by
    let g : V × V → V := fun e => if e.1 ∈ C then e.1 else e.2
    have hg : ∀ e ∈ m₂, g e ∈ C := by
      intro e he'
      obtain ⟨hem, hn⟩ := mem_filter.1 he'
      obtain ⟨a1, a2, a3, a4⟩ := hm.1 e hem
      rcases hC _ _ a1 a2 a3 a4 with h | h | h
      · exact absurd h hn
      · simp only [g, h, ↓reduceIte]
      · by_cases h1 : e.1 ∈ C
        · simp only [g, h1, ↓reduceIte]
        · simp only [g, h1, ↓reduceIte]; exact h
    refine card_le_card_of_injOn g (fun e he' => hg e he') ?_
    intro e he' f hf hfe
    by_contra hef
    obtain ⟨b1, b2, b3, b4⟩ := hm.2 e (mem_filter.1 he').1 f (mem_filter.1 hf).1 hef
    simp only [g] at hfe
    split_ifs at hfe <;> simp_all
  omega

end WaveTurbulence.GammaLow.FinalCount.Ghost
