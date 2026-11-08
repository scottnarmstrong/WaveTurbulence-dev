/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # FL-FACE: first maximizers and first minimizers with a tie-breaking rank

Supplement Lemma 9.1 partitions the selected time interval according to the maximizing lower endpoint (and, on the
general `kDomainFix` domain, the minimizing upper endpoint). Ties must be broken deterministically for an exact
identity: pinned neighbour times and the layer floor can coincide on sets of positive measure. A **first maximizer** of
`f` on `s` is a maximizer of smallest rank `r` among the maximizers. With `r` injective on `s` it exists and is unique,
so a sum over `s` restricted to the first maximizer collapses to the value at the maximum. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset

variable {α : Type*}

/-- `a` is a maximizer of `f` on `s` of least rank `r` among the maximizers (ties broken by `r`). -/
def IsFirstMax (s : Finset α) (f : α → ℝ) (r : α → ℕ) (a : α) : Prop :=
  ∀ b ∈ s, f b < f a ∨ (f b = f a ∧ r a ≤ r b)

/-- `a` is a minimizer of `f` on `s` of least rank `r` among the minimizers (ties broken by `r`). -/
def IsFirstMin (s : Finset α) (f : α → ℝ) (r : α → ℕ) (a : α) : Prop :=
  ∀ b ∈ s, f a < f b ∨ (f a = f b ∧ r a ≤ r b)

theorem exists_isFirstMax (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) (r : α → ℕ) :
    ∃ a ∈ s, IsFirstMax s f r a ∧ f a = s.sup' hs f := by
  obtain ⟨a₀, ha₀, he₀⟩ := s.exists_mem_eq_sup' hs f
  have hne : (s.filter fun b => f b = s.sup' hs f).Nonempty := ⟨a₀, mem_filter.2 ⟨ha₀, he₀.symm⟩⟩
  obtain ⟨a, ha, hmin⟩ := (s.filter fun b => f b = s.sup' hs f).exists_min_image r hne
  have ha' := mem_filter.1 ha
  refine ⟨a, ha'.1, fun b hb => ?_, ha'.2⟩
  have hle : f b ≤ f a := ha'.2 ▸ le_sup' f hb
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hmin b (mem_filter.2 ⟨hb, heq.trans ha'.2⟩)⟩

theorem exists_isFirstMin (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) (r : α → ℕ) :
    ∃ a ∈ s, IsFirstMin s f r a ∧ f a = s.inf' hs f := by
  obtain ⟨a₀, ha₀, he₀⟩ := s.exists_mem_eq_inf' hs f
  have hne : (s.filter fun b => f b = s.inf' hs f).Nonempty := ⟨a₀, mem_filter.2 ⟨ha₀, he₀.symm⟩⟩
  obtain ⟨a, ha, hmin⟩ := (s.filter fun b => f b = s.inf' hs f).exists_min_image r hne
  have ha' := mem_filter.1 ha
  refine ⟨a, ha'.1, fun b hb => ?_, ha'.2⟩
  have hle : f a ≤ f b := ha'.2 ▸ inf'_le f hb
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hmin b (mem_filter.2 ⟨hb, heq.symm.trans ha'.2⟩)⟩

theorem IsFirstMax.unique {s : Finset α} {f : α → ℝ} {r : α → ℕ} (hr : Set.InjOn r s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hA : IsFirstMax s f r a) (hB : IsFirstMax s f r b) : a = b := by
  refine hr ha hb ?_
  rcases hA b hb with h1 | ⟨h1, h1'⟩ <;> rcases hB a ha with h2 | ⟨h2, h2'⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd h1 (by rw [h2]; exact lt_irrefl _)
  · exact absurd h2 (by rw [h1]; exact lt_irrefl _)
  · exact le_antisymm h1' h2'

theorem IsFirstMin.unique {s : Finset α} {f : α → ℝ} {r : α → ℕ} (hr : Set.InjOn r s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hA : IsFirstMin s f r a) (hB : IsFirstMin s f r b) : a = b := by
  refine hr ha hb ?_
  rcases hA b hb with h1 | ⟨h1, h1'⟩ <;> rcases hB a ha with h2 | ⟨h2, h2'⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd h1 (by rw [h2]; exact lt_irrefl _)
  · exact absurd h2 (by rw [h1]; exact lt_irrefl _)
  · exact le_antisymm h1' h2'

theorem IsFirstMax.eq_sup' {s : Finset α} {f : α → ℝ} {r : α → ℕ} {a : α} (ha : a ∈ s)
    (hA : IsFirstMax s f r a) (hs : s.Nonempty) : f a = s.sup' hs f := by
  refine le_antisymm (le_sup' f ha) (sup'_le hs f fun b hb => ?_)
  rcases hA b hb with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem IsFirstMin.eq_inf' {s : Finset α} {f : α → ℝ} {r : α → ℕ} {a : α} (ha : a ∈ s)
    (hA : IsFirstMin s f r a) (hs : s.Nonempty) : f a = s.inf' hs f := by
  refine le_antisymm (le_inf' hs f fun b hb => ?_) (inf'_le f ha)
  rcases hA b hb with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-- A sum over `s` restricted to the first maximizer is the value at the maximum. -/
theorem sum_isFirstMax {β : Type*} [AddCommMonoid β] (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    (r : α → ℕ) (hr : Set.InjOn r s) (P : ℝ → Prop) (g : ℝ → β) :
    (∑ a ∈ s, if IsFirstMax s f r a ∧ P (f a) then g (f a) else 0) =
      if P (s.sup' hs f) then g (s.sup' hs f) else 0 := by
  obtain ⟨a₀, ha₀, hA₀, he₀⟩ := exists_isFirstMax s hs f r
  rw [sum_eq_single_of_mem a₀ ha₀ fun b hb hne => ?_]
  · simp only [hA₀, true_and, he₀]
  · have : ¬ IsFirstMax s f r b := fun hB => hne (hB.unique hr hb ha₀ hA₀ |>.symm ▸ rfl)
    simp only [this, false_and, ite_false]

/-- A sum over `s` restricted to the first minimizer is the value at the minimum. -/
theorem sum_isFirstMin {β : Type*} [AddCommMonoid β] (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    (r : α → ℕ) (hr : Set.InjOn r s) (P : ℝ → Prop) (g : ℝ → β) :
    (∑ a ∈ s, if IsFirstMin s f r a ∧ P (f a) then g (f a) else 0) =
      if P (s.inf' hs f) then g (s.inf' hs f) else 0 := by
  obtain ⟨a₀, ha₀, hA₀, he₀⟩ := exists_isFirstMin s hs f r
  rw [sum_eq_single_of_mem a₀ ha₀ fun b hb hne => ?_]
  · simp only [hA₀, true_and, he₀]
  · have : ¬ IsFirstMin s f r b := fun hB => hne (hB.unique hr hb ha₀ hA₀ |>.symm ▸ rfl)
    simp only [this, false_and, ite_false]

end WaveTurbulence.Flower.FlFace
