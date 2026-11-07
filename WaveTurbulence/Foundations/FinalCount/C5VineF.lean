/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5VineE
import Mathlib.Tactic

/-! # Prop 9.6, case (5): the bond-count identity between `M₀` and its reduction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountG8

variable {V : Type*} [DecidableEq V]

/-- Abstract bond-count identity: `bM` the counts of `M₀`, `bP` those of the reduction, `a, b` the removed atoms,
`c, d` the ends of `b`, `u₁, u₂` the ends of `a`. -/
theorem bb_identity (MA : Finset V) (bM bP : V → V → ℕ) (a b c d u₁ u₂ : V)
    (hsM : ∀ p q, bM p q = bM q p) (hsP : ∀ p q, bP p q = bP q p)
    (hab : a ≠ b) (ha : a ∈ MA) (hb : b ∈ MA)
    (hc : c ∈ MA ∧ c ≠ a ∧ c ≠ b) (hd : d ∈ MA ∧ d ≠ a ∧ d ≠ b)
    (hu1 : u₁ ∈ MA ∧ u₁ ≠ a ∧ u₁ ≠ b) (hu2 : u₂ ∈ MA ∧ u₂ ≠ a ∧ u₂ ≠ b)
    (h1 : ∀ p q, (p ∈ MA ∧ p ≠ a ∧ p ≠ b) → (q ∈ MA ∧ q ≠ a ∧ q ≠ b) →
      bP p q = bM p q + (if s(d, c) = s(p, q) then 1 else 0))
    (h2 : ∀ p q, ¬ ((p ∈ MA ∧ p ≠ a ∧ p ≠ b) ∧ (q ∈ MA ∧ q ≠ a ∧ q ≠ b)) → bP p q = 0)
    (h3 : ∀ q, bM a q = (if q = u₁ then 1 else 0) + (if q = u₂ then 1 else 0))
    (h4 : ∀ q, bM b q = (if q = c then 1 else 0) + (if q = d then 1 else 0))
    (h5 : ∀ p q, p ∉ MA → bM p q = 0) (p q : V) :
    bM p q + (if s(d, c) = s(p, q) then 1 else 0) = bP p q + (if s(c, b) = s(p, q) then 1 else 0) +
      (if s(b, d) = s(p, q) then 1 else 0) + (if s(u₁, a) = s(p, q) then 1 else 0) +
      (if s(a, u₂) = s(p, q) then 1 else 0) := by
  classical
  -- the case `p ∈ {a, b}`
  have hpa : ∀ q, bM a q + (if s(d, c) = s(a, q) then 1 else 0) = bP a q + (if s(c, b) = s(a, q) then 1 else 0) +
      (if s(b, d) = s(a, q) then 1 else 0) + (if s(u₁, a) = s(a, q) then 1 else 0) +
      (if s(a, u₂) = s(a, q) then 1 else 0) := by
    intro q
    rw [h3, h2 a q (fun h => h.1.2.1 rfl)]
    have e1 : ¬ s(d, c) = s(a, q) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hd.2.1 h1
      · exact hc.2.1 h2
    have e2 : ¬ s(c, b) = s(a, q) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hc.2.1 h1
      · exact hab h2.symm
    have e3 : ¬ s(b, d) = s(a, q) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hab h1.symm
      · exact hd.2.1 h2
    have e4 : (s(u₁, a) = s(a, q)) ↔ q = u₁ := by
      constructor
      · intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 hu1.2.1
        · exact h1.symm
      · rintro rfl; exact Sym2.eq_swap
    have e5 : (s(a, u₂) = s(a, q)) ↔ q = u₂ := by
      constructor
      · intro h; rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2.symm
        · exact absurd h2 hu2.2.1
      · rintro rfl; rfl
    simp only [if_neg e1, if_neg e2, if_neg e3, e4, e5]
    simp
  have hpb : ∀ q, bM b q + (if s(d, c) = s(b, q) then 1 else 0) = bP b q + (if s(c, b) = s(b, q) then 1 else 0) +
      (if s(b, d) = s(b, q) then 1 else 0) + (if s(u₁, a) = s(b, q) then 1 else 0) +
      (if s(a, u₂) = s(b, q) then 1 else 0) := by
    intro q
    rw [h4, h2 b q (fun h => h.1.2.2 rfl)]
    have e1 : ¬ s(d, c) = s(b, q) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hd.2.2 h1
      · exact hc.2.2 h2
    have e2 : (s(c, b) = s(b, q)) ↔ q = c := by
      constructor
      · intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1 hc.2.2
        · exact h1.symm
      · rintro rfl; exact Sym2.eq_swap
    have e3 : (s(b, d) = s(b, q)) ↔ q = d := by
      constructor
      · intro h; rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2.symm
        · exact absurd h2 hd.2.2
      · rintro rfl; rfl
    have e4 : ¬ s(u₁, a) = s(b, q) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hu1.2.2 h1
      · exact hab h2
    have e5 : ¬ s(a, u₂) = s(b, q) := by
      intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hab h1
      · exact hu2.2.2 h2
    simp only [if_neg e1, if_neg e4, if_neg e5, e2, e3]
    simp
  by_cases hp : p = a
  · subst hp; exact hpa q
  by_cases hp' : p = b
  · subst hp'; exact hpb q
  by_cases hq : q = a
  · subst hq
    have := hpa p
    rw [hsM p q, hsP p q]
    simpa [Sym2.eq_swap] using this
  by_cases hq' : q = b
  · subst hq'
    have := hpb p
    rw [hsM p q, hsP p q]
    simpa [Sym2.eq_swap] using this
  -- `p, q ∉ {a, b}`
  have hmem : ∀ x y : V, x ∈ MA → y ∈ MA → s(x, y) = s(p, q) → p ∈ MA ∧ q ∈ MA := by
    intro x y hx hy h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ hx, h2 ▸ hy⟩
    · exact ⟨h2 ▸ hy, h1 ▸ hx⟩
  have hnab : ∀ x y z : V, (z = a ∨ z = b) → s(x, y) = s(p, q) → (x = z ∨ y = z) → False := by
    intro x y z hz h hxy
    have hpz : p ≠ z := fun h' => by
      rcases hz with h'' | h'' <;> [exact hp (h'.trans h''); exact hp' (h'.trans h'')]
    have hqz : q ≠ z := fun h' => by
      rcases hz with h'' | h'' <;> [exact hq (h'.trans h''); exact hq' (h'.trans h'')]
    have hmem' : z ∈ s(x, y) := Sym2.mem_iff.mpr (by tauto)
    rw [h] at hmem'
    rcases Sym2.mem_iff.mp hmem' with h' | h'
    · exact hpz h'.symm
    · exact hqz h'.symm
  by_cases hboth : p ∈ MA ∧ q ∈ MA
  · have hP1 := h1 p q ⟨hboth.1, hp, hp'⟩ ⟨hboth.2, hq, hq'⟩
    have f1 : ¬ s(c, b) = s(p, q) := fun h => hnab c b b (Or.inr rfl) h (Or.inr rfl)
    have f2 : ¬ s(b, d) = s(p, q) := fun h => hnab b d b (Or.inr rfl) h (Or.inl rfl)
    have f3 : ¬ s(u₁, a) = s(p, q) := fun h => hnab u₁ a a (Or.inl rfl) h (Or.inr rfl)
    have f4 : ¬ s(a, u₂) = s(p, q) := fun h => hnab a u₂ a (Or.inl rfl) h (Or.inl rfl)
    rw [hP1]
    simp only [if_neg f1, if_neg f2, if_neg f3, if_neg f4]
    simp
  · have hP0 := h2 p q (fun h => hboth ⟨h.1.1, h.2.1⟩)
    have hM0 : bM p q = 0 := by
      by_cases hpM : p ∈ MA
      · have hqM : q ∉ MA := fun h => hboth ⟨hpM, h⟩
        rw [hsM]; exact h5 q p hqM
      · exact h5 p q hpM
    have f0 : ¬ s(d, c) = s(p, q) := fun h => hboth (hmem d c hd.1 hc.1 h)
    have f1 : ¬ s(c, b) = s(p, q) := fun h => hboth (hmem c b hc.1 hb h)
    have f2 : ¬ s(b, d) = s(p, q) := fun h => hboth (hmem b d hb hd.1 h)
    have f3 : ¬ s(u₁, a) = s(p, q) := fun h => hboth (hmem u₁ a hu1.1 ha h)
    have f4 : ¬ s(a, u₂) = s(p, q) := fun h => hboth (hmem a u₂ ha hu2.1 h)
    rw [hP0, hM0]
    simp only [if_neg f0, if_neg f1, if_neg f2, if_neg f3, if_neg f4]

end WaveTurbulence.FinalCountG8
