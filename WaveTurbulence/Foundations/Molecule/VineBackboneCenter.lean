/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpandedSingleBackbone
import Mathlib.Tactic

/-! # Literal normal centers have two distinct attachments to the backbone -/

public section
namespace WaveTurbulence.Vine

/-- Every core atom omitted by a nontrivial template's single backbone
has two distinct backbone neighbors. The type-I template is excluded. -/
theorem template_center_neighbors (X : VineType) : ∀ i : Fin X.template.n,
    X ≠ .I → ¬OnSingleBackbone X i.1 →
    ∃ j k : Fin X.template.n,OnSingleBackbone X j.1 ∧ OnSingleBackbone X k.1 ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ EdgeAdj X.template.bonds i.1 j.1 ∧
      EdgeAdj X.template.bonds i.1 k.1 := by
  cases X <;> decide

/-- Marked slots avoid each normal center, so its attachment edges
are retained under all rung insertions. -/
theorem template_slot_avoids_center (X : VineType) : ∀ i : Fin X.template.n,
    X ≠ .I → ¬OnSingleBackbone X i.1 → ∀ s ∈ X.template.slots,
    i.1 ≠ s.1.1 ∧ i.1 ≠ s.1.2 ∧ i.1 ≠ s.2.1 ∧ i.1 ≠ s.2.2 := by
  cases X <;> decide

/-- Any nonbackbone label in a nontrivial template is an old normal
center, never a freshly allocated label. -/
theorem nonbackbone_label_lt (X : VineType) (hX : X ≠ .I) (i : ℕ)
    (hi : ¬OnSingleBackbone X i) : i<X.template.n := by
  cases X <;> simp_all [OnSingleBackbone,VineType.template]

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A normal center's literal attachment edge is present in every
expanded realization. Its encoded orientation is immaterial. -/
theorem VineRealization.center_core_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (i j : Fin X.template.n) (hX : X ≠ .I) (hi : ¬OnSingleBackbone X i.1)
    (he : EdgeAdj X.template.bonds i.1 j.1) : M.Adj (R.coreAtom i).1 (R.coreAtom j).1 := by
  have hs := template_slot_avoids_center X i hX hi
  rcases he with he | he
  · apply R.core_untouched_adj i j he
    intro s hsm
    have hh := hs s hsm
    constructor
    · intro heq
      exact hh.1 (congrArg Prod.fst heq)
    · intro heq
      exact hh.2.2.1 (congrArg Prod.fst heq)
  · apply Mole.adj_symmetric M
    apply R.core_untouched_adj j i he
    intro s hsm
    have hh := hs s hsm
    constructor
    · intro heq
      exact hh.2.1 (congrArg Prod.snd heq)
    · intro heq
      exact hh.2.2.2 (congrArg Prod.snd heq)

end WaveTurbulence.Vine
