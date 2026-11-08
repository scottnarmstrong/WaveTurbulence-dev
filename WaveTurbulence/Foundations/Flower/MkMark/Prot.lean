/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.Owner

/-! # B2b MK-MARK: the protected set `Π₀` on addresses

`protI0 LG J pat t s` (MkDefs/Intrinsic) is the closed unit neighbourhood of the seeds: roots of non-cap trees,
capped-flower parents, and the pattern pins of the frozen `fixPat` around them. Here every ingredient is read off
the addresses of the garden (`NodeAt`, `LeafAt`, `BranchAt`, `CapFlowerAt`, `CapParentAt`, `FixSomeAt`, `SeedAt`,
`NearAt`), and `mem_protI0_iff` characterizes membership: `a ∈ Π₀ ↔ ∃ σ, NearAt a.1 σ ∧ SeedAt σ`. This is the
form transported by twists (`Transport.lean`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

section Addr
variable (LG : LayeredGarden w)

/-- `z` is a node of the garden. -/
def NodeAt (z : Address w) : Prop := z.2 ∈ (LG.garden.tree z.1).nodes

/-- `z` is a leaf of the garden. -/
def LeafAt (z : Address w) : Prop := z.2 ∈ (LG.garden.tree z.1).leaves

/-- `z` is a branching node of the garden. -/
def BranchAt (z : Address w) : Prop := z.2 ∈ (LG.garden.tree z.1).branching

/-- `z` is a capped flower: a leaf of a non-cap tree paired with a leaf of a cap tree. -/
def CapFlowerAt (J : Finset (Fin w)) (z : Address w) : Prop :=
  ∃ h : LeafAt LG z, z.1 ∉ J ∧ (LG.garden.pair ⟨z, h⟩).1.1 ∈ J

/-- `z` is the parent of a capped flower. -/
def CapParentAt (J : Finset (Fin w)) (z : Address w) : Prop :=
  BranchAt LG z ∧ ∃ i : Fin 3, CapFlowerAt LG J (addrExt z [i])

/-- The pinned branches of `fixCap`, read on addresses. -/
def FixSomeAt (J : Finset (Fin w)) (pat : Fin w → FixPat) (z : Address w) : Prop :=
  CapParentAt LG J z ∨
    match pat z.1 with
    | .plain => False
    | .dRoot => z.2 = []
    | .dParent => ∃ i : Fin 3, CapParentAt LG J (addrExt z [i])
    | .dChild i => ∃ y : Address w, CapParentAt LG J y ∧ z = addrExt y [i]

/-- The seeds of `Π₀`: non-cap roots and pinned branches. -/
def SeedAt (J : Finset (Fin w)) (pat : Fin w → FixPat) (z : Address w) : Prop :=
  NodeAt LG z ∧ ((z.1 ∉ J ∧ z.2 = []) ∨ (BranchAt LG z ∧ FixSomeAt LG J pat z))

/-- The address form of `MkDefs.NearNode`. -/
def NearAt (z σ : Address w) : Prop :=
  z.1 = σ.1 ∧ (z.2 = σ.2 ∨ (σ.2 ≠ [] ∧ z.2 = σ.2.dropLast) ∨ (z.2 ≠ [] ∧ z.2.dropLast = σ.2))

end Addr

section Char
variable {LG : LayeredGarden w} {J : Finset (Fin w)}

theorem isCapFlowerParent_iff (b : GBranch LG.garden.tree) :
    IsCapFlowerParent LG J b ↔ CapParentAt LG J b.1 := by
  constructor
  · rintro ⟨ℓ, ⟨h1, h2⟩, he, i, hi⟩
    have hz : ℓ.1 = addrExt b.1 [i] := Prod.ext he hi
    refine ⟨b.2, i, ?_, ?_, ?_⟩
    · show (addrExt b.1 [i]).2 ∈ (LG.garden.tree (addrExt b.1 [i]).1).leaves
      rw [← hz]
      exact ℓ.2
    · rw [← hz]
      exact h1
    · have e : (⟨addrExt b.1 [i], by rw [← hz]; exact ℓ.2⟩ : GLeaf LG.garden.tree) = ℓ := Subtype.ext hz.symm
      rw [e]
      exact h2
  · rintro ⟨-, i, hl, h1, h2⟩
    exact ⟨⟨addrExt b.1 [i], hl⟩, ⟨h1, h2⟩, rfl, i, rfl⟩

theorem fixCap_isSome_iff (pat : Fin w → FixPat) (t s : ℝ) (b : GBranch LG.garden.tree) :
    (fixCap LG J pat t s b).isSome ↔ FixSomeAt LG J pat b.1 := by
  unfold fixCap FixSomeAt
  by_cases hc : IsCapFlowerParent LG J b
  · simp only [hc, ↓reduceIte, Option.isSome_some, true_iff]
    exact Or.inl ((isCapFlowerParent_iff b).mp hc)
  · simp only [hc, ↓reduceIte]
    have hc' : ¬ CapParentAt LG J b.1 := fun h => hc ((isCapFlowerParent_iff b).mpr h)
    simp only [hc', false_or]
    cases hp : pat b.1.1 with
    | plain => simp
    | dRoot =>
      by_cases hr : b.1.2 = [] <;> simp [hr]
    | dParent =>
      simp only
      constructor
      · intro h
        by_contra hn
        rw [if_neg] at h
        · exact absurd h (by simp)
        rintro ⟨c, hcp, he, i, hi⟩
        exact hn ⟨i, by
          have hz : c.1 = addrExt b.1 [i] := Prod.ext he hi
          rw [← hz]
          exact (isCapFlowerParent_iff c).mp hcp⟩
      · rintro ⟨i, hi⟩
        have hb : (addrExt b.1 [i]).2 ∈ (LG.garden.tree (addrExt b.1 [i]).1).branching := hi.1
        rw [if_pos ⟨⟨addrExt b.1 [i], hb⟩, (isCapFlowerParent_iff _).mpr hi, rfl, i, rfl⟩]
        rfl
    | dChild i =>
      simp only
      constructor
      · intro h
        by_contra hn
        rw [if_neg] at h
        · exact absurd h (by simp)
        rintro ⟨c, hcp, he, hi⟩
        exact hn ⟨c.1, (isCapFlowerParent_iff c).mp hcp, Prod.ext he hi⟩
      · rintro ⟨y, hy, hz⟩
        rw [if_pos ⟨⟨y, hy.1⟩, (isCapFlowerParent_iff _).mpr hy, by rw [hz]; rfl, by rw [hz]; rfl⟩]
        rfl

/-- **`Π₀` on addresses.** -/
theorem mem_protI0_iff (pat : Fin w → FixPat) (t s : ℝ) (a : GNode LG.garden.tree) :
    a ∈ protI0 LG J pat t s ↔ ∃ σ : Address w, NearAt a.1 σ ∧ SeedAt LG J pat σ := by
  unfold protI0 protectedSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, or_false]
  constructor
  · rintro ⟨σ, hn, hσ⟩
    refine ⟨σ.1, hn, σ.2, ?_⟩
    rcases hσ with h | ⟨b, hb, hf⟩
    · exact Or.inl h
    · subst hb
      exact Or.inr ⟨b.2, (fixCap_isSome_iff pat t s b).mp hf⟩
  · rintro ⟨σ, hn, hnode, hσ⟩
    refine ⟨⟨σ, hnode⟩, hn, ?_⟩
    rcases hσ with h | ⟨hb, hf⟩
    · exact Or.inl h
    · exact Or.inr ⟨⟨σ, hb⟩, rfl, (fixCap_isSome_iff pat t s ⟨σ, hb⟩).mpr hf⟩

end Char

end WaveTurbulence.Flower.MkMark
