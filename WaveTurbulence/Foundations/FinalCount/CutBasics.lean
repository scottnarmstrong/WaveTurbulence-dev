/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutCover
/-! Basic facts about `Molecule.cut`: dart sets, degrees, and closed-set dart sums (FINALCOUNT-HALF M2a). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- Sum over the darts at the atoms of an `M.mate`-closed atom set of an odd function vanishes. -/
theorem sum_dart_closed_zero {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V)
    (hS : ∀ x, M.atom x ∈ S → M.atom (M.mate x) ∈ S) (g : D → E) (hg : ∀ x, g (M.mate x) = -g x) :
    ∑ a ∈ S, ∑ x ∈ M.dartsAt a, g x = 0 := by
  have h1 : ∑ a ∈ S, ∑ x ∈ M.dartsAt a, g x =
      ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ S), g x := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => M.atom x ∈ S))
      (t := S) (g := M.atom) (fun x hx => (Finset.mem_filter.mp hx).2)]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ ha, h⟩
    · intro h; exact h.2
  rw [h1]
  refine Finset.sum_involution (fun x _ => M.mate x) ?_ ?_ ?_ ?_
  · intro x _; rw [hg x]; simp
  · intro x _ hx h; exact M.mate_ne x h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hS x hx
  · intro x _; exact M.mate_mate x

section cut
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem cut_atom (v v₂ : V) (x₁ x₂ : D) (x : D) :
    (M.cut v v₂ x₁ x₂).atom x = if M.atom x = v ∧ x ≠ x₁ ∧ x ≠ x₂ then v₂ else M.atom x := rfl

theorem mem_dartsAt (M : Molecule V D) (a : V) (x : D) : x ∈ M.dartsAt a ↔ M.atom x = a := by
  simp [Molecule.dartsAt]

theorem cut_dartsAt_other (hcd : M.IsCutData v v₂ x₁ x₂) {a : V} (hav : a ≠ v) (hav₂ : a ≠ v₂) :
    (M.cut v v₂ x₁ x₂).dartsAt a = M.dartsAt a := by
  ext x
  rw [mem_dartsAt, mem_dartsAt, cut_atom]
  split_ifs with h
  · exact ⟨fun e => (hav₂ e.symm).elim, fun e => (hav (h.1 ▸ e.symm)).elim⟩
  · exact Iff.rfl

theorem cut_mem_dartsAt_v₂ (hcd : M.IsCutData v v₂ x₁ x₂) (x : D) :
    x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂ ↔ (M.atom x = v ∧ x ≠ x₁ ∧ x ≠ x₂) := by
  rw [mem_dartsAt, cut_atom]
  have hv₂ : ∀ y, M.atom y ≠ v₂ := fun y e => hcd.2.1 (e ▸ M.atom_mem y)
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => (hv₂ x e).elim, fun e => (h e).elim⟩

theorem cut_mem_dartsAt_v (hcd : M.IsCutData v v₂ x₁ x₂) (x : D) :
    x ∈ (M.cut v v₂ x₁ x₂).dartsAt v ↔ (M.atom x = v ∧ (x = x₁ ∨ x = x₂)) := by
  rw [mem_dartsAt, cut_atom]
  have hv₂ : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
  split_ifs with h
  · exact ⟨fun e => (hv₂ e).elim, fun e => (by tauto)⟩
  · constructor
    · intro e; refine ⟨e, ?_⟩; by_contra hc; push_neg at hc; exact h ⟨e, hc.1, hc.2⟩
    · intro e; exact e.1

/-- Dart sums at `v` split between the two halves of the cut. -/
theorem cut_sum_split (hcd : M.IsCutData v v₂ x₁ x₂) {E : Type*} [AddCommMonoid E] (g : D → E) :
    ∑ x ∈ M.dartsAt v, g x =
      ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v, g x + ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂, g x := by
  rw [← Finset.sum_union]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    rw [Finset.mem_union, mem_dartsAt, cut_mem_dartsAt_v M hcd, cut_mem_dartsAt_v₂ M hcd]
    constructor
    · intro h
      by_cases h1 : x = x₁ ∨ x = x₂
      · exact Or.inl ⟨h, h1⟩
      · push_neg at h1; exact Or.inr ⟨h, h1⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [cut_mem_dartsAt_v M hcd] at hx
    rw [cut_mem_dartsAt_v₂ M hcd] at hx'
    rcases hx.2 with h | h
    · exact hx'.2.1 h
    · exact hx'.2.2 h

/-- Degrees of the two halves of a cut. -/
theorem cut_deg_v (hcd : M.IsCutData v v₂ x₁ x₂) : (M.cut v v₂ x₁ x₂).deg v = 2 := by
  have hne : x₁ ≠ x₂ := fun e => by have := hcd.2.2.2.2.2.1; have h2 := hcd.2.2.2.2.2.2; rw [e] at this; simp_all
  have : (M.cut v v₂ x₁ x₂).dartsAt v = {x₁, x₂} := by
    ext x
    rw [cut_mem_dartsAt_v M hcd]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (h | h)
      · exact ⟨h ▸ hcd.2.2.1, Or.inl h⟩
      · exact ⟨h ▸ hcd.2.2.2.1, Or.inr h⟩
  unfold Molecule.deg; rw [this, Finset.card_pair hne]

end cut
end WaveTurbulence.FinalCount
