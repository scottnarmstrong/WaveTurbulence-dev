/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutBasics
/-! Component sums for a cut that separates `v` from `v₂` (FINALCOUNT-HALF M2b). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem dartSign_mate (M : Molecule V D) (x : D) : M.dartSign (M.mate x) = - M.dartSign x := by
  unfold Molecule.dartSign
  have := M.out_mate x
  cases h : M.out x <;> simp_all

/-- The atoms of `M` in the component of `v₂` of the cut, other than `v₂`. -/
noncomputable def betaSide (M : Molecule V D) (v v₂ : V) (x₁ x₂ : D) : Finset V := by
  classical
  exact ((M.cut v v₂ x₁ x₂).atoms.filter fun a => (M.cut v v₂ x₁ x₂).SameComponent a v₂).erase v₂

theorem betaSide_sub (hcd : M.IsCutData v v₂ x₁ x₂) (hsep : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂) :
    betaSide M v v₂ x₁ x₂ ⊆ M.atoms.erase v := by
  classical
  intro a ha
  unfold betaSide at ha
  simp only [Finset.mem_erase, Finset.mem_filter] at ha
  obtain ⟨hne, hmem, hsc⟩ := ha
  have hm : a ∈ insert v₂ M.atoms := hmem
  rw [Finset.mem_insert] at hm
  refine Finset.mem_erase.mpr ⟨?_, hm.resolve_left hne⟩
  rintro rfl
  exact hsep hsc

theorem betaSide_not_v₂ : v₂ ∉ betaSide M v v₂ x₁ x₂ := by
  classical
  unfold betaSide; simp

/-- Sum over the side: key identity. -/
theorem beta_side_sum {E : Type*} [AddCommGroup E] (hcd : M.IsCutData v v₂ x₁ x₂)
    (hsep : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂) (g : D → E) (hg : ∀ x, g (M.mate x) = -g x) :
    ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂, g x +
      ∑ a ∈ betaSide M v v₂ x₁ x₂, ∑ x ∈ M.dartsAt a, g x = 0 := by
  classical
  set M' := M.cut v v₂ x₁ x₂ with hM'
  set S := M'.atoms.filter fun a => M'.SameComponent a v₂ with hS
  have hv₂S : v₂ ∈ S := by
    simp only [hS, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _, Relation.EqvGen.refl _⟩
  have hclosed : ∀ x, M'.atom x ∈ S → M'.atom (M'.mate x) ∈ S := by
    intro x hx
    simp only [hS, Finset.mem_filter] at hx ⊢
    exact ⟨M'.atom_mem _, Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩)) hx.2⟩
  have hsum := sum_dart_closed_zero M' S hclosed g hg
  have hsplit : ∑ a ∈ S, ∑ x ∈ M'.dartsAt a, g x =
      ∑ x ∈ M'.dartsAt v₂, g x + ∑ a ∈ betaSide M v v₂ x₁ x₂, ∑ x ∈ M'.dartsAt a, g x := by
    unfold betaSide
    rw [← Finset.add_sum_erase S _ hv₂S]
  rw [hsplit] at hsum
  rw [← hsum]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have hsub := betaSide_sub M hcd hsep ha
  rw [Finset.mem_erase] at hsub
  have hne : a ≠ v₂ := fun e => betaSide_not_v₂ M (e ▸ ha)
  rw [cut_dartsAt_other M hcd hsub.1 hne]

end WaveTurbulence.FinalCount
