/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG5
/-! **FINALCOUNT-G3: `vineLG`, part 6: a double bond is a vine of type (I).** -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V]

/-- A molecule with exactly two atoms, each with one incoming and one outgoing bond and no self-loop, is a vine of type (I). -/
theorem isVine_I {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {j₁ j₂ : V} (hne : j₁ ≠ j₂)
    (hat : M.atoms = {j₁, j₂}) (ho1 : M.outdeg j₁ = 1) (hi1 : M.indeg j₁ = 1) (ho2 : M.outdeg j₂ = 1)
    (hi2 : M.indeg j₂ = 1) (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) : M.IsVine .I M.atoms j₁ j₂ := by
  have hg : ∀ x, M.InGroup M.atoms x := fun x => ⟨M.atom_mem x, M.atom_mem _⟩
  have m1 : j₁ ∈ M.atoms := by rw [hat]; simp
  have m2 : j₂ ∈ M.atoms := by rw [hat]; simp
  -- the out darts
  obtain ⟨x1, hx1⟩ := Finset.card_eq_one.1 ho1
  obtain ⟨x2, hx2⟩ := Finset.card_eq_one.1 ho2
  have hx1m : x1 ∈ (M.dartsAt j₁).filter fun x => M.out x = true := by rw [hx1]; simp
  have hx2m : x2 ∈ (M.dartsAt j₂).filter fun x => M.out x = true := by rw [hx2]; simp
  have a1 : M.atom x1 = j₁ := (Finset.mem_filter.1 (Finset.mem_filter.1 hx1m).1).2
  have a2 : M.atom x2 = j₂ := (Finset.mem_filter.1 (Finset.mem_filter.1 hx2m).1).2
  have o1 : M.out x1 = true := (Finset.mem_filter.1 hx1m).2
  have o2 : M.out x2 = true := (Finset.mem_filter.1 hx2m).2
  have mem_at : ∀ x, M.atom x = j₁ ∨ M.atom x = j₂ := fun x => by
    have := M.atom_mem x; rw [hat] at this; simpa using this
  have b1 : M.atom (M.mate x1) = j₂ := by
    rcases mem_at (M.mate x1) with h | h
    · exact absurd (a1.trans h.symm) (hnl x1)
    · exact h
  have b2 : M.atom (M.mate x2) = j₁ := by
    rcases mem_at (M.mate x2) with h | h
    · exact h
    · exact absurd (a2.trans h.symm) (hnl x2)
  have hout : ∀ y, M.out y = true → y = x1 ∨ y = x2 := by
    intro y hy
    rcases mem_at y with h | h
    · left
      have : y ∈ (M.dartsAt j₁).filter fun x => M.out x = true :=
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, hy⟩
      rw [hx1] at this; simpa using this
    · right
      have : y ∈ (M.dartsAt j₂).filter fun x => M.out x = true :=
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, hy⟩
      rw [hx2] at this; simpa using this
  have hx12 : x1 ≠ x2 := fun e => hne (by rw [← a1, ← a2, e])
  refine ⟨⟨Finset.Subset.refl _, m1, m2, hne, ?_, ?_, ?_, ?_, ?_, ?_⟩, [], rfl, fun v => if v = j₁ then 0 else 1, ?_, ?_, ?_, ?_⟩
  · rw [outIn_of_all hg]; exact ho1
  · rw [inIn_of_all hg]; exact hi1
  · rw [outIn_of_all hg]; exact ho2
  · rw [inIn_of_all hg]; exact hi2
  · intro v hv h1 h2; rw [hat] at hv; simp at hv; tauto
  · -- connected
    have step : Relation.EqvGen (fun a b => ∃ x, M.InGroup M.atoms x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) j₁ j₂ :=
      Relation.EqvGen.rel _ _ ⟨x1, hg x1, a1, b1⟩
    intro u hu v hv
    rw [hat] at hu hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact step
    · exact Relation.EqvGen.symm _ _ step
    · exact Relation.EqvGen.refl _
  · intro u hu v hv e
    rw [hat] at hu hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    simp only at e
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · simp [hne, hne.symm] at e
    · simp [hne, hne.symm] at e
    · rfl
  · rw [hat]
    ext n
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
      Finset.mem_range]
    simp [VineType.expand, VineType.template, hne.symm]
    omega
  · simp [hne.symm]
  · have hgb : M.groupBonds M.atoms = {s(j₁, j₂), s(j₁, j₂)} := by
      unfold Molecule.groupBonds
      have : (Finset.univ.filter fun x => M.out x = true ∧ M.InGroup M.atoms x) = {x1, x2} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h, -⟩; exact hout y h
        · rintro (rfl | rfl)
          · exact ⟨o1, hg _⟩
          · exact ⟨o2, hg _⟩
      rw [this]
      have e2 : M.ends x2 = s(j₁, j₂) := by
        simp [Molecule.ends, a2, b2, Sym2.eq_swap]
      have e1 : M.ends x1 = s(j₁, j₂) := by simp [Molecule.ends, a1, b1]
      rw [Finset.insert_val_of_notMem (by simpa using hx12)]
      simp [e1, e2]
    rw [hgb]
    simp [VineType.expand, VineType.template, hne.symm]
    rfl

end WaveTurbulence.FinalCountG3
