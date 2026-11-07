/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutLad1
/-! Ladders under a cut, part 2 (FINALCOUNT-G2 step 2): ladder sets and maximal ladders. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LadderDisjoint

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem ladderAtoms_subset_atoms (N : Molecule V D) {m : ℕ} {u w : Fin (m + 1) → V} (h : N.IsLadder u w) :
    Molecule.ladderAtoms u w ⊆ N.atoms := by
  intro a ha
  obtain ⟨j, hj | hj⟩ := (mem_ladderAtoms u w a).1 ha
  · exact hj ▸ (h.2.2.1 j).1
  · exact hj ▸ (h.2.2.1 j).2

theorem isLadderSet_subset (N : Molecule V D) {S : Finset V} (h : N.IsLadderSet S) : S ⊆ N.atoms := by
  obtain ⟨m, u, w, hL, rfl⟩ := h
  exact ladderAtoms_subset_atoms N hL

/-- The ladders of the cut molecule are the ladders of `M` avoiding `v`. -/
theorem cut_isLadderSet_iff (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) {S : Finset V} :
    (M.cut v v₂ x₁ x₂).IsLadderSet S ↔ M.IsLadderSet S ∧ v ∉ S := by
  constructor
  · rintro ⟨m, u, w, hL, rfl⟩
    have h3 : ∀ a ∈ Molecule.ladderAtoms u w, a ≠ v ∧ a ≠ v₂ := by
      intro a ha
      have := ladder_atom_deg_ge_three _ hL ha
      constructor
      · rintro rfl; rw [cut_deg_v M hcd] at this; omega
      · rintro rfl; have := cut_deg_v₂ M hcd; omega
    have hu : Avoid v v₂ u := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inl rfl⟩)
    have hw : Avoid v v₂ w := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inr rfl⟩)
    exact ⟨⟨m, u, w, (cut_isLadder_iff M hcd hu hw).1 hL, rfl⟩, fun h => (h3 v h).1 rfl⟩
  · rintro ⟨⟨m, u, w, hL, rfl⟩, hv⟩
    have h3 : ∀ a ∈ Molecule.ladderAtoms u w, a ≠ v ∧ a ≠ v₂ := by
      intro a ha
      refine ⟨fun e => hv (e ▸ ha), fun e => hcd.2.1 (e ▸ ladderAtoms_subset_atoms M hL ha)⟩
    have hu : Avoid v v₂ u := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inl rfl⟩)
    have hw : Avoid v v₂ w := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inr rfl⟩)
    exact ⟨m, u, w, (cut_isLadder_iff M hcd hu hw).2 hL, rfl⟩

/-- Every ladder set lies in a maximal ladder. -/
theorem exists_maximal_ladder_ge (N : Molecule V D) {A : Finset V} (hA : N.IsLadderSet A) :
    ∃ S ∈ N.maximalLadders, A ⊆ S := by
  classical
  set 𝒮 := N.atoms.powerset.filter (fun S => N.IsLadderSet S ∧ A ⊆ S) with h𝒮
  have hne : 𝒮.Nonempty := ⟨A, by
    rw [h𝒮, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨isLadderSet_subset N hA, hA, Finset.Subset.refl _⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image 𝒮 Finset.card hne
  rw [h𝒮, Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, ?_, hS.2.2⟩
  unfold Molecule.maximalLadders
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨hS.1, hS.2.1, fun S' hS' hsub => ?_⟩
  have : S' ∈ 𝒮 := by
    rw [h𝒮, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨isLadderSet_subset N hS', hS', hS.2.2.trans hsub⟩
  exact (Finset.eq_of_subset_of_card_le hsub (hmax S' this)).symm

theorem mem_maximalLadders_iff (N : Molecule V D) {S : Finset V} :
    S ∈ N.maximalLadders ↔ N.IsLadderSet S ∧ ∀ S' : Finset V, N.IsLadderSet S' → S ⊆ S' → S' = S := by
  classical
  unfold Molecule.maximalLadders
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨isLadderSet_subset N h.1, h⟩⟩

/-- A maximal ladder of `M` avoiding `v` stays maximal after the cut. -/
theorem cut_maximal_of_avoid (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) {S : Finset V}
    (hS : S ∈ M.maximalLadders) (hv : v ∉ S) : S ∈ (M.cut v v₂ x₁ x₂).maximalLadders := by
  rw [mem_maximalLadders_iff] at hS ⊢
  refine ⟨(cut_isLadderSet_iff M hcd hdeg).2 ⟨hS.1, hv⟩, fun S' hS' hsub => ?_⟩
  exact hS.2 S' ((cut_isLadderSet_iff M hcd hdeg).1 hS').1 hsub

/-- A maximal ladder of the cut lies in a maximal ladder of `M`. -/
theorem cut_maximal_sub (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) {S' : Finset V}
    (hS' : S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders) : ∃ S ∈ M.maximalLadders, S' ⊆ S :=
  exists_maximal_ladder_ge M ((cut_isLadderSet_iff M hcd hdeg).1 ((mem_maximalLadders_iff _).1 hS').1).1

theorem cut_deg_le_four (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) : ∀ a ∈ (M.cut v v₂ x₁ x₂).atoms, (M.cut v v₂ x₁ x₂).deg a ≤ 4 := by
  intro a ha
  by_cases h1 : a = v
  · subst h1; rw [cut_deg_v M hcd]; omega
  by_cases h2 : a = v₂
  · subst h2; have := cut_deg_v₂ M hcd; omega
  · have haM : a ∈ M.atoms := (Finset.mem_insert.mp ha).resolve_left h2
    unfold Molecule.deg; rw [cut_dartsAt_other M hcd h1 h2]; exact hM a haM

end WaveTurbulence.FinalCount
