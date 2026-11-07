/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Iso
public import WaveTurbulence.Foundations.FinalCount.CutLad5
/-! **FINALCOUNT-G3 (R29 item 6, O3), part 1: ladders of `M - E`.**  A ladder of `eraseSet M E` is a ladder of `M` avoiding `E`:
`(eraseSet M E).IsLadderSet S ↔ M.IsLadderSet S ∧ Disjoint S E`; hence a maximal ladder of `M` avoiding `E` stays maximal, and a maximal
ladder of `M - E` lies in a maximal ladder of `M`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u v
variable {V : Type u} [DecidableEq V] {D : Type v} [Fintype D] [DecidableEq D] (M : Molecule V D) {E : Finset V}

theorem eraseSet_bondsBetween {a b : V} (ha : a ∉ E) (hb : b ∉ E) :
    (eraseSet M E).bondsBetween a b = M.bondsBetween a b := by
  unfold Molecule.bondsBetween Molecule.bonds
  refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy
  · intro y _ y' _ e; exact Subtype.ext e
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hx2 : M.ends x = s(a, b) := hx.2
    unfold Molecule.ends at hx2
    rw [Sym2.eq_iff] at hx2
    have h1 : M.atom x ∉ E ∧ M.atom (M.mate x) ∉ E := by
      rcases hx2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ ha, h2 ▸ hb⟩
      · exact ⟨h1 ▸ hb, h2 ▸ ha⟩
    exact ⟨⟨x, h1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hx, rfl⟩

theorem eraseSet_directed_iff {a b : V} (ha : a ∉ E) (hb : b ∉ E) :
    (eraseSet M E).Directed a b ↔ M.Directed a b := by
  constructor
  · rintro ⟨y, h1, h2, h3⟩
    exact ⟨y.1, h1, h2, h3⟩
  · rintro ⟨x, h1, h2, h3⟩
    exact ⟨⟨x, h2 ▸ ha, h3 ▸ hb⟩, h1, h2, h3⟩

theorem eraseSet_isLadder_iff {m : ℕ} {u w : Fin (m + 1) → V} (hu : ∀ j, u j ∉ E) (hw : ∀ j, w j ∉ E) :
    (eraseSet M E).IsLadder u w ↔ M.IsLadder u w := by
  unfold Molecule.IsLadder
  have mem : ∀ a, a ∉ E → (a ∈ (eraseSet M E).atoms ↔ a ∈ M.atoms) := by
    intro a ha
    show a ∈ M.atoms \ E ↔ _
    simp [ha]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_)))
  · refine forall_congr' fun j => ?_
    rw [mem _ (hu j), mem _ (hw j)]
  · refine forall_congr' fun j => ?_
    rw [eraseSet_bondsBetween M (hu j) (hw j)]
  · refine forall_congr' fun j => ?_
    rw [eraseSet_bondsBetween M (hu _) (hu _), eraseSet_bondsBetween M (hw _) (hw _),
      eraseSet_directed_iff M (hu _) (hu _), eraseSet_directed_iff M (hw _) (hw _)]

theorem eraseSet_isLadderSet_iff {S : Finset V} :
    (eraseSet M E).IsLadderSet S ↔ M.IsLadderSet S ∧ Disjoint S E := by
  constructor
  · rintro ⟨m, u, w, hL, rfl⟩
    have h3 : ∀ a ∈ Molecule.ladderAtoms u w, a ∉ E := by
      intro a ha
      have := ladderAtoms_subset_atoms (eraseSet M E) hL ha
      exact (Finset.mem_sdiff.1 this).2
    have hu : ∀ j, u j ∉ E := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inl rfl⟩)
    have hw : ∀ j, w j ∉ E := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inr rfl⟩)
    exact ⟨⟨m, u, w, (eraseSet_isLadder_iff M hu hw).1 hL, rfl⟩, Finset.disjoint_right.2 fun a hE ha => h3 a ha hE⟩
  · rintro ⟨⟨m, u, w, hL, rfl⟩, hd⟩
    have h3 : ∀ a ∈ Molecule.ladderAtoms u w, a ∉ E := fun a ha hE => Finset.disjoint_left.1 hd ha hE
    have hu : ∀ j, u j ∉ E := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inl rfl⟩)
    have hw : ∀ j, w j ∉ E := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inr rfl⟩)
    exact ⟨m, u, w, (eraseSet_isLadder_iff M hu hw).2 hL, rfl⟩

theorem erase_maximal_of_avoid {S : Finset V} (hS : S ∈ M.maximalLadders) (hd : Disjoint S E) :
    S ∈ (eraseSet M E).maximalLadders := by
  rw [mem_maximalLadders_iff] at hS ⊢
  refine ⟨(eraseSet_isLadderSet_iff M).2 ⟨hS.1, hd⟩, fun S' hS' hsub => ?_⟩
  exact hS.2 S' ((eraseSet_isLadderSet_iff M).1 hS').1 hsub

theorem erase_maximal_sub {S' : Finset V} (hS' : S' ∈ (eraseSet M E).maximalLadders) :
    ∃ S ∈ M.maximalLadders, S' ⊆ S :=
  exists_maximal_ladder_ge M (((eraseSet_isLadderSet_iff M).1 ((mem_maximalLadders_iff _).1 hS').1).1)

theorem isLadderSet_of_erase {S : Finset V} (h : (eraseSet M E).IsLadderSet S) : M.IsLadderSet S :=
  ((eraseSet_isLadderSet_iff M).1 h).1

end WaveTurbulence.FinalCountG3
