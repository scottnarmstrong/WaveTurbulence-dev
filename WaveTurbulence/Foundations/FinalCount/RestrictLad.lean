/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RestrictComp
public import WaveTurbulence.Foundations.FinalCount.CutLad3
/-! Restriction, part 3 (FINALCOUNT-G2 infrastructure): the ladders of `M` are the ladders of the two halves. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LadderDisjoint

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed M P)
include h

theorem restrictP_bondsBetween {a b : V} (ha : P a) (hb : P b) :
    (restrictP M P h).bondsBetween a b = M.bondsBetween a b := by
  unfold Molecule.bondsBetween Molecule.bonds
  rw [Finset.filter_filter, Finset.filter_filter]
  have e := card_filter_subtype' (fun x : D => P (M.atom x)) (fun x => M.out x = true ∧ M.ends x = s(a, b))
  refine e.trans ?_
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hx => hx.2
  · intro hx
    refine ⟨?_, hx⟩
    have : M.atom x = a ∨ M.atom x = b := by
      have h2 := hx.2
      unfold Molecule.ends at h2
      rcases Sym2.eq_iff.mp h2 with ⟨e1, _⟩ | ⟨e1, _⟩
      · exact Or.inl e1
      · exact Or.inr e1
    rcases this with e | e <;> rw [e] <;> assumption

theorem restrictP_directed {a b : V} (ha : P a) (hb : P b) :
    (restrictP M P h).Directed a b ↔ M.Directed a b := by
  unfold Molecule.Directed
  constructor
  · rintro ⟨x, hx1, hx2, hx3⟩
    exact ⟨x.1, hx1, hx2, hx3⟩
  · rintro ⟨x, hx1, hx2, hx3⟩
    exact ⟨⟨x, hx2 ▸ ha⟩, hx1, hx2, hx3⟩


theorem restrictP_isLadder_iff {m : ℕ} {u w : Fin (m + 1) → V} (hu : ∀ j, P (u j)) (hw : ∀ j, P (w j)) :
    (restrictP M P h).IsLadder u w ↔ M.IsLadder u w := by
  unfold Molecule.IsLadder
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_)))
  · refine forall_congr' fun j => ?_
    show (u j ∈ M.atoms.filter P ∧ w j ∈ M.atoms.filter P) ↔ _
    simp only [Finset.mem_filter, hu j, hw j, and_true]
  · refine forall_congr' fun j => ?_
    rw [restrictP_bondsBetween M P h (hu j) (hw j)]
  · refine forall_congr' fun j => ?_
    rw [restrictP_bondsBetween M P h (hu _) (hu _), restrictP_bondsBetween M P h (hw _) (hw _),
      restrictP_directed M P h (hu _) (hu _), restrictP_directed M P h (hw _) (hw _)]

theorem ladder_P_const {m : ℕ} {u w : Fin (m + 1) → V} (hL : M.IsLadder u w) :
    (∀ j, P (u j) ∧ P (w j)) ∨ (∀ j, ¬P (u j) ∧ ¬P (w j)) := by
  obtain ⟨hu, hw, huw⟩ := Sum.elim_injective.mp hL.2.1
  have hrung : ∀ j, P (u j) ↔ P (w j) := by
    intro j
    have hpos : 0 < M.bondsBetween (u j) (w j) := by rw [hL.2.2.2.1 j]; norm_num
    exact PClosed.adj_iff M P h (adj_of_bondsBetween_pos M (fun e => huw j j e) hpos)
  have hrail : ∀ j : Fin m, P (u j.castSucc) ↔ P (u j.succ) := by
    intro j
    have hpos : 0 < M.bondsBetween (u j.castSucc) (u j.succ) := by rw [(hL.2.2.2.2 j).1]; norm_num
    refine PClosed.adj_iff M P h (adj_of_bondsBetween_pos M ?_ hpos)
    intro e
    have := hu e
    have := congrArg Fin.val this
    simp at this
  have hall : ∀ n (hn : n < m + 1), P (u ⟨n, hn⟩) ↔ P (u 0) := by
    intro n
    induction n with
    | zero => intro hn; exact Iff.rfl
    | succ n ih =>
      intro hn
      have h1 := hrail ⟨n, by omega⟩
      have h2 := ih (by omega)
      simp only [Fin.castSucc_mk, Fin.succ_mk] at h1
      exact h1.symm.trans h2
  by_cases h0 : P (u 0)
  · left
    intro j
    have := (hall j.val j.isLt).2 h0
    have hj : u j = u ⟨j.val, j.isLt⟩ := rfl
    exact ⟨this, (hrung j).1 this⟩
  · right
    intro j
    have hj := hall j.val j.isLt
    have : ¬ P (u j) := fun hp => h0 (hj.1 hp)
    exact ⟨this, fun hp => this ((hrung j).2 hp)⟩


theorem restrictP_isLadderSet_iff {S : Finset V} (hS : ∀ a ∈ S, P a) :
    (restrictP M P h).IsLadderSet S ↔ M.IsLadderSet S := by
  constructor
  · rintro ⟨m, u, w, hL, rfl⟩
    have hu : ∀ j, P (u j) := fun j => hS _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inl rfl⟩)
    have hw : ∀ j, P (w j) := fun j => hS _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inr rfl⟩)
    exact ⟨m, u, w, (restrictP_isLadder_iff M P h hu hw).1 hL, rfl⟩
  · rintro ⟨m, u, w, hL, rfl⟩
    have hu : ∀ j, P (u j) := fun j => hS _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inl rfl⟩)
    have hw : ∀ j, P (w j) := fun j => hS _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inr rfl⟩)
    exact ⟨m, u, w, (restrictP_isLadder_iff M P h hu hw).2 hL, rfl⟩

theorem isLadderSet_cases {S : Finset V} (hS : M.IsLadderSet S) : (∀ a ∈ S, P a) ∨ (∀ a ∈ S, ¬P a) := by
  obtain ⟨m, u, w, hL, rfl⟩ := hS
  rcases ladder_P_const M P h hL with H | H
  · left
    intro a ha
    obtain ⟨j, hj | hj⟩ := (mem_ladderAtoms u w a).1 ha
    · exact hj ▸ (H j).1
    · exact hj ▸ (H j).2
  · right
    intro a ha
    obtain ⟨j, hj | hj⟩ := (mem_ladderAtoms u w a).1 ha
    · exact hj ▸ (H j).1
    · exact hj ▸ (H j).2

omit h in
theorem isLadderSet_nonempty {S : Finset V} (hS : M.IsLadderSet S) : S.Nonempty := by
  obtain ⟨m, u, w, hL, rfl⟩ := hS
  rw [← Finset.card_pos, card_ladderAtoms M hL]; omega

theorem restrictP_maximal_iff {S : Finset V} :
    S ∈ (restrictP M P h).maximalLadders ↔ S ∈ M.maximalLadders ∧ (∀ a ∈ S, P a) := by
  rw [mem_maximalLadders_iff, mem_maximalLadders_iff]
  constructor
  · rintro ⟨hS, hmax⟩
    have hP : ∀ a ∈ S, P a := fun a ha => (restrictP_atom_mem M P h (isLadderSet_subset _ hS ha)).2
    refine ⟨⟨(restrictP_isLadderSet_iff M P h hP).1 hS, fun S' hS' hsub => ?_⟩, hP⟩
    rcases isLadderSet_cases M P h hS' with H | H
    · exact hmax S' ((restrictP_isLadderSet_iff M P h H).2 hS') hsub
    · obtain ⟨a, ha⟩ := isLadderSet_nonempty _ ((restrictP_isLadderSet_iff M P h hP).1 hS)
      exact absurd (hP a ha) (H a (hsub ha))
  · rintro ⟨⟨hS, hmax⟩, hP⟩
    refine ⟨(restrictP_isLadderSet_iff M P h hP).2 hS, fun S' hS' hsub => ?_⟩
    have hP' : ∀ a ∈ S', P a := fun a ha => (restrictP_atom_mem M P h (isLadderSet_subset _ hS' ha)).2
    exact hmax S' ((restrictP_isLadderSet_iff M P h hP').1 hS') hsub

/-- **The maximal ladders split.** -/
theorem maximalLadders_restrict_union :
    M.maximalLadders = (restrictP M P h).maximalLadders ∪ (restrictP M (fun a => ¬ P a) h.neg).maximalLadders := by
  ext S
  rw [Finset.mem_union, restrictP_maximal_iff, restrictP_maximal_iff]
  constructor
  · intro hS
    have hS' := (mem_maximalLadders_iff M).1 hS
    rcases isLadderSet_cases M P h hS'.1 with H | H
    · exact Or.inl ⟨hS, H⟩
    · exact Or.inr ⟨hS, H⟩
  · rintro (H | H) <;> exact H.1

theorem maximalLadders_restrict_disjoint :
    Disjoint (restrictP M P h).maximalLadders (restrictP M (fun a => ¬ P a) h.neg).maximalLadders := by
  rw [Finset.disjoint_left]
  intro S h1 h2
  rw [restrictP_maximal_iff] at h1 h2
  obtain ⟨a, ha⟩ := isLadderSet_nonempty M ((mem_maximalLadders_iff M).1 h1.1).1
  exact h2.2 a ha (h1.2 a ha)

end WaveTurbulence.FinalCount
