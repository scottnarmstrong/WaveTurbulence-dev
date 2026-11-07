/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Multi
public import WaveTurbulence.Foundations.Molecule.VineExpansionSequences
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
public import WaveTurbulence.Foundations.Molecule.VineInsertionCounts
public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic

/-! # The inserted-rung ladders of a vine realization (TARGET layervine, L1519)

Every slot of a vine template carries a `FullRungSequence` of its `k` inserted rungs
(`VineRealization.has_rungSequence`); the atoms of different slots have different template labels, hence are
distinct; the remaining atoms of the vine are exactly the base template atoms (at most `15`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
  {S : Finset V} {a b : V}

theorem template_slots_le (X : VineType) : X.template.slots.length ≤ 3 := by
  cases X <;> simp [VineType.template]

theorem template_n_le (X : VineType) : X.template.n ≤ 15 := by
  cases X <;> simp [VineType.template]

theorem template_n_ge (X : VineType) : 2 ≤ X.template.n ∧ (X.IsBad = false → 9 ≤ X.template.n) := by
  cases X <;> simp [VineType.template, VineType.IsBad]

/-- Slot data `(slot, k)` zipped. -/
@[expose] def slotZip (R : VineRealization M X S a b) : List (((ℕ × ℕ) × ℕ × ℕ) × ℕ) :=
  X.template.slots.zip R.k

theorem slotZip_length (R : VineRealization M X S a b) : (slotZip R).length = X.template.slots.length := by
  unfold slotZip; rw [List.length_zip, R.length_eq, min_self]

/-- Number of rungs at slot `c`. -/
@[expose] def kSlot (R : VineRealization M X S a b) (c : Fin X.template.slots.length) : ℕ :=
  ((slotZip R)[c.1]'(by rw [slotZip_length]; exact c.2)).2

/-- First label of the inserted atoms at slot `c`. -/
@[expose] def offSlot (R : VineRealization M X S a b) (c : Fin X.template.slots.length) : ℕ :=
  X.template.n + 2 * (((slotZip R).take c.1).map Prod.snd).sum

theorem exists_slotSeq (R : VineRealization M X S a b) (c : Fin X.template.slots.length) :
    ∃ Q : FullRungSequence M (kSlot R c), ∀ i, 1 ≤ i → i ≤ kSlot R c →
      Q.u i ∈ S ∧ Q.v i ∈ S ∧ R.f (Q.u i) = offSlot R c + (i - 1) ∧
        R.f (Q.v i) = offSlot R c + kSlot R c + (i - 1) := by
  have hc : c.1 < (slotZip R).length := by rw [slotZip_length]; exact c.2
  have hloc : X.template.slots.zip R.k =
      (slotZip R).take c.1 ++ ((slotZip R)[c.1]'hc) :: (slotZip R).drop (c.1 + 1) := by
    change slotZip R = _
    rw [← List.drop_eq_getElem_cons hc, List.take_append_drop]
  obtain ⟨Q, hQ⟩ := R.has_rungSequence ((slotZip R).take c.1) ((slotZip R).drop (c.1 + 1))
    ((slotZip R)[c.1]'hc).1 ((slotZip R)[c.1]'hc).2 hloc
  refine ⟨Q, ?_⟩
  intro i hi1 hi2
  have := hQ i hi1 hi2
  simp only [fold_insertRungs_atoms] at this
  exact this

/-- The rung list `ls = [k_1, …, k_L]`. -/
@[expose] def kList (R : VineRealization M X S a b) : List ℕ := (slotZip R).map Prod.snd

theorem kList_length (R : VineRealization M X S a b) : (kList R).length = X.template.slots.length := by
  unfold kList; rw [List.length_map, slotZip_length]

theorem kSlot_eq (R : VineRealization M X S a b) (c : Fin X.template.slots.length) :
    kSlot R c = (kList R)[c.1]'(by rw [kList_length]; exact c.2) := by
  unfold kSlot; simp only [kList, List.getElem_map]

theorem offSlot_eq (R : VineRealization M X S a b) (c : Fin X.template.slots.length) :
    offSlot R c = X.template.n + 2 * ((kList R).take c.1).sum := by
  unfold offSlot kList; rw [List.map_take]

theorem take_sum_mono (l : List ℕ) {i j : ℕ} (h : i ≤ j) : (l.take i).sum ≤ (l.take j).sum := by
  have := List.sum_take_add_sum_drop (l.take j) i
  rw [List.take_take, min_eq_left h] at this
  omega

theorem offSlot_mono (R : VineRealization M X S a b) {c c' : Fin X.template.slots.length} (h : c < c') :
    offSlot R c + 2 * kSlot R c ≤ offSlot R c' := by
  rw [offSlot_eq, offSlot_eq, kSlot_eq]
  have hc : c.1 < (kList R).length := by rw [kList_length]; exact c.2
  have h1 := List.sum_take_succ (kList R) c.1 hc
  have h2 := take_sum_mono (kList R) (show c.1 + 1 ≤ c'.1 from h)
  omega

/-- The chosen rung sequence at slot `c`. -/
@[expose] noncomputable def slotQ (R : VineRealization M X S a b) (c : Fin X.template.slots.length) :
    FullRungSequence M (kSlot R c) := Classical.choose (exists_slotSeq R c)

theorem slotQ_spec (R : VineRealization M X S a b) (c : Fin X.template.slots.length) :
    ∀ i, 1 ≤ i → i ≤ kSlot R c →
      (slotQ R c).u i ∈ S ∧ (slotQ R c).v i ∈ S ∧ R.f ((slotQ R c).u i) = offSlot R c + (i - 1) ∧
        R.f ((slotQ R c).v i) = offSlot R c + kSlot R c + (i - 1) := Classical.choose_spec (exists_slotSeq R c)

theorem slotInt_sub (R : VineRealization M X S a b) (c : Fin X.template.slots.length) :
    intAtoms (slotQ R c).u (slotQ R c).v (kSlot R c) ⊆ S := by
  intro x hx
  unfold intAtoms at hx
  simp only [mem_union, mem_image, mem_Ico] at hx
  rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact (slotQ_spec R c i (by omega) (by omega)).1
  · exact (slotQ_spec R c i (by omega) (by omega)).2.1

theorem slotInt_label (R : VineRealization M X S a b) (c : Fin X.template.slots.length) {x : V}
    (hx : x ∈ intAtoms (slotQ R c).u (slotQ R c).v (kSlot R c)) :
    offSlot R c ≤ R.f x ∧ R.f x < offSlot R c + 2 * kSlot R c := by
  unfold intAtoms at hx
  simp only [mem_union, mem_image, mem_Ico] at hx
  rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · have := (slotQ_spec R c i (by omega) (by omega)).2.2.1
    omega
  · have := (slotQ_spec R c i (by omega) (by omega)).2.2.2
    omega

theorem slotInt_disjoint (R : VineRealization M X S a b) {c c' : Fin X.template.slots.length}
    (h : c ≠ c') : Disjoint (intAtoms (slotQ R c).u (slotQ R c).v (kSlot R c))
      (intAtoms (slotQ R c').u (slotQ R c').v (kSlot R c')) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have h1 := slotInt_label R c hx
  have h2 := slotInt_label R c' hx'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have := offSlot_mono R hlt; omega
  · have := offSlot_mono R hlt; omega

theorem sum_kSlot (R : VineRealization M X S a b) :
    ∑ c : Fin X.template.slots.length, kSlot R c = (kList R).sum := by
  rw [← Fin.sum_univ_getElem (kList R)]
  apply Fintype.sum_equiv (finCongr (kList_length R).symm)
  intro c
  rw [kSlot_eq]; rfl

theorem card_slotInt (R : VineRealization M X S a b) (c : Fin X.template.slots.length) :
    (intAtoms (slotQ R c).u (slotQ R c).v (kSlot R c)).card = 2 * kSlot R c := by
  unfold intAtoms
  rw [Finset.card_union_of_disjoint (intAtoms_disjoint M (slotQ R c)),
    Finset.card_image_of_injOn (u_injOn M (slotQ R c)), Finset.card_image_of_injOn (v_injOn M (slotQ R c))]
  simp; ring

theorem card_allInt (R : VineRealization M X S a b) :
    (allInt M (slotQ R)).card = 2 * (kList R).sum := by
  unfold allInt
  rw [Finset.card_biUnion (fun c _ c' _ h => slotInt_disjoint R h)]
  simp only [card_slotInt]
  rw [← sum_kSlot, Finset.mul_sum]

theorem card_S (R : VineRealization M X S a b) : S.card = X.template.n + 2 * (kList R).sum := by
  have h1 : S.card = (X.expand R.k).n := by
    rw [← Finset.card_range (X.expand R.k).n, ← R.image_eq, Finset.card_image_of_injOn R.injOn]
  rw [h1, expand_atoms]
  rfl

theorem allInt_sub (R : VineRealization M X S a b) : allInt M (slotQ R) ⊆ S := by
  intro x hx
  unfold allInt at hx
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hx
  exact slotInt_sub R c hc

theorem card_rest (R : VineRealization M X S a b) : (S \ allInt M (slotQ R)).card = X.template.n := by
  rw [Finset.card_sdiff_of_subset (allInt_sub R), card_allInt R, card_S R]
  omega

end WaveTurbulence.LayerCnt
