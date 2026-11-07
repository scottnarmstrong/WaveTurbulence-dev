/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.Step0Y1c3
import Mathlib.Tactic

/-! # Merging the two atoms of a double bond (DH23 Prop 10.4(2), case (IV))

DH23 L1977: "we merge the two atoms `(v₁, v₂)` into one atom which has bonds `(ℓ₃, …, ℓ₆)`". `mergePair M v₁ v₂` drops
every bond between `v₁` and `v₂` and renames `v₂` to `v₁`. Its darts are the darts of `𝕄` off those bonds, and a
decoration of `𝕄` restricts to one of the merged molecule.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The darts off the bonds between `v₁` and `v₂`. -/
abbrev OffPair (M : Molecule V D) (v₁ v₂ : V) := {x : D // M.ends x ≠ s(v₁, v₂)}

/-- The renaming `v₂ ↦ v₁`. -/
def mergeMap (v₁ v₂ : V) (u : V) : V := if u = v₂ then v₁ else u

/-- **Merge `v₂` into `v₁`**, dropping the bonds between them. -/
def mergePair (M : Molecule V D) (v₁ v₂ : V) (hv₁ : v₁ ∈ M.atoms) (hne : v₁ ≠ v₂) :
    Molecule V (OffPair M v₁ v₂) where
  atoms := M.atoms.erase v₂
  atom x := mergeMap v₁ v₂ (M.atom x.val)
  mate x := ⟨M.mate x.val, by rw [ends_mate M]; exact x.property⟩
  out x := M.out x.val
  atom_mem x := by
    unfold mergeMap
    by_cases h : M.atom x.val = v₂
    · rw [ite_of_pos h]; exact mem_erase.mpr ⟨hne, hv₁⟩
    · rw [ite_of_not h]; exact mem_erase.mpr ⟨h, M.atom_mem _⟩
  mate_mate x := Subtype.ext (M.mate_mate x.val)
  mate_ne x h := M.mate_ne x.val (congrArg Subtype.val h)
  out_mate x := M.out_mate x.val

namespace Merge
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

omit [Fintype D] [DecidableEq D] in
theorem mergeMap_eq_v₁ {u : V} : mergeMap v₁ v₂ u = v₁ ↔ u = v₁ ∨ u = v₂ := by
  unfold mergeMap
  by_cases h : u = v₂
  · rw [ite_of_pos h]; exact ⟨fun _ => Or.inr h, fun _ => rfl⟩
  · rw [ite_of_not h]; exact ⟨Or.inl, fun h' => h'.resolve_right h⟩

omit [Fintype D] [DecidableEq D] in
theorem mergeMap_of_ne {u : V} (h : u ≠ v₂) : mergeMap v₁ v₂ u = u := by
  unfold mergeMap; rw [ite_of_not h]

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- A dart at `v₁` is a pair dart iff its other end is `v₂`. -/
theorem ends_eq_pair_iff (hne : v₁ ≠ v₂) {x : D} (hx : M.atom x = v₁) :
    M.ends x = s(v₁, v₂) ↔ M.atom (M.mate x) = v₂ := by
  unfold Molecule.ends
  rw [hx]
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd h1 hne
  · intro h; rw [h]

omit [DecidableEq D] in
/-- Counting darts of the merged molecule by a property of the underlying dart. -/
theorem card_filter_val (Q : D → Prop) [DecidablePred Q] :
    ((univ : Finset (OffPair M v₁ v₂)).filter fun x => Q x.val).card =
      (univ.filter fun x => M.ends x ≠ s(v₁, v₂) ∧ Q x).card := by
  refine card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _, x.property, (mem_filter.mp hx).2⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro x hx
    obtain ⟨_, h1, h2⟩ := mem_filter.mp hx
    exact ⟨⟨x, h1⟩, mem_filter.mpr ⟨mem_univ _, h2⟩, rfl⟩

omit [Fintype D] [DecidableEq D] in
theorem atoms_eq : (mergePair M v₁ v₂ hv₁ hne).atoms = M.atoms.erase v₂ := rfl

omit [Fintype D] [DecidableEq D] in
theorem atom_eq (x : OffPair M v₁ v₂) : (mergePair M v₁ v₂ hv₁ hne).atom x = mergeMap v₁ v₂ (M.atom x.val) := rfl

omit [Fintype D] [DecidableEq D] in
theorem mate_val (x : OffPair M v₁ v₂) : ((mergePair M v₁ v₂ hv₁ hne).mate x).val = M.mate x.val := rfl

omit [Fintype D] [DecidableEq D] in
theorem out_eq (x : OffPair M v₁ v₂) : (mergePair M v₁ v₂ hv₁ hne).out x = M.out x.val := rfl

omit [Fintype D] [DecidableEq D] in
theorem card_atoms (hv₂ : v₂ ∈ M.atoms) : (mergePair M v₁ v₂ hv₁ hne).atoms.card + 1 = M.atoms.card := by
  rw [atoms_eq, card_erase_of_mem hv₂]
  have := card_pos.mpr ⟨v₂, hv₂⟩
  omega

omit [DecidableEq D] in
/-- Darts at a far atom are unchanged. -/
theorem card_filter_of_ne (Q : D → Prop) [DecidablePred Q] {y : V} (h1 : y ≠ v₁) (h2 : y ≠ v₂) :
    ((univ : Finset (OffPair M v₁ v₂)).filter fun x => (mergePair M v₁ v₂ hv₁ hne).atom x = y ∧ Q x.val).card =
      (univ.filter fun x => M.atom x = y ∧ Q x).card := by
  classical
  have hQ : ∀ x : OffPair M v₁ v₂, (mergePair M v₁ v₂ hv₁ hne).atom x = y ↔ M.atom x.val = y := by
    intro x
    rw [atom_eq]
    by_cases hx : M.atom x.val = v₂
    · rw [hx, mergeMap, ite_of_pos rfl]; exact ⟨fun h => absurd h.symm h1, fun h => absurd h.symm h2⟩
    · rw [mergeMap_of_ne hx]
  simp_rw [hQ]
  rw [card_filter_val (fun x => M.atom x = y ∧ Q x)]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
  rintro ⟨hx, _⟩ h
  have hm : M.atom x ∈ M.ends x := Sym2.mem_mk_left _ _
  rw [h, hx] at hm
  rcases Sym2.mem_iff.mp hm with h' | h'
  · exact h1 h'
  · exact h2 h'

omit [DecidableEq D] in
theorem deg_of_ne {y : V} (h1 : y ≠ v₁) (h2 : y ≠ v₂) :
    (mergePair M v₁ v₂ hv₁ hne).deg y = M.deg y := by
  classical
  have h := card_filter_of_ne (M := M) (hv₁ := hv₁) (hne := hne) (fun _ => True) h1 h2
  simp only [and_true] at h
  exact h

omit [DecidableEq D] in
theorem outdeg_of_ne {y : V} (h1 : y ≠ v₁) (h2 : y ≠ v₂) :
    (mergePair M v₁ v₂ hv₁ hne).outdeg y = M.outdeg y := by
  classical
  have h := card_filter_of_ne (M := M) (hv₁ := hv₁) (hne := hne) (fun x => M.out x = true) h1 h2
  unfold Molecule.outdeg Molecule.dartsAt
  rw [filter_filter, filter_filter]
  exact h

omit [DecidableEq D] in
theorem indeg_of_ne {y : V} (h1 : y ≠ v₁) (h2 : y ≠ v₂) :
    (mergePair M v₁ v₂ hv₁ hne).indeg y = M.indeg y := by
  classical
  have h := card_filter_of_ne (M := M) (hv₁ := hv₁) (hne := hne) (fun x => M.out x = false) h1 h2
  unfold Molecule.indeg Molecule.dartsAt
  rw [filter_filter, filter_filter]
  exact h

/-- The darts at the merged atom, filtered by a predicate `Q` on darts: those at `v₁` or `v₂` off the pair. -/
theorem card_at_v₁ (Q : D → Prop) [DecidablePred Q] :
    ((univ : Finset (OffPair M v₁ v₂)).filter fun x => (mergePair M v₁ v₂ hv₁ hne).atom x = v₁ ∧ Q x.val).card +
        ((univ.filter fun x => M.atom x = v₁ ∧ M.atom (M.mate x) = v₂ ∧ Q x).card +
          (univ.filter fun x => M.atom x = v₂ ∧ M.atom (M.mate x) = v₁ ∧ Q x).card) =
      (univ.filter fun x => M.atom x = v₁ ∧ Q x).card + (univ.filter fun x => M.atom x = v₂ ∧ Q x).card := by
  classical
  have h1 : ((univ : Finset (OffPair M v₁ v₂)).filter fun x =>
      (mergePair M v₁ v₂ hv₁ hne).atom x = v₁ ∧ Q x.val).card =
      (univ.filter fun x => M.ends x ≠ s(v₁, v₂) ∧ ((M.atom x = v₁ ∨ M.atom x = v₂) ∧ Q x)).card := by
    simp_rw [atom_eq, mergeMap_eq_v₁]
    exact card_filter_val (fun x => (M.atom x = v₁ ∨ M.atom x = v₂) ∧ Q x)
  have hsplit : (univ.filter fun x => M.atom x = v₁ ∧ Q x).card + (univ.filter fun x => M.atom x = v₂ ∧ Q x).card =
      (univ.filter fun x : D => (M.atom x = v₁ ∨ M.atom x = v₂) ∧ Q x).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext x; simp only [mem_union, mem_filter, mem_univ, true_and]; tauto
    · rw [disjoint_filter]; rintro x _ ⟨h, _⟩ ⟨h', _⟩; exact hne (h.symm.trans h')
  have h2 := card_filter_add_card_filter_not (s := univ.filter fun x : D => (M.atom x = v₁ ∨ M.atom x = v₂) ∧ Q x)
    (fun x => M.ends x ≠ s(v₁, v₂))
  rw [filter_filter, filter_filter] at h2
  have h3 : (univ.filter fun x : D => ((M.atom x = v₁ ∨ M.atom x = v₂) ∧ Q x) ∧ M.ends x ≠ s(v₁, v₂)).card =
      (univ.filter fun x => M.ends x ≠ s(v₁, v₂) ∧ ((M.atom x = v₁ ∨ M.atom x = v₂) ∧ Q x)).card := by
    congr 1; ext x; simp only [mem_filter, mem_univ, true_and]; tauto
  have h4 : (univ.filter fun x : D => ((M.atom x = v₁ ∨ M.atom x = v₂) ∧ Q x) ∧ ¬ M.ends x ≠ s(v₁, v₂)).card =
      (univ.filter fun x => M.atom x = v₁ ∧ M.atom (M.mate x) = v₂ ∧ Q x).card +
        (univ.filter fun x => M.atom x = v₂ ∧ M.atom (M.mate x) = v₁ ∧ Q x).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      simp only [mem_union, mem_filter, mem_univ, true_and, not_not]
      constructor
      · rintro ⟨⟨h1 | h1, hq⟩, h⟩
        · exact Or.inl ⟨h1, (ends_eq_pair_iff hne h1).mp h, hq⟩
        · right
          refine ⟨h1, ?_, hq⟩
          have h' : M.ends x = s(v₂, v₁) := by rw [h]; exact Sym2.eq_swap
          exact (ends_eq_pair_iff hne.symm h1).mp h'
      · rintro (⟨h1, h2, hq⟩ | ⟨h1, h2, hq⟩)
        · exact ⟨⟨Or.inl h1, hq⟩, (ends_eq_pair_iff hne h1).mpr h2⟩
        · refine ⟨⟨Or.inr h1, hq⟩, ?_⟩
          unfold Molecule.ends; rw [h1, h2]; exact Sym2.eq_swap
    · rw [disjoint_filter]; rintro x _ ⟨h, _⟩ ⟨h', _⟩; exact hne (h.symm.trans h')
  omega

omit [DecidableEq D] in
theorem dartsAt_card_filter (v : V) (Q : D → Prop) [DecidablePred Q] :
    ((M.dartsAt v).filter Q).card = (univ.filter fun x => M.atom x = v ∧ Q x).card := by
  unfold Molecule.dartsAt; rw [filter_filter]

/-- The pair bonds, by their outgoing dart. -/
theorem pair_bonds_card (hne : v₁ ≠ v₂) : M.bondsBetween v₁ v₂ =
    (univ.filter fun x => M.atom x = v₁ ∧ M.atom (M.mate x) = v₂ ∧ M.out x = true).card +
      (univ.filter fun x => M.atom x = v₂ ∧ M.atom (M.mate x) = v₁ ∧ M.out x = true).card := by
  unfold Molecule.bondsBetween Molecule.bonds
  rw [filter_filter, ← card_union_of_disjoint]
  · congr 1; ext x
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨ho, he⟩
      have hm : M.atom x ∈ M.ends x := Sym2.mem_mk_left _ _
      rw [he] at hm
      rcases Sym2.mem_iff.mp hm with h1 | h1
      · exact Or.inl ⟨h1, (ends_eq_pair_iff hne h1).mp he, ho⟩
      · exact Or.inr ⟨h1, (ends_eq_pair_iff hne.symm h1).mp (by rw [he]; exact Sym2.eq_swap), ho⟩
    · rintro (⟨h1, h2, ho⟩ | ⟨h1, h2, ho⟩)
      · exact ⟨ho, (ends_eq_pair_iff hne h1).mpr h2⟩
      · refine ⟨ho, ?_⟩; unfold Molecule.ends; rw [h1, h2]; exact Sym2.eq_swap
  · rw [disjoint_filter]; rintro x _ ⟨h, _⟩ ⟨h', _⟩; exact hne (h.symm.trans h')

omit [DecidableEq D] in
/-- Incoming pair darts are the mates of outgoing ones. -/
theorem pair_in_card (a b : V) :
    (univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b ∧ M.out x = false).card =
      (univ.filter fun x => M.atom x = b ∧ M.atom (M.mate x) = a ∧ M.out x = true).card := by
  refine card_bij (fun x _ => M.mate x) ?_ ?_ ?_
  · intro x hx
    obtain ⟨_, h1, h2, h3⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨mem_univ _, h2, by rw [M.mate_mate]; exact h1, ?_⟩
    rw [M.out_mate, h3]; rfl
  · intro x _ y _ h; have := congrArg M.mate h; rwa [M.mate_mate, M.mate_mate] at this
  · intro x hx
    obtain ⟨_, h1, h2, h3⟩ := mem_filter.mp hx
    refine ⟨M.mate x, mem_filter.mpr ⟨mem_univ _, h2, by rw [M.mate_mate]; exact h1, ?_⟩, M.mate_mate x⟩
    rw [M.out_mate, h3]; rfl

/-- **Degree of the merged atom**: `deg' v₁ + 2·bb(v₁, v₂) = deg v₁ + deg v₂`. -/
theorem deg_v₁ : (mergePair M v₁ v₂ hv₁ hne).deg v₁ + 2 * M.bondsBetween v₁ v₂ = M.deg v₁ + M.deg v₂ := by
  classical
  have h := card_at_v₁ (M := M) (hv₁ := hv₁) (hne := hne) (fun _ => True)
  simp only [and_true] at h
  have hb := pair_bonds_card (M := M) hne
  have hi1 := pair_in_card (M := M) v₁ v₂
  have hi2 := pair_in_card (M := M) v₂ v₁
  have hs : ∀ a b : V, (univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b).card =
      (univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b ∧ M.out x = true).card +
        (univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b ∧ M.out x = false).card := by
    intro a b
    rw [← card_union_of_disjoint]
    · congr 1; ext x; simp only [mem_filter, mem_univ, true_and, mem_union]
      cases M.out x <;> simp
    · rw [disjoint_filter]; rintro x _ ⟨_, _, h⟩ ⟨_, _, h'⟩; rw [h] at h'; exact Bool.noConfusion h'
  have hs1 := hs v₁ v₂
  have hs2 := hs v₂ v₁
  have e1 : (mergePair M v₁ v₂ hv₁ hne).deg v₁ =
      ((univ : Finset (OffPair M v₁ v₂)).filter fun x => (mergePair M v₁ v₂ hv₁ hne).atom x = v₁).card := rfl
  have e2 : M.deg v₁ = (univ.filter fun x => M.atom x = v₁).card := rfl
  have e3 : M.deg v₂ = (univ.filter fun x => M.atom x = v₂).card := rfl
  omega

/-- **Out-degree of the merged atom.** -/
theorem outdeg_v₁ : (mergePair M v₁ v₂ hv₁ hne).outdeg v₁ + M.bondsBetween v₁ v₂ = M.outdeg v₁ + M.outdeg v₂ := by
  classical
  have h := card_at_v₁ (M := M) (hv₁ := hv₁) (hne := hne) (fun x => M.out x = true)
  have hb := pair_bonds_card (M := M) hne
  have e1 : (mergePair M v₁ v₂ hv₁ hne).outdeg v₁ =
      ((univ : Finset (OffPair M v₁ v₂)).filter fun x =>
        (mergePair M v₁ v₂ hv₁ hne).atom x = v₁ ∧ M.out x.val = true).card := by
    unfold Molecule.outdeg Molecule.dartsAt; rw [filter_filter]; rfl
  have e2 : M.outdeg v₁ = (univ.filter fun x => M.atom x = v₁ ∧ M.out x = true).card := dartsAt_card_filter _ _
  have e3 : M.outdeg v₂ = (univ.filter fun x => M.atom x = v₂ ∧ M.out x = true).card := dartsAt_card_filter _ _
  omega

/-- **In-degree of the merged atom.** -/
theorem indeg_v₁ : (mergePair M v₁ v₂ hv₁ hne).indeg v₁ + M.bondsBetween v₁ v₂ = M.indeg v₁ + M.indeg v₂ := by
  classical
  have h := card_at_v₁ (M := M) (hv₁ := hv₁) (hne := hne) (fun x => M.out x = false)
  have hb := pair_bonds_card (M := M) hne
  rw [← pair_in_card, ← pair_in_card] at hb
  have e1 : (mergePair M v₁ v₂ hv₁ hne).indeg v₁ =
      ((univ : Finset (OffPair M v₁ v₂)).filter fun x =>
        (mergePair M v₁ v₂ hv₁ hne).atom x = v₁ ∧ M.out x.val = false).card := by
    unfold Molecule.indeg Molecule.dartsAt; rw [filter_filter]; rfl
  have e2 : M.indeg v₁ = (univ.filter fun x => M.atom x = v₁ ∧ M.out x = false).card := dartsAt_card_filter _ _
  have e3 : M.indeg v₂ = (univ.filter fun x => M.atom x = v₂ ∧ M.out x = false).card := dartsAt_card_filter _ _
  omega

omit [Fintype D] [DecidableEq D] in
/-- **No loops** after merging, if `𝕄` has none and `v₁, v₂` are joined only by the dropped bonds. -/
theorem loopFree (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) :
    ∀ z, (mergePair M v₁ v₂ hv₁ hne).atom z ≠ (mergePair M v₁ v₂ hv₁ hne).atom ((mergePair M v₁ v₂ hv₁ hne).mate z) := by
  intro z h
  rw [atom_eq, atom_eq, mate_val] at h
  have hz := z.property
  by_cases h1 : M.atom z.val = v₂
  · by_cases h2 : M.atom (M.mate z.val) = v₂
    · exact hloop z.val (h1.trans h2.symm)
    · rw [h1, mergeMap, ite_of_pos rfl, mergeMap_of_ne h2] at h
      apply hz; unfold Molecule.ends; rw [h1, ← h]; exact Sym2.eq_swap
  · rw [mergeMap_of_ne h1] at h
    by_cases h2 : M.atom (M.mate z.val) = v₂
    · rw [h2, mergeMap, ite_of_pos rfl] at h
      apply hz; unfold Molecule.ends; rw [h, h2]
    · rw [mergeMap_of_ne h2] at h
      exact hloop z.val h

omit [Fintype D] [DecidableEq D] in
/-- Paths survive merging (images under `v₂ ↦ v₁`). -/
theorem sameComponent_map {a b : V} (h : M.SameComponent a b) :
    (mergePair M v₁ v₂ hv₁ hne).SameComponent (mergeMap v₁ v₂ a) (mergeMap v₁ v₂ b) := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    by_cases hz : M.ends z = s(v₁, v₂)
    · have : mergeMap v₁ v₂ (M.atom z) = mergeMap v₁ v₂ (M.atom (M.mate z)) := by
        have h1 : M.atom z = v₁ ∨ M.atom z = v₂ := by
          have hm : M.atom z ∈ M.ends z := Sym2.mem_mk_left _ _
          rw [hz] at hm; exact Sym2.mem_iff.mp hm
        have h2 : M.atom (M.mate z) = v₁ ∨ M.atom (M.mate z) = v₂ := by
          have hm : M.atom (M.mate z) ∈ M.ends z := Sym2.mem_mk_right _ _
          rw [hz] at hm; exact Sym2.mem_iff.mp hm
        rw [mergeMap_eq_v₁.mpr h1, mergeMap_eq_v₁.mpr h2]
      rw [this]; exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ ⟨⟨z, hz⟩, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

omit [Fintype D] [DecidableEq D] in
/-- **Connectivity** survives merging. -/
theorem connected (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    ∀ u ∈ (mergePair M v₁ v₂ hv₁ hne).atoms, ∀ v ∈ (mergePair M v₁ v₂ hv₁ hne).atoms,
      (mergePair M v₁ v₂ hv₁ hne).SameComponent u v := by
  intro u hu v hv
  rw [atoms_eq] at hu hv
  have h := sameComponent_map (hv₁ := hv₁) (hne := hne) (hconn u (mem_of_mem_erase hu) v (mem_of_mem_erase hv))
  rwa [mergeMap_of_ne (ne_of_mem_erase hu), mergeMap_of_ne (ne_of_mem_erase hv)] at h

end Merge

end WaveTurbulence.MoleProp4
