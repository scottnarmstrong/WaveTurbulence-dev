/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3InvDel
/-! **FINALCOUNT-G3: erasing an atom** (TARGET Remark `remtame` case (ii), L2152: "we then remove `v` without
assigning any new `α`- or `β`-atoms").  `eraseAt M v` is the molecule on the atoms other than `v`, with the darts of
the bonds not touching `v`.  Degree formula, dart count, and the comparison of the connected components of `M` and of
`M - v`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V)

/-- The darts of the bonds not touching `v`. -/
abbrev EDart := {x : D // M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v}

/-- The molecule `M - v`. -/
def eraseAt : Molecule V (EDart M v) where
  atoms := M.atoms.erase v
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1, by rw [M.mate_mate]; exact ⟨x.2.2, x.2.1⟩⟩
  out := fun x => M.out x.1
  atom_mem := fun x => Finset.mem_erase.mpr ⟨x.2.1, M.atom_mem x.1⟩
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x e => M.mate_ne x.1 (congrArg Subtype.val e)
  out_mate := fun x => M.out_mate x.1

/-- The number of darts at `a` whose bond goes to `v`. -/
noncomputable def mult (a : V) : ℕ := ((M.dartsAt a).filter fun x => M.atom (M.mate x) = v).card

theorem eraseAt_atoms : (eraseAt M v).atoms = M.atoms.erase v := rfl

theorem eraseAt_dartsAt_card {a : V} (ha : a ≠ v) :
    (eraseAt M v).deg a + mult M v a = M.deg a := by
  have h1 : (eraseAt M v).deg a =
      (Finset.univ.filter fun x : D => (M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v) ∧ M.atom x = a).card := by
    unfold Molecule.deg Molecule.dartsAt
    exact card_filter_subtype' (fun x : D => M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v) (fun x => M.atom x = a)
  have h2 : (Finset.univ.filter fun x : D => (M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v) ∧ M.atom x = a) =
      (M.dartsAt a).filter fun x => ¬ M.atom (M.mate x) = v := by
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨⟨h' ▸ ha, h⟩, h'⟩
  rw [h1, h2]
  unfold mult Molecule.deg
  rw [add_comm]
  exact Finset.card_filter_add_card_filter_not (s := M.dartsAt a) _

theorem eraseAt_sum {a : V} (ha : a ≠ v) {E : Type*} [AddCommMonoid E] (g : D → E) :
    ∑ x ∈ (eraseAt M v).dartsAt a, g x.1 = ∑ x ∈ (M.dartsAt a).filter (fun x => ¬ M.atom (M.mate x) = v), g x := by
  have h : (eraseAt M v).dartsAt a =
      ((M.dartsAt a).filter (fun x => ¬ M.atom (M.mate x) = v)).subtype
        (fun x => M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v) := by
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_subtype]
    constructor
    · intro hx; exact ⟨hx, x.2.2⟩
    · intro hx; exact hx.1
  rw [h, Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem]
  intro x hx
  simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact ⟨hx.1 ▸ ha, hx.2⟩

section counts
variable {M v}

theorem card_mate_at : (Finset.univ.filter fun x : D => M.atom (M.mate x) = v).card = M.deg v := by
  unfold Molecule.deg Molecule.dartsAt
  refine Finset.card_bij (fun x _ => M.mate x) ?_ ?_ ?_
  · intro x hx; simpa using hx
  · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
  · intro y hy
    refine ⟨M.mate y, ?_, M.mate_mate y⟩
    simpa [M.mate_mate] using hy

theorem card_edart (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) :
    Fintype.card (EDart M v) + 2 * M.deg v = Fintype.card D := by
  have h1 : Fintype.card (EDart M v) =
      (Finset.univ.filter fun x : D => M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v).card := Fintype.card_subtype _
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D))
    (fun x : D => M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v)
  rw [Finset.card_univ] at h2
  have h3 : (Finset.univ.filter fun x : D => ¬ (M.atom x ≠ v ∧ M.atom (M.mate x) ≠ v)) =
      (Finset.univ.filter fun x : D => M.atom x = v) ∪ (Finset.univ.filter fun x : D => M.atom (M.mate x) = v) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; tauto
  have h4 : Disjoint (Finset.univ.filter fun x : D => M.atom x = v)
      (Finset.univ.filter fun x : D => M.atom (M.mate x) = v) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hnl x (hx.trans hy.symm)
  rw [h3, Finset.card_union_of_disjoint h4, card_mate_at] at h2
  have h5 : (Finset.univ.filter fun x : D => M.atom x = v).card = M.deg v := rfl
  rw [h5] at h2
  rw [h1]; omega

theorem sum_mult (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) :
    ∑ a ∈ M.atoms.erase v, mult M v a = M.deg v := by
  have key := Finset.card_eq_sum_card_fiberwise (f := M.atom)
    (s := (Finset.univ.filter fun x : D => M.atom (M.mate x) = v)) (t := M.atoms.erase v) (fun x hx => by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_erase.2 ⟨fun e => hnl x (e.trans hx.symm), M.atom_mem x⟩)
  rw [card_mate_at] at key
  rw [key]
  refine Finset.sum_congr rfl fun a ha => ?_
  unfold mult Molecule.dartsAt
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem eraseAt_outdeg_le (a : V) : (eraseAt M v).outdeg a ≤ M.outdeg a := by
  unfold Molecule.outdeg
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx
  · intro x _ y _ e; exact Subtype.ext e

theorem eraseAt_indeg_le (a : V) : (eraseAt M v).indeg a ≤ M.indeg a := by
  unfold Molecule.indeg
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx
  · intro x _ y _ e; exact Subtype.ext e

end counts

section comps
variable {M v}

theorem adj_symm_er {a b : V} (h : M.Adj a b) : M.Adj b a := by
  obtain ⟨z, h1, h2⟩ := h
  exact ⟨M.mate z, h2, by rw [M.mate_mate]; exact h1⟩

theorem eraseAt_adj_iff {a b : V} : (eraseAt M v).Adj a b ↔ M.Adj a b ∧ a ≠ v ∧ b ≠ v := by
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨⟨x.1, h1, h2⟩, h1 ▸ x.2.1, h2 ▸ x.2.2⟩
  · rintro ⟨⟨z, h1, h2⟩, ha, hb⟩
    exact ⟨⟨z, h1 ▸ ha, h2 ▸ hb⟩, h1, h2⟩

theorem sc_lift {a b : V} (h : (eraseAt M v).SameComponent a b) : M.SameComponent a b := by
  induction h with
  | rel x y hr => exact Relation.EqvGen.rel _ _ (eraseAt_adj_iff.1 hr).1
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem sc_avoid {a b : V} (h : M.SameComponent a b) :
    ¬ M.SameComponent a v → (eraseAt M v).SameComponent a b := by
  induction h with
  | rel x y hr =>
    intro hx
    have hxv : x ≠ v := fun e => hx (e ▸ Relation.EqvGen.refl _)
    have hyv : y ≠ v := fun e => hx (Relation.EqvGen.rel _ _ (e ▸ hr))
    exact Relation.EqvGen.rel _ _ (eraseAt_adj_iff.2 ⟨hr, hxv, hyv⟩)
  | refl x => exact fun _ => Relation.EqvGen.refl _
  | symm x y hxy ih =>
    intro hy
    have hx : ¬ M.SameComponent x v := fun h' => hy (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hxy) h')
    exact Relation.EqvGen.symm _ _ (ih hx)
  | trans x y z hxy hyz ih1 ih2 =>
    intro hx
    have hy : ¬ M.SameComponent y v := fun h' => hx (Relation.EqvGen.trans _ _ _ hxy h')
    exact Relation.EqvGen.trans _ _ _ (ih1 hx) (ih2 hy)

/-- An atom in the component of `v` (other than `v`) reaches a neighbour of `v` in `M - v`. -/
theorem comp_to_v (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) {a : V} (ha : a ≠ v)
    (h : M.SameComponent a v) : ∃ w, M.Adj v w ∧ (eraseAt M v).SameComponent a w := by
  let S : V → Prop := fun x => ∃ w, M.Adj v w ∧ (eraseAt M v).SameComponent x w
  let Rr : V → Prop := fun x => x = v ∨ S x
  have dir : ∀ x y, M.Adj x y → Rr x → Rr y := by
    intro x y hxy hx
    by_cases hxv : x = v
    · subst hxv
      have hyv : y ≠ x := by
        rintro rfl
        obtain ⟨z, h1, h2⟩ := hxy
        exact hnl z (h1.trans h2.symm)
      exact Or.inr ⟨y, hxy, Relation.EqvGen.refl _⟩
    · by_cases hyv : y = v
      · exact Or.inl hyv
      · rcases hx with hx | ⟨w, hw, hxw⟩
        · exact absurd hx hxv
        · exact Or.inr ⟨w, hw, Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (eraseAt_adj_iff.2 ⟨hxy, hxv, hyv⟩))) hxw⟩
  have iff' : ∀ x y, M.SameComponent x y → (Rr x ↔ Rr y) := by
    intro x y hxy
    induction hxy with
    | rel x y hr => exact ⟨dir x y hr, dir y x (adj_symm_er hr)⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  have := (iff' a v h).2 (Or.inl rfl)
  rcases this with h1 | h1
  · exact absurd h1 ha
  · exact h1

end comps

end WaveTurbulence.FinalCountG3
