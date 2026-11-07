/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseSt
/-! **FINALCOUNT-G3 (R29 item 3): Operation 5, set erasure.**  `eraseSet M E` is the molecule `M - E` on the darts of the bonds
touching no atom of `E` (a tame cluster, or the union of the tame clusters: erasing a set of atoms is independent of the order and
of the grouping into clusters).  `St.eraseSetSt s E` also deletes the former neighbours that became isolated (ghost neighbours).
`Good.eraseSet`: the index of the invariant satisfies `2R' + 4|E| ≤ 2R + (number of darts touching E)`, i.e.
`R' ≤ R + (e_E + int_E) - 2|E|` (`e_E` bonds from `E` to the outside, `int_E` bonds inside `E`); for `E = ⊔ K` over maximal clusters this is
`R + ∑_K (e_K + χ_K - 1 - s_K)` with `χ_K = int_K - s_K + 1` (R29 item 3). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (E : Finset V)

/-- The darts of the bonds touching no atom of `E`. -/
abbrev EDartS := {x : D // M.atom x ∉ E ∧ M.atom (M.mate x) ∉ E}

/-- The molecule `M - E`. -/
def eraseSet : Molecule V (EDartS M E) where
  atoms := M.atoms \ E
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1, by rw [M.mate_mate]; exact ⟨x.2.2, x.2.1⟩⟩
  out := fun x => M.out x.1
  atom_mem := fun x => Finset.mem_sdiff.2 ⟨M.atom_mem x.1, x.2.1⟩
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x e => M.mate_ne x.1 (congrArg Subtype.val e)
  out_mate := fun x => M.out_mate x.1

/-- The number of darts at `a` whose bond goes into `E`. -/
noncomputable def multS (a : V) : ℕ := ((M.dartsAt a).filter fun x => M.atom (M.mate x) ∈ E).card

/-- The darts touching `E`. -/
noncomputable def tch : ℕ := (Finset.univ.filter fun x : D => M.atom x ∈ E ∨ M.atom (M.mate x) ∈ E).card

theorem eraseSet_atoms : (eraseSet M E).atoms = M.atoms \ E := rfl

theorem eraseSet_deg_card {a : V} (ha : a ∉ E) : (eraseSet M E).deg a + multS M E a = M.deg a := by
  have h1 : (eraseSet M E).deg a =
      (Finset.univ.filter fun x : D => (M.atom x ∉ E ∧ M.atom (M.mate x) ∉ E) ∧ M.atom x = a).card := by
    unfold Molecule.deg Molecule.dartsAt
    exact card_filter_subtype' (fun x : D => M.atom x ∉ E ∧ M.atom (M.mate x) ∉ E) (fun x => M.atom x = a)
  have h2 : (Finset.univ.filter fun x : D => (M.atom x ∉ E ∧ M.atom (M.mate x) ∉ E) ∧ M.atom x = a) =
      (M.dartsAt a).filter fun x => ¬ M.atom (M.mate x) ∈ E := by
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨⟨h' ▸ ha, h⟩, h'⟩
  rw [h1, h2]
  unfold multS Molecule.deg
  rw [add_comm]
  exact Finset.card_filter_add_card_filter_not (s := M.dartsAt a) _

theorem card_edartS : Fintype.card (EDartS M E) + tch M E = Fintype.card D := by
  have h1 : Fintype.card (EDartS M E) =
      (Finset.univ.filter fun x : D => M.atom x ∉ E ∧ M.atom (M.mate x) ∉ E).card := Fintype.card_subtype _
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D))
    (fun x : D => M.atom x ∉ E ∧ M.atom (M.mate x) ∉ E)
  rw [Finset.card_univ] at h2
  have h3 : (Finset.univ.filter fun x : D => ¬ (M.atom x ∉ E ∧ M.atom (M.mate x) ∉ E)) =
      Finset.univ.filter fun x : D => M.atom x ∈ E ∨ M.atom (M.mate x) ∈ E := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [h3] at h2
  unfold tch
  rw [h1]; omega

theorem eraseSet_outdeg_le (a : V) : (eraseSet M E).outdeg a ≤ M.outdeg a := by
  unfold Molecule.outdeg
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx
  · intro x _ y _ e; exact Subtype.ext e

theorem eraseSet_indeg_le (a : V) : (eraseSet M E).indeg a ≤ M.indeg a := by
  unfold Molecule.indeg
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx
  · intro x _ y _ e; exact Subtype.ext e


/-- The darts leaving `E` (`e_E` of them: the bonds from `E` to the outside). -/
noncomputable def eDart : ℕ := (Finset.univ.filter fun x : D => M.atom x ∈ E ∧ M.atom (M.mate x) ∉ E).card

/-- The darts of the bonds inside `E` (`2 int_E` of them). -/
noncomputable def intDart : ℕ := (Finset.univ.filter fun x : D => M.atom x ∈ E ∧ M.atom (M.mate x) ∈ E).card

/-- `tch(E) = 2 e_E + 2 int_E`: with `R' ≤ R + (tch(E) - 4|E|)/2` this is `R + e_E + int_E - 2|E|`
`= R + ∑_K (e_K + χ_K - 1 - s_K)` over the maximal clusters `K` of `E` (`χ_K = int_K - s_K + 1`). -/
theorem tch_eq : tch M E = 2 * eDart M E + intDart M E := by
  have h1 : (Finset.univ.filter fun x : D => M.atom (M.mate x) ∈ E ∧ M.atom x ∉ E).card = eDart M E := by
    unfold eDart
    refine Finset.card_bij (fun x _ => M.mate x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [M.mate_mate]; exact ⟨hx.1, hx.2⟩
    · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨M.mate y, ?_, M.mate_mate y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [M.mate_mate]; exact ⟨hy.1, hy.2⟩
  have h2 : (Finset.univ.filter fun x : D => M.atom x ∈ E ∨ M.atom (M.mate x) ∈ E) =
      ((Finset.univ.filter fun x : D => M.atom x ∈ E ∧ M.atom (M.mate x) ∉ E) ∪
        (Finset.univ.filter fun x : D => M.atom (M.mate x) ∈ E ∧ M.atom x ∉ E)) ∪
        (Finset.univ.filter fun x : D => M.atom x ∈ E ∧ M.atom (M.mate x) ∈ E) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; tauto
  unfold tch
  rw [h2, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, h1]
  · unfold intDart eDart; ring
  · rw [Finset.disjoint_left]; intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hy.2 hx.1
  · rw [Finset.disjoint_left]; intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx hy
    rcases hx with hx | hx
    · exact hx.2 hy.2
    · exact hx.2 hy.1

end WaveTurbulence.FinalCountG3
