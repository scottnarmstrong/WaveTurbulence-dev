/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3MapBase
public import WaveTurbulence.Foundations.FinalCount.GL19
/-! **FINALCOUNT-G3: `FinalShape` for a component of the final molecule** (first part: degrees, classes, bonds). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

theorem bondsBetween_le_twoL {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D)
    (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hnt : NoTripleBond M) (a b : V) : M.bondsBetween a b ≤ 2 := by
  by_cases hab : a = b
  · subst hab
    have : M.bondsBetween a a = 0 := by
      unfold Molecule.bondsBetween
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hx
      unfold Molecule.ends at hx
      have := Sym2.eq_iff.mp hx
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hnl x (h1.trans h2.symm)
    omega
  · by_cases ha : a ∈ M.atoms
    · by_cases hb : b ∈ M.atoms
      · have := hnt a ha b hb hab; omega
      · have : M.bondsBetween a b = 0 := by
          unfold Molecule.bondsBetween
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _ hx
          unfold Molecule.ends at hx
          rcases Sym2.eq_iff.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hb (h2 ▸ M.atom_mem _)
          · exact hb (h1 ▸ M.atom_mem _)
        omega
    · have : M.bondsBetween a b = 0 := by
        unfold Molecule.bondsBetween
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _ hx
        unfold Molecule.ends at hx
        rcases Sym2.eq_iff.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ha (h1 ▸ M.atom_mem _)
        · exact ha (h2 ▸ M.atom_mem _)
      omega

theorem compMol_bondsBetween_leL {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (a₀ a b : V) :
    (compMol M a₀).bondsBetween a b ≤ M.bondsBetween a b := by
  unfold Molecule.bondsBetween
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Molecule.bonds, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx
  · intro x _ y _ e; exact Subtype.ext e

section shape
variable {hf : HSt V D₀} (hC : Prop95ConclAtL L γ η w κ R hf Tm) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms)
include hC ha₀

private theorem sc_of_memL {b c : V} (hb : b ∈ (compMol hf.s.M a₀).atoms) (hc : c ∈ (compMol hf.s.M a₀).atoms) :
    hf.s.M.SameComponent b c :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ((mem_compMol _ _).1 hb).2) ((mem_compMol _ _).1 hc).2

theorem shape_nonemptyL : (compMol hf.s.M a₀).atoms.Nonempty :=
  ⟨a₀, (mem_compMol _ _).2 ⟨ha₀, Relation.EqvGen.refl _⟩⟩

theorem shape_capsL : ∀ a ∈ (compMol hf.s.M a₀).atoms,
    (compMol hf.s.M a₀).outdeg a ≤ 2 ∧ (compMol hf.s.M a₀).indeg a ≤ 2 := by
  intro a ha
  have h := (mem_compMol _ _).1 ha
  rw [compMol_outdeg _ _ h.2, compMol_indeg _ _ h.2]
  exact hC.bal.1 a h.1

theorem shape_noLoopL : ∀ x, (compMol hf.s.M a₀).atom x ≠ (compMol hf.s.M a₀).atom ((compMol hf.s.M a₀).mate x) :=
  fun x => hC.noloop x.1

theorem shape_connL : ∀ a ∈ (compMol hf.s.M a₀).atoms, ∀ b ∈ (compMol hf.s.M a₀).atoms,
    (compMol hf.s.M a₀).SameComponent a b := by
  intro a ha b hb
  exact restrictP_sc_of _ _ (compP_closed _ a₀) (sc_of_memL hC ha₀ ha hb) ((mem_compMol _ _).1 ha).2

theorem shape_degPosL : ∀ a ∈ (compMol hf.s.M a₀).atoms, 1 ≤ (compMol hf.s.M a₀).deg a := by
  intro a ha
  have h := (mem_compMol _ _).1 ha
  rw [compMol_deg _ _ h.2]
  exact (hC.struct.deg_range a h.1).1

theorem shape_classesL (hE : LowFree hf a₀) : ∀ a ∈ (compMol hf.s.M a₀).atoms,
    ((compMol hf.s.M a₀).deg a ≤ 2 ↔ ¬ (toCls (hf.s.cls a)).IsEps) := by
  intro a ha
  have h := (mem_compMol _ _).1 ha
  rw [compMol_deg _ _ h.2, toCls_isEps]
  constructor
  · intro hd hc
    have := hE a (Finset.mem_filter.2 h) hc
    omega
  · intro hc
    exact hC.struct.ab_deg a h.1 hc

theorem shape_dir2L (hE : LowFree hf a₀) : ∀ a ∈ (compMol hf.s.M a₀).atoms, (compMol hf.s.M a₀).deg a = 2 →
    (compMol hf.s.M a₀).outdeg a = 1 ∧ (compMol hf.s.M a₀).indeg a = 1 := by
  intro a ha hd
  have h := (mem_compMol _ _).1 ha
  rw [compMol_deg _ _ h.2] at hd
  rw [compMol_outdeg _ _ h.2, compMol_indeg _ _ h.2]
  refine hC.bal.2 a h.1 ?_ hd
  intro hc
  have := hE a (Finset.mem_filter.2 h) hc
  omega

theorem shape_noTripleL : ∀ a b, (compMol hf.s.M a₀).bondsBetween a b ≤ 2 :=
  fun a b => (compMol_bondsBetween_leL _ _ a b).trans
    (bondsBetween_le_twoL _ hC.noloop hC.no_triple a b)

end shape

end WaveTurbulence.FinalCountG3
