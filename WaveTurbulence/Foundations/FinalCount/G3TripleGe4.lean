/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3RunN
public import WaveTurbulence.Foundations.FinalCount.G3Init
public import WaveTurbulence.Foundations.FinalCount.G3Inv
public import WaveTurbulence.Foundations.FinalCount.GhostMain4
/-! **FINALCOUNT-G3: the `≥ 4` case of `TripleDesig` (R37).**  A bond multiplicity `≥ 4` between two distinct atoms of `M_sub`
would make `{a, b}` a closed atom set (all `≤ 8` darts of `a` and `b` lie on those bonds), hence, by connectedness, all of
`M_sub`; the count `bonds + R = 2·atoms` with `R ≥ 1` then fails.  So S4's `= 3` form (`Subpro.triple_in_designated`) suffices:
`TripleDesig3 C → TripleDesig C`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- No two distinct atoms of a connected `M_sub` carry `4` or more bonds. -/
theorem bondsBetween_lt_four {R : ℕ} {M : Molecule V D₀} (hS : SubHyp R M) {a b : V} (ha : a ∈ M.atoms) : M.bondsBetween a b < 4 := by
  by_contra h4
  push Not at h4
  have hb : b ∈ M.atoms := by
    by_contra hb
    have : M.bondsBetween a b = 0 := by
      unfold Molecule.bondsBetween
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hx
      unfold Molecule.ends at hx
      rcases Sym2.eq_iff.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hb (h2 ▸ M.atom_mem _)
      · exact hb (h1 ▸ M.atom_mem _)
    omega
  set B := M.bonds.filter fun x => M.ends x = s(a, b) with hB
  have hBcard : B.card = M.bondsBetween a b := rfl
  have hBout : ∀ x ∈ B, M.out x = true := by
    intro x hx
    have := (Finset.mem_filter.1 hx).1
    simpa [Molecule.bonds] using this
  have hBin : ∀ x ∈ B, M.atom x = a ∨ M.atom x = b := by
    intro x hx
    have := (Finset.mem_filter.1 hx).2
    unfold Molecule.ends at this
    rcases Sym2.eq_iff.mp this with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hBin' : ∀ x ∈ B, M.atom (M.mate x) = a ∨ M.atom (M.mate x) = b := by
    intro x hx
    have := (Finset.mem_filter.1 hx).2
    unfold Molecule.ends at this
    rcases Sym2.eq_iff.mp this with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Or.inr h1
    · exact Or.inl h1
  set Dset : Finset D₀ := Finset.univ.filter fun x => M.atom x = a ∨ M.atom x = b with hD
  have hDcard : Dset.card ≤ 8 := by
    have h1 : Dset ⊆ M.dartsAt a ∪ M.dartsAt b := by
      intro x hx
      have := (Finset.mem_filter.1 hx).2
      rcases this with h | h
      · exact Finset.mem_union_left _ ((mem_dartsAt M a x).2 h)
      · exact Finset.mem_union_right _ ((mem_dartsAt M b x).2 h)
    have h2 := Finset.card_le_card h1
    have h3 := Finset.card_union_le (M.dartsAt a) (M.dartsAt b)
    have h4a := deg_le_four (M := M) (hS.bounds a ha)
    have h4b := deg_le_four (M := M) (hS.bounds b hb)
    unfold Molecule.deg at h4a h4b
    omega
  set E := B ∪ B.image M.mate with hE
  have hdisj : Disjoint B (B.image M.mate) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx'
    have h1 := hBout _ hx
    have h2 := hBout _ hy
    rw [M.out_mate, h2] at h1; simp at h1
  have hEcard : 8 ≤ E.card := by
    rw [hE, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (Function.Involutive.injective (f := M.mate) M.mate_mate)]
    omega
  have hEsub : E ⊆ Dset := by
    intro x hx
    rw [hD, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.1 hx with h | h
    · exact hBin x h
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact hBin' y hy
  have hEq : E = Dset := Finset.eq_of_subset_of_card_le hEsub (by omega)
  have hclosed : IsClosedSet M ({a, b} : Finset V) := by
    intro x hx
    have hxD : x ∈ Dset := by
      rw [hD, Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
      simpa using hx
    rw [← hEq] at hxD
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases Finset.mem_union.1 hxD with h | h
    · exact hBin' x h
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      rw [M.mate_mate]; exact hBin y hy
  have hatoms : M.atoms ⊆ {a, b} := by
    intro c hc
    exact hclosed.sc (by simp) (hS.conn a ha c hc)
  have h1 := Finset.card_le_card hatoms
  have h2 : ({a, b} : Finset V).card ≤ 2 := Finset.card_le_two
  have h3 : B.card ≤ M.bonds.card := Finset.card_le_card (Finset.filter_subset _ _)
  have := hS.count
  have := hS.one_le
  omega

/-- S4's form of `triple_in_designated` (`bondsBetween = 3`). -/
def TripleDesig3 {M₀ : Molecule V D₀} (C : CollData M₀) : Prop :=
  ∀ a b : V, a ∈ M₀.atoms → b ∈ M₀.atoms → a ≠ b → M₀.bondsBetween a b = 3 →
    ∃ v c x y, ((v = a ∧ c = b) ∨ (v = b ∧ c = a)) ∧ v ∈ C.hinges ∧ C.first v = some x ∧ C.second v = some y ∧
      TripleAtM M₀ v x y ∧ M₀.atom (M₀.mate x) = c ∧ M₀.atom (M₀.mate y) = c

/-- **`TripleDesig` from S4's `= 3` form**: the `≥ 4` case does not occur (`bondsBetween_lt_four`). -/
theorem tripleDesig_of_eq3 {R : ℕ} {M₀ : Molecule V D₀} (hS : SubHyp R M₀) {C : CollData M₀} (h3 : TripleDesig3 C) :
    TripleDesig C := by
  intro a b ha hb hab h
  exact h3 a b ha hb hab (le_antisymm (by have := bondsBetween_lt_four (b := b) hS ha; omega) h)

end WaveTurbulence.FinalCountG3
