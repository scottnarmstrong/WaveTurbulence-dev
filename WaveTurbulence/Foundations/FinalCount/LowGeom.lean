/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowIface
/-! **FINALCOUNT-ASSEMBLY (LOW-GARDEN start, session 20): the standing hypotheses of a LOW garden from the amended geometry.**

* `bondsBetween_lt_four_of`: G3's `bondsBetween_lt_four` from `bounds`, `count`, `conn`, `1 ≤ R` only (no `deg3`, loops allowed).
* `tripleDesig_LOW`: `TripleDesig` of the garden's collection data from AMEND7's `tripleDesignated`, without `RegGeom`.
* `subHypLoop_of_geometry`: G3-LOWDEG's `SubHypLoop R` for a garden with at least two atoms (the one-atom gardens are G3-LOWDEG's
  Examples A/B: `countA_dartless_le_one`, `countA_allLoops_le`).
* `subHypL_of_geometry`: `SubHypL R` for a loop-free garden with at least two atoms. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

section gen
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- No two distinct atoms carry `4` or more bonds (G3 `bondsBetween_lt_four`, from `bounds`, `count`, `conn`, `1 ≤ R`). -/
theorem bondsBetween_lt_four_of {R : ℕ} {M : Molecule V D₀} (hbd : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2)
    (hcount : M.bonds.card + R = 2 * M.atoms.card) (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hR : 1 ≤ R) {a b : V} (ha : a ∈ M.atoms) : M.bondsBetween a b < 4 := by
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
    have h4a := deg_le_four (M := M) (hbd a ha)
    have h4b := deg_le_four (M := M) (hbd b hb)
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
    exact hclosed.sc (by simp) (hconn a ha c hc)
  have h1 := Finset.card_le_card hatoms
  have h2 : ({a, b} : Finset V).card ≤ 2 := Finset.card_le_two
  have h3 : B.card ≤ M.bonds.card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- `TripleDesig` from S4's `= 3` form under the four standing facts (no `deg3`). -/
theorem tripleDesig_of_eq3_of {R : ℕ} {M₀ : Molecule V D₀} (hbd : ∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2)
    (hcount : M₀.bonds.card + R = 2 * M₀.atoms.card) (hconn : ∀ a ∈ M₀.atoms, ∀ b ∈ M₀.atoms, M₀.SameComponent a b)
    (hR : 1 ≤ R) {C : CollData M₀} (h3 : TripleDesig3 C) : TripleDesig C := by
  intro a b ha hb hab h
  exact h3 a b ha hb hab (le_antisymm (by have := bondsBetween_lt_four_of hbd hcount hconn hR (b := b) ha; omega) h)

end gen

section garden
variable {d : ℕ}

/-- **`TripleDesig` for every garden with amended geometry** (no `RegGeom`; R48 AMEND7 `tripleDesignated`). -/
theorem tripleDesig_LOW {R : ℕ} {G : Garden (2 * R)} {C : CountingChoices G d} (hg : CountingGeometry G C) (hR : 1 ≤ R) :
    TripleDesig (collD C.subpro) :=
  tripleDesig_of_eq3_of hg.molecule.1 (by rw [hg.atom_count]; exact hg.bond_count) hg.connected hR
    (tripleDesig3_of_field C.subpro hg.tripleDesignated)

/-- **`SubHypLoop R`** (G3-LOWDEG GL18) for a garden with amended geometry and at least two atoms. -/
theorem subHypLoop_of_geometry {R : ℕ} {G : Garden (2 * R)} {C : CountingChoices G d} (hg : CountingGeometry G C) (hR : 1 ≤ R)
    (h2 : 2 ≤ G.molecule.atoms.card) : SubHypLoop R G.molecule where
  bounds := hg.molecule.1
  count := by rw [hg.atom_count]; exact hg.bond_count
  conn := hg.connected
  one_le := hR
  nonloop := nonloop_of_two_le hg.connected h2

end garden

end WaveTurbulence.FinalCountAsm
