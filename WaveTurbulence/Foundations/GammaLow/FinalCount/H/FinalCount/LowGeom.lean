/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGeom
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGeom`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN start, session 20): the standing hypotheses of a LOW garden from the amended geometry.**

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
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

section gen
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

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
theorem tripleDesig_LOW {R : ℕ} {G : Garden (2 * R)} {C : Src.CountingChoices Src.γL G d} (hg : Src.CountingGeometry G C) (hR : 1 ≤ R) :
    TripleDesig (collD C.subpro) :=
  tripleDesig_of_eq3_of hg.molecule.1 (by rw [hg.atom_count]; exact hg.bond_count) hg.connected hR
    (tripleDesig3_of_field C.subpro hg.tripleDesignated)

/-- **`SubHypLoop R`** (G3-LOWDEG GL18) for a garden with amended geometry and at least two atoms. -/
theorem subHypLoop_of_geometry {R : ℕ} {G : Garden (2 * R)} {C : Src.CountingChoices Src.γL G d} (hg : Src.CountingGeometry G C) (hR : 1 ≤ R)
    (h2 : 2 ≤ G.molecule.atoms.card) : SubHypLoop R G.molecule where
  bounds := hg.molecule.1
  count := by rw [hg.atom_count]; exact hg.bond_count
  conn := hg.connected
  one_le := hR
  nonloop := nonloop_of_two_le hg.connected h2

/-- **`SubHypL R`** for a loop-free garden with amended geometry and at least two atoms. -/
theorem subHypL_of_geometry {R : ℕ} {G : Garden (2 * R)} {C : Src.CountingChoices Src.γL G d} (hg : Src.CountingGeometry G C) (hR : 1 ≤ R)
    (h2 : 2 ≤ G.molecule.atoms.card) (hnl : ∀ x, G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x)) :
    SubHypL R G.molecule where
  bounds := hg.molecule.1
  count := by rw [hg.atom_count]; exact hg.bond_count
  noloop := hnl
  conn := hg.connected
  one_le := hR
  deg_pos := by
    intro a ha
    obtain ⟨x, hx, -⟩ := nonloop_of_two_le hg.connected h2 a ha
    unfold Molecule.deg
    exact Finset.card_pos.2 ⟨x, (Mole.mem_dartsAt G.molecule a x).2 hx⟩

end garden

end WaveTurbulence.GammaLow.FinalCount.H
