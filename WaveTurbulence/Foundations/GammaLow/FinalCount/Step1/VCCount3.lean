/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCCount3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCExcess
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCCount3`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 21: **the single-vine label count `𝔉`** (DH23 L1799--L1801), of a charted vine (main: from `VINEPARAM`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Aux
variable {M : Molecule V D} (K : VineCut g M) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)

theorem card_atoms_eq : K.C.atoms.card = A.indexing.shape.n + 1 := by
  have h1 : Fintype.card (Fin A.indexing.shape.n) = Fintype.card ↥(K.C.atoms.erase K.C.upper) :=
    Fintype.card_congr A.indexing.atom
  simp only [Fintype.card_fin, Fintype.card_coe] at h1
  rw [Finset.card_erase_of_mem K.a_mem] at h1
  have : 0 < K.C.atoms.card := Finset.card_pos.mpr ⟨_, K.a_mem⟩
  omega

theorem shape_n_bad (hbad : X.IsBad = true) : A.indexing.shape.n = 2 * A.indexing.shape.m + 1 := by
  simp [Shape.n, hbad]

theorem shape_n_normal (hn : X.IsBad = false) : A.indexing.shape.n = 2 * A.indexing.shape.m + 4 := by
  simp [Shape.n, hn]

end Aux

end WaveTurbulence.GammaLow.FinalCount.Step1
