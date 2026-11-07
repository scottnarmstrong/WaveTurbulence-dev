/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTDomain
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTHval
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTExt
/-! # FLOWER-P5: the class Fourier bound for the free clocks (copy-and-thread of `class_fourier`, `Glue9`)

The generic engine `class_bound` is applied on the free branches `FrB`, with the domain `Om0 chF lsF capF` of
`LadderSTDomain` and the ladder atoms (which are free, since stubs lie in no maximal ladder). The frequency region
is the projection of the class `clsPF` to the free coordinates; its pointwise facts are obtained from `loc_atom`
and `exists_Sy` by extending a free frequency by the stub frequencies of a witness. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.LadderDisjoint MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ} {G : Garden w}

/-- The class `clsPF`, projected to the free coordinates. -/
def clsPFfree (D : SplicedKernelDataST G d) (scales : Finset (GBranch G.tree) → ℝ) (L γ η δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π : PF G) : Set (FrB G D.fix → ℝ) :=
  {αf | ∃ α ∈ clsPF G D.toSplicedKernelData scales L γ η δ base roots π, ∀ v : FrB G D.fix, αf v = α v.1}

/-- The ladder atoms of a presentation are free. -/
theorem rowN_free (D : SplicedKernelDataST G d)
    (hpend : ∀ S ∈ G.molecule.maximalLadders, ∀ b ∈ D.stubs, b ∉ S) (π0 : PF G) (S : LQ G) (j : ℕ) :
    D.fix (rowN (π0.u S) j) = none ∧ D.fix (rowN (π0.v S) j) = none := by
  have h := rowN_mem_ladderAtoms (π0.u S) (π0.v S) j
  rw [π0.atoms S] at h
  exact ⟨(fix_none_iff D _).mpr fun hb => hpend S.1 S.2 _ hb h.1, (fix_none_iff D _).mpr fun hb => hpend S.1 S.2 _ hb h.2⟩

theorem atomAt_free (D : SplicedKernelDataST G d)
    (hpend : ∀ S ∈ G.molecule.maximalLadders, ∀ b ∈ D.stubs, b ∉ S) (π0 : PF G) (S : LQ G) (b : Bool) (i : ℕ) :
    D.fix (atomAt π0 S b i) = none := by
  unfold atomAt
  split_ifs
  · exact (rowN_free D hpend π0 S i).1
  · exact (rowN_free D hpend π0 S i).2


end WaveTurbulence.FlowerP5
