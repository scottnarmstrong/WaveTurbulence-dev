/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCCount1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCCount1`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 18: the constraint sets of the chart coordinates and their cardinalities.

For a fixed integer gap `rr` the chart coordinates of the labels of the removed vine lie in the set `Xset`: the joint
coordinate in a radius-`4` ball, each chart rung `(x_j, y_j)` in a `PairSet` (with the gap of its ladder when the rung
lies in a ladder of nonzero scale, and with the trivial gap `0` otherwise), and the core triple of a normal vine in a
`TripleSet`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Sets
variable {M : Molecule V D} (K : VineCut g M) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)

/-- The pair set of chart rung `j` for the gap `rr` (both constraints of the restricted decoration). -/
noncomputable def rungSet (L : ℝ) (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d) (β : V → ℝ) (τ : ℝ)
    (rr : Fin d → ℤ) (j : Fin A.indexing.shape.m) : Set ((Fin d → ℤ) × (Fin d → ℤ)) :=
  PairSet L (cenI K A w k0 r₀ (A.indexing.shape.xSlot j)) (cenI K A w k0 r₀ (A.indexing.shape.ySlot j))
    (latticePoint L rr) (A.ζc j 0) (A.ζc j 1) (β (av A (A.indexing.shape.ySlot j)) / 2)
    (-(A.ζc j 2 : ℝ) * ‖latticePoint L rr‖ ^ 2 -
      (β (av A (A.indexing.shape.xSlot j)) + β (av A (A.indexing.shape.ySlot j))) / 2) τ

/-- The pair set of chart rung `j` keeping only the first constraint (gap replaced by `0`). -/
noncomputable def rungSet0 (L : ℝ) (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d) (β : V → ℝ) (τ : ℝ)
    (j : Fin A.indexing.shape.m) : Set ((Fin d → ℤ) × (Fin d → ℤ)) :=
  PairSet L (cenI K A w k0 r₀ (A.indexing.shape.xSlot j)) (cenI K A w k0 r₀ (A.indexing.shape.ySlot j))
    (latticePoint L (0 : Fin d → ℤ)) 1 0 (β (av A (A.indexing.shape.ySlot j)) / 2) 0 τ

theorem rungSet_sub_rungSet0 (L : ℝ) (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d) (β : V → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (rr : Fin d → ℤ) (j : Fin A.indexing.shape.m) :
    rungSet K A L w k0 r₀ β τ rr j ⊆ rungSet0 K A L w k0 r₀ β τ j := by
  intro q hq
  obtain ⟨n1, n2, i1, -⟩ := hq
  refine ⟨n1, n2, i1, ?_⟩
  simp [latticePoint_zero, hτ]

end Sets

section RungBounds
variable {M : Molecule V D} (K : VineCut g M) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)
  {γ δ Cp L : ℝ}

theorem rung_ncard_gain (hpair : PairProp d γ δ Cp L) (hL0 : 0 < L) (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d)
    (β : V → ℝ) (rr : Fin d → ℤ) (Pr : ℝ) (hP1 : L⁻¹ ≤ Pr) (hP2 : Pr ≤ 1)
    (hsc : (8 : ℝ)⁻¹ * Pr ≤ ‖latticePoint L rr‖) (j : Fin A.indexing.shape.m)
    (hz : A.ζc j 0 ≠ 0 ∨ A.ζc j 1 ≠ 0) :
    (rungSet K A L w k0 r₀ β (δ⁻¹ * L ^ (-2 * γ)) rr j).Finite ∧
    ((rungSet K A L w k0 r₀ β (δ⁻¹ * L ^ (-2 * γ)) rr j).ncard : ℝ) ≤
      Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * (Molecule.ladderWeight L γ δ Pr)⁻¹ := by
  have := hpair rr Pr (Or.inr ⟨hP1, hP2⟩) (fun _ => hsc) (cenI K A w k0 r₀ (A.indexing.shape.xSlot j))
    (cenI K A w k0 r₀ (A.indexing.shape.ySlot j)) (β (av A (A.indexing.shape.ySlot j)) / 2)
    (-(A.ζc j 2 : ℝ) * ‖latticePoint L rr‖ ^ 2 -
      (β (av A (A.indexing.shape.xSlot j)) + β (av A (A.indexing.shape.ySlot j))) / 2)
    (A.ζc j 0) (A.ζc j 1) (A.ζ_unit j 0) (A.ζ_unit j 1) hz
  exact this

theorem rung_ncard_nogain (hpair : PairProp d γ δ Cp L) (hlog : 1 ≤ Real.log L) (hτ : 0 ≤ δ⁻¹ * L ^ (-2 * γ))
    (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d) (β : V → ℝ) (j : Fin A.indexing.shape.m) :
    (rungSet0 K A L w k0 r₀ β (δ⁻¹ * L ^ (-2 * γ)) j).Finite ∧
    ((rungSet0 K A L w k0 r₀ β (δ⁻¹ * L ^ (-2 * γ)) j).ncard : ℝ) ≤
      Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * 1 := by
  have h := hpair 0 0 (Or.inl rfl) (fun h => absurd h (lt_irrefl _)) (cenI K A w k0 r₀ (A.indexing.shape.xSlot j))
    (cenI K A w k0 r₀ (A.indexing.shape.ySlot j)) (β (av A (A.indexing.shape.ySlot j)) / 2) 0 1 0
    (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inl (by norm_num))
  have hw : min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * 0) = 1 := by
    rw [mul_zero, add_zero]; exact min_eq_right (one_le_pow₀ hlog)
  rw [hw, inv_one] at h
  exact h

end RungBounds

end WaveTurbulence.GammaLow.FinalCount.Step1
