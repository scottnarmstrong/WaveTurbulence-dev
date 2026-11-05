/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickInclusionExclusion
public import WaveTurbulence.Foundations.RegAsymp.SpecialZeroSupport

/-! # Only non-special energy links survive a nontrivial Wick pattern -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset Links ApproxNT

/-- The links whose energy coordinate is frozen by the pattern. -/
def wickTracedLinks {n : ℕ} (σ : Fin n → Fin 4) : Finset (Fin n) :=
  univ.filter (fun j => σ j ≠ 0)

/-- Every nontrivial pattern freezes at least one energy coordinate. -/
theorem wickTracedLinks_nonempty {n : ℕ} {σ : Fin n → Fin 4} (hσ : σ ≠ 0) :
    (wickTracedLinks σ).Nonempty := by
  classical
  by_contra h
  apply hσ
  funext j
  change σ j = 0
  have hj : j ∉ wickTracedLinks σ := fun hj => h ⟨j,hj⟩
  simpa only [wickTracedLinks,mem_filter,mem_univ,true_and,not_not] using hj

/-- A nonzero pattern term satisfies every literal coordinate constraint. -/
theorem wickPatternConstraint_of_prod_ne_zero {d n : ℕ}
    {θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)} {σ : Fin n → Fin 4}
    (h : (∏ j, wickPatternTerm θ j (σ j)) ≠ 0) (j : Fin n) :
    wickPatternConstraint θ j (σ j) := by
  classical
  have hj := (prod_ne_zero_iff.mp h) j (mem_univ j)
  by_contra hc
  exact hj (by simp only [wickPatternTerm,hc,ite_false])

/-- Every traced link has at least one actually zero vector. -/
theorem wickPattern_zero_coordinate {d n : ℕ}
    {θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)} {σ : Fin n → Fin 4}
    (h : (∏ j, wickPatternTerm θ j (σ j)) ≠ 0) {j : Fin n} (hj : j ∈ wickTracedLinks σ) :
    (θ j).1=0 ∨ (θ j).2=0 := by
  have hc := wickPatternConstraint_of_prod_ne_zero h j
  have hz : σ j ≠ 0 := (mem_filter.mp hj).2
  generalize he : σ j = c at hc hz
  fin_cases c <;> simp_all [wickPatternConstraint]

/-- Special zero energies vanish, so every surviving trace is in J's complement. -/
theorem wickTracedLinks_disjoint_special {d n : ℕ}
    (L μ : ℝ) {θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)} {σ : Fin n → Fin 4}
    (h : (∏ j, wickPatternTerm θ j (σ j)) ≠ 0)
    (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (hΨ : resProfile J Ψ (fun j => μ*inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2)) ≠ 0) :
    Disjoint (wickTracedLinks σ) J := by
  classical
  apply disjoint_left.mpr
  intro j hj hJ
  have hz : μ*inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2) = 0 := by
    rcases wickPattern_zero_coordinate h hj with hx | hy
    · rw [hx]
      have he : latticePoint L (0 : Fin d → ℤ) = 0 := by
        ext i
        simp [latticePoint]
      rw [he,inner_zero_left,mul_zero]
    · rw [hy]
      have he : latticePoint L (0 : Fin d → ℤ) = 0 := by
        ext i
        simp [latticePoint]
      rw [he,inner_zero_right,mul_zero]
  exact hΨ (resProfile_eq_zero_of_coordinate_zero J Ψ _ hJ hz)

end WaveTurbulence.RegAsymp
