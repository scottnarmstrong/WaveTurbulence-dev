/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedFourier
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! Literal spliced amplitudes: uniform bounds and support in the actual source unit balls. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset

noncomputable def splicedMomentumAmplitude {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  (splicedEpsilon G D.hinges z : ℂ) * (splicedGapIndicator G D L γ η base z : ℂ) *
    (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z x))) *
    D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z x.1))

theorem abs_splicedEpsilon_le_one {w d : ℕ} (G : Garden w)
    (hinges : Finset (GBranch G.tree)) (z : GNode G.tree → (Fin d → ℤ)) :
    |splicedEpsilon G hinges z| ≤ 1 := by
  classical
  rw [splicedEpsilon, abs_prod]
  apply prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro v _
  unfold epsCoef
  split_ifs <;> norm_num

theorem abs_splicedGapIndicator_le_one {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    |splicedGapIndicator G D L γ η base z| ≤ 1 := by
  classical
  rw [splicedGapIndicator, abs_prod]
  apply prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro v _
  cases D.gapSpecification v <;> simp only
  · norm_num
  · split_ifs <;> norm_num

theorem norm_splicedMomentumAmplitude_le_one {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ‖splicedMomentumAmplitude G D L γ η base z‖ ≤ 1 := by
  have he : ‖∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z x))‖ ≤ 1 := by
    rw [norm_prod]
    apply prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro x hx
    have hh := SNorm_pointwise (D.edgeAmplitude x) 1 zero_le_one (by simpa using (hD.2.1 x hx).1)
      (base + latticePoint L (bondIndex G z x))
    simpa only [pow_zero, one_mul] using hh
  unfold splicedMomentumAmplitude
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_one₀
    (mul_le_one₀
      (mul_le_one₀ (abs_splicedEpsilon_le_one G D.hinges z) (abs_nonneg _)
        (abs_splicedGapIndicator_le_one G D L γ η base z)) (norm_nonneg _) he)
    (norm_nonneg _) (hD.2.2.1 _)

theorem splicedMomentumAmplitude_support {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (hD : SplicedAmplitudeBounds G D) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : splicedMomentumAmplitude G D L γ η base z ≠ 0) :
    splicedEpsilon G D.hinges z ≠ 0 ∧ splicedGapIndicator G D L γ η base z ≠ 0 ∧
    ∀ x ∈ G.molecule.bonds, ‖base + latticePoint L (bondIndex G z x) - D.center x‖ ≤ 1 := by
  classical
  constructor
  · intro he
    apply hz
    simp only [splicedMomentumAmplitude, he, Complex.ofReal_zero, zero_mul]
  constructor
  · intro he
    apply hz
    simp only [splicedMomentumAmplitude, he, Complex.ofReal_zero, mul_zero, zero_mul]
  · intro x hx
    by_contra hnorm
    have he := (hD.2.1 x hx).2 _ (lt_of_not_ge hnorm)
    have hp : (∏ y ∈ G.molecule.bonds,
        D.edgeAmplitude y (base + latticePoint L (bondIndex G z y))) = 0 :=
      prod_eq_zero hx he
    apply hz
    simp only [splicedMomentumAmplitude, hp, mul_zero, zero_mul]

end WaveTurbulence.LGSpine
