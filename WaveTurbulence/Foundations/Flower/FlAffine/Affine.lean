/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Frozen.Defs.OmegaNode
public import WaveTurbulence.Foundations.Cut2A.SpatialMeasure
public import WaveTurbulence.Foundations.LemLin.ScalarPeriod
public import WaveTurbulence.Foundations.WaveB.Bridges
/-! FL-AFFINE: supplement Lemma 9.3. At a branching node with conservation
`k_b = k₀ - k₁ + k₂`, the resonance factor at a same-sign (stem) child equals `2 r·(a - f)`
with `f` the other same-sign child, `a` the mid child, `r = k_b - f`; and the top filter
`χ₀(|Ω|/M)` is the value at `a` of a `SpatialMeasure` of mass `∫ ‖𝓕 χ₀‖`, uniformly in `f, r, M`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.FlAffine
open MeasureTheory
open scoped FourierTransform

/-- Algebraic core: `|f|² - |a|² + |a+r|² - |f+r|² = 2 r·(a-f)`. -/
theorem resFactor_affine {d : ℕ} (f a r : Mom d) :
    resFactor f a (a + r) (f + r) = 2 * inner ℝ r (a - f) := by
  unfold resFactor
  have h : ∀ x : Mom d, ‖x‖ ^ 2 = inner ℝ x x := fun x => (real_inner_self_eq_norm_sq x).symm
  simp only [h, inner_add_left, inner_add_right, inner_sub_right, real_inner_comm r a,
    real_inner_comm r f]
  ring

/-- Stem child `2`: `Ω_b = 2 r·(a - f)` with `f = k₀`, `a = k₁`, `r = k_b - k₀`. -/
theorem omegaNode_stem_two {w d : ℕ} (G : Garden w) (k : GNode G.tree → Mom d)
    (b : GBranch G.tree)
    (hcons : k b.toNode = k (b.child 0) - k (b.child 1) + k (b.child 2)) :
    omegaNode G k b =
      2 * inner ℝ (k b.toNode - k (b.child 0)) (k (b.child 1) - k (b.child 0)) ∧
    k (b.child 2) = k (b.child 1) + (k b.toNode - k (b.child 0)) := by
  have h2 : k (b.child 2) = k (b.child 1) + (k b.toNode - k (b.child 0)) := by
    rw [hcons]; abel
  refine ⟨?_, h2⟩
  unfold omegaNode
  obtain ⟨r, hr⟩ : ∃ r, r = k b.toNode - k (b.child 0) := ⟨_, rfl⟩
  have hB : k b.toNode = k (b.child 0) + r := by rw [hr]; abel
  rw [← hr] at h2 ⊢
  rw [h2, hB]
  exact resFactor_affine _ _ _

/-- Stem child `0`: the same with `f = k₂`, `a = k₁`, `r = k_b - k₂`. -/
theorem omegaNode_stem_zero {w d : ℕ} (G : Garden w) (k : GNode G.tree → Mom d)
    (b : GBranch G.tree)
    (hcons : k b.toNode = k (b.child 0) - k (b.child 1) + k (b.child 2)) :
    omegaNode G k b =
      2 * inner ℝ (k b.toNode - k (b.child 2)) (k (b.child 1) - k (b.child 2)) ∧
    k (b.child 0) = k (b.child 1) + (k b.toNode - k (b.child 2)) := by
  have h0 : k (b.child 0) = k (b.child 1) + (k b.toNode - k (b.child 2)) := by
    rw [hcons]; abel
  refine ⟨?_, h0⟩
  have hsym : omegaNode G k b = resFactor (k (b.child 2)) (k (b.child 1)) (k (b.child 0))
      (k b.toNode) := by
    unfold omegaNode resFactor; ring
  rw [hsym]
  obtain ⟨r, hr⟩ : ∃ r, r = k b.toNode - k (b.child 2) := ⟨_, rfl⟩
  have hB : k b.toNode = k (b.child 2) + r := by rw [hr]; abel
  rw [← hr] at h0 ⊢
  rw [h0, hB]
  exact resFactor_affine _ _ _

/-- Unified form: stem child `i`, other same-sign child `o` (`{i,o} = {0,2}`). -/
theorem omegaNode_stem {w d : ℕ} (G : Garden w) (k : GNode G.tree → Mom d)
    (b : GBranch G.tree)
    (hcons : k b.toNode = k (b.child 0) - k (b.child 1) + k (b.child 2))
    (i o : Fin 3) (hio : (i = 0 ∧ o = 2) ∨ (i = 2 ∧ o = 0)) :
    omegaNode G k b =
      2 * inner ℝ (k b.toNode - k (b.child o)) (k (b.child 1) - k (b.child o)) ∧
    k (b.child i) = k (b.child 1) + (k b.toNode - k (b.child o)) := by
  rcases hio with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact omegaNode_stem_zero G k b hcons
  · exact omegaNode_stem_two G k b hcons

/-- The cutoff `χ₀` as a one-dimensional Fourier measure: parameter `ξ ∈ ℝ`, amplitude
`𝓕 χ₀`, frequency `ξ`. -/
def chi0Measure : Cut2A.SpatialMeasure ℝ ℝ where
  μ := volume
  sigmaFinite := inferInstance
  frequency := id
  frequency_measurable := measurable_id
  amplitude := 𝓕 Fourier.chi0Complex
  amplitude_integrable := LemLin.integrable_fourier_chi0Complex

theorem chi0Measure_value (x : ℝ) : chi0Measure.value x = ((Fourier.chi0 x : ℝ) : ℂ) := by
  have hc : Continuous Fourier.chi0Complex := Fourier.chi0Complex_contDiff.continuous
  have hi : Integrable Fourier.chi0Complex := by
    have := Fourier.chi0_integrable.ofReal (𝕜 := ℂ)
    exact this
  have hx := congrFun (hc.fourierInv_fourier_eq hi LemLin.integrable_fourier_chi0Complex) x
  rw [Real.fourierInv_eq'] at hx
  unfold Cut2A.SpatialMeasure.value chi0Measure
  simp only [id, RCLike.inner_apply, conj_trivial, smul_eq_mul] at hx ⊢
  have hcx : Fourier.chi0Complex x = ((Fourier.chi0 x : ℝ) : ℂ) := rfl
  rw [← hcx, ← hx]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Real.fourierChar_apply, mul_comm]

/-- The top filter in the middle-child momentum `a`: `a ↦ χ₀(2 r·(a - f)/M)`. -/
def topFilterMeasure {d : ℕ} (r f : Mom d) (M : ℝ) : Cut2A.SpatialMeasure (Mom d) ℝ :=
  chi0Measure.affine (innerSL ℝ ((2 / M) • r)) (-((2 / M) * inner ℝ r f))

theorem topFilterMeasure_value {d : ℕ} (r f a : Mom d) (M : ℝ) :
    (topFilterMeasure r f M).value a =
      ((chi0 (|2 * inner ℝ r (a - f)| / M) : ℝ) : ℂ) := by
  unfold topFilterMeasure
  rw [Cut2A.SpatialMeasure.affine_value, chi0Measure_value, ← WaveBBridges.chi0_eq_fourier_chi0]
  congr 1
  have h1 : (innerSL ℝ ((2 / M) • r)) a + -((2 / M) * inner ℝ r f) =
      (2 * inner ℝ r (a - f)) / M := by
    simp only [innerSL_apply_apply, inner_smul_left, inner_sub_right, RCLike.conj_to_real]
    ring
  rw [h1]
  have h2 : |(2 * inner ℝ r (a - f)) / M| = |(|2 * inner ℝ r (a - f)| / M)| := by
    rw [abs_div, abs_div, abs_abs]
  unfold chi0
  rw [h2]

/-- Lemma 9.3: for a same-sign stem child, the top filter is the value at the mid-child
momentum of a `SpatialMeasure` of mass `∫ ‖𝓕 χ₀‖`, uniformly in the outputs and `M`. -/
theorem topFilter_omegaNode {w d : ℕ} (G : Garden w) (k : GNode G.tree → Mom d)
    (b : GBranch G.tree)
    (hcons : k b.toNode = k (b.child 0) - k (b.child 1) + k (b.child 2))
    (i o : Fin 3) (hio : (i = 0 ∧ o = 2) ∨ (i = 2 ∧ o = 0)) (M : ℝ) :
    ((chi0 (|omegaNode G k b| / M) : ℝ) : ℂ) =
      (topFilterMeasure (k b.toNode - k (b.child o)) (k (b.child o)) M).value
        (k (b.child 1)) := by
  rw [topFilterMeasure_value, (omegaNode_stem G k b hcons i o hio).1]

end WaveTurbulence.Flower.FlAffine
