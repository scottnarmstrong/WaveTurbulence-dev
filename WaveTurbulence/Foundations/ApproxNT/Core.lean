/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.CellBounds
public import WaveTurbulence.Foundations.ApproxNT.Products

/-!
# Products of cells and their Fourier representation (packet NT6)

For a finite index type `ι` (the momentum pairs), cell centers `p, q`, frequencies `ξ, ζ` and a
profile `Φ` on `ℝ^ι` with a Fourier representation `Φ(Ω) = ∫ Φ̂(s) e(s·Ω) ds`, the lattice sum and
the integral

* `multiSum = ∑_{(x,y) ∈ (L⁻¹ℤ^d)^{2ι}} ∏ᵢ θ(xᵢ-pᵢ)θ(yᵢ-qᵢ)e(ξᵢ·xᵢ+ζᵢ·yᵢ) · Φ(μ⟨xᵢ,yᵢ⟩)`,
* `multiInt = ∫ ∏ᵢ θ(xᵢ-pᵢ)θ(yᵢ-qᵢ)e(ξᵢ·xᵢ+ζᵢ·yᵢ) · Φ(μ⟨xᵢ,yᵢ⟩) dx dy`

decouple: `multiSum = ∫ Φ̂(s) ∏ᵢ cellSum(μ sᵢ) ds` and `multiInt = ∫ Φ̂(s) ∏ᵢ cellInt(μ sᵢ) ds`.
This is the step of DH21 Prop 6.1's proof writing `S = ∫ μ^{-n} Ψ̂(μ^{-1}s)[∑ W e(s·Ω)] ds`, after
the unit-cell localization has made the amplitude a product.
-/

public section

noncomputable section

open MeasureTheory Metric WithLp Finset Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The phase-weighted cell amplitude of one pair. -/
@[expose] def pairAmp (p q ξ ζ : Mom d) (w : Mom d × Mom d) : ℂ :=
  Real.fourierChar (inner ℝ w.1 ξ + inner ℝ w.2 ζ) • cellAmp p q w.1 w.2

/-- The product amplitude `∏ᵢ θ(xᵢ-pᵢ)θ(yᵢ-qᵢ)e(ξᵢ·xᵢ+ζᵢ·yᵢ)`. -/
@[expose] def multiAmp (p q ξ ζ : ι → Mom d) (w : ι → Mom d × Mom d) : ℂ :=
  ∏ i, pairAmp (p i) (q i) (ξ i) (ζ i) (w i)

/-- The resonance vector `(⟨xᵢ, yᵢ⟩)ᵢ`. -/
@[expose] def resVec (w : ι → Mom d × Mom d) : ι → ℝ := fun i => inner ℝ (w i).1 (w i).2

/-- The lattice points of a pair index. -/
@[expose] def latPair (L : ℝ) (g : (Fin d → ℤ) × (Fin d → ℤ)) : Mom d × Mom d :=
  (latticePoint L g.1, latticePoint L g.2)

/-- The decoupled lattice sum. -/
@[expose] def multiSum (L μ : ℝ) (Φ : (ι → ℝ) → ℂ) (p q ξ ζ : ι → Mom d) : ℂ :=
  ∑' g : ι → (Fin d → ℤ) × (Fin d → ℤ),
    multiAmp p q ξ ζ (fun i => latPair L (g i)) * Φ (μ • resVec (fun i => latPair L (g i)))

/-- The decoupled integral. -/
@[expose] def multiInt (μ : ℝ) (Φ : (ι → ℝ) → ℂ) (p q ξ ζ : ι → Mom d) : ℂ :=
  ∫ w : ι → Mom d × Mom d, multiAmp p q ξ ζ w * Φ (μ • resVec w)

/-- A Fourier representation of a profile on `ℝ^ι`. -/
@[expose] def IsFourierRep (Φ Φh : (ι → ℝ) → ℂ) : Prop :=
  Integrable Φh ∧ ∀ Ω : ι → ℝ, Φ Ω = ∫ s, Φh s * ∏ i, (Real.fourierChar (s i * Ω i) : ℂ)

omit [DecidableEq ι] in
theorem norm_pairAmp_le (p q ξ ζ : Mom d) (w : Mom d × Mom d) : ‖pairAmp p q ξ ζ w‖ ≤ 1 := by
  rw [pairAmp, Circle.norm_smul]; exact norm_cellAmp_le_one _ _ _ _

omit [DecidableEq ι] in
theorem norm_multiAmp_le (p q ξ ζ : ι → Mom d) (w : ι → Mom d × Mom d) :
    ‖multiAmp p q ξ ζ w‖ ≤ 1 := by
  rw [multiAmp, norm_prod]
  exact prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => norm_pairAmp_le _ _ _ _ _

/-- One factor after inserting the phase `e(sᵢ μ ⟨xᵢ,yᵢ⟩)`. -/
theorem pairAmp_mul_phase (p q ξ ζ : Mom d) (w : Mom d × Mom d) {r t : ℝ}
    (hr : r = t * inner ℝ w.1 w.2) :
    pairAmp p q ξ ζ w * (Real.fourierChar r : ℂ) =
      Real.fourierChar (inner ℝ w.1 ξ + inner ℝ w.2 ζ + t * inner ℝ w.1 w.2) •
        cellAmp p q w.1 w.2 := by
  rw [pairAmp, Circle.smul_def, Circle.smul_def, ← hr,
    AddChar.map_add_eq_mul Real.fourierChar (inner ℝ w.1 ξ + inner ℝ w.2 ζ) r, Circle.coe_mul]
  ring

omit [DecidableEq ι] in
theorem continuous_pairAmp (p q ξ ζ : Mom d) : Continuous (pairAmp p q ξ ζ) :=
  (contDiff_cellIntegrand p q ξ ζ 0).continuous.congr (fun w => by simp [pairAmp])

omit [DecidableEq ι] in
theorem continuous_multiAmp (p q ξ ζ : ι → Mom d) : Continuous (multiAmp p q ξ ζ) :=
  continuous_finsetProd _ fun i _ => (continuous_pairAmp _ _ _ _).comp (continuous_apply i)

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_resVec_apply (i : ι) :
    Continuous (fun w : ι → Mom d × Mom d => resVec w i) :=
  ((continuous_apply i).fst).inner ((continuous_apply i).snd)

omit [DecidableEq ι] in
theorem measurable_prod_phase (Ω : ι → ℝ) :
    Continuous (fun s : ι → ℝ => ∏ i, (Real.fourierChar (s i * Ω i) : ℂ)) :=
  continuous_finsetProd _ fun i _ => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
    ((continuous_apply i).mul continuous_const)

omit [DecidableEq ι] in
theorem norm_prod_phase (s Ω : ι → ℝ) : ‖∏ i, (Real.fourierChar (s i * Ω i) : ℂ)‖ = 1 := by
  rw [norm_prod]; simp

/-- The decoupling of the lattice sum. -/
theorem multiSum_eq {L : ℝ} (hL : 0 < L) (μ : ℝ) {Φ Φh : (ι → ℝ) → ℂ} (hrep : IsFourierRep Φ Φh)
    (p q ξ ζ : ι → Mom d) :
    multiSum L μ Φ p q ξ ζ =
      ∫ s, Φh s * ∏ i, cellSum L (p i) (q i) (ξ i) (ζ i) (μ * s i) := by
  set G : Finset (ι → (Fin d → ℤ) × (Fin d → ℤ)) :=
    Fintype.piFinset fun i => cellIndex hL (p i) (q i)
  have hzero : ∀ g ∉ G, multiAmp p q ξ ζ (fun i => latPair L (g i)) = 0 := by
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    simp only [not_forall] at hg
    obtain ⟨i, hi⟩ := hg
    refine prod_eq_zero (mem_univ i) ?_
    simp only [latPair]
    rw [pairAmp, cellAmp_lattice_eq_zero hL hi, smul_zero]
  have hint : ∀ g ∈ G, Integrable (fun s : ι → ℝ => Φh s * (multiAmp p q ξ ζ
      (fun i => latPair L (g i)) * ∏ i, (Real.fourierChar (s i *
        (μ • resVec (fun i => latPair L (g i))) i) : ℂ))) := by
    intro g _
    refine hrep.1.mul_bdd (c := 1) ?_ ?_
    · exact (continuous_const.mul (measurable_prod_phase _)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun s => ?_
      rw [norm_mul, norm_prod_phase, mul_one]
      exact norm_multiAmp_le _ _ _ _ _
  rw [multiSum, tsum_eq_sum (s := G) fun g hg => by rw [hzero g hg, zero_mul]]
  calc ∑ g ∈ G, multiAmp p q ξ ζ (fun i => latPair L (g i)) *
        Φ (μ • resVec (fun i => latPair L (g i)))
      = ∑ g ∈ G, ∫ s, Φh s * (multiAmp p q ξ ζ (fun i => latPair L (g i)) *
          ∏ i, (Real.fourierChar (s i *
            (μ • resVec (fun i => latPair L (g i))) i) : ℂ)) := by
        refine sum_congr rfl fun g _ => ?_
        rw [hrep.2, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only
        ring
    _ = ∫ s, ∑ g ∈ G, Φh s * (multiAmp p q ξ ζ (fun i => latPair L (g i)) *
          ∏ i, (Real.fourierChar (s i *
            (μ • resVec (fun i => latPair L (g i))) i) : ℂ)) := (integral_finsetSum _ hint).symm
    _ = ∫ s, Φh s * ∏ i, cellSum L (p i) (q i) (ξ i) (ζ i) (μ * s i) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only
        rw [← mul_sum]
        congr 1
        simp_rw [cellSum_eq_finset hL]
        rw [prod_univ_sum]
        refine sum_congr rfl fun g _ => ?_
        rw [multiAmp, ← prod_mul_distrib]
        refine prod_congr rfl fun i _ => ?_
        rw [pairAmp_mul_phase (p i) (q i) (ξ i) (ζ i) (latPair L (g i)) (t := μ * s i)
          (by simp only [resVec, Pi.smul_apply, smul_eq_mul]; ring)]
        rfl

omit [DecidableEq ι] in
theorem integrable_multiAmp (p q ξ ζ : ι → Mom d) :
    Integrable (fun w : ι → Mom d × Mom d => multiAmp p q ξ ζ w) := by
  have h : ∀ i, Integrable (fun w : Mom d × Mom d => pairAmp (p i) (q i) (ξ i) (ζ i) w) := by
    intro i
    refine (integrable_cellAmp (p i) (q i)).norm.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact ((contDiff_cellIntegrand (p i) (q i) (ξ i) (ζ i) 0).continuous.congr
        (fun w => by simp [pairAmp])).aestronglyMeasurable
    · simp [pairAmp, Circle.norm_smul]
  exact Integrable.fintype_prod (f := fun i w => pairAmp (p i) (q i) (ξ i) (ζ i) w) h

omit [DecidableEq ι] in
/-- The decoupling of the integral. -/
theorem multiInt_eq (μ : ℝ) {Φ Φh : (ι → ℝ) → ℂ} (hrep : IsFourierRep Φ Φh)
    (p q ξ ζ : ι → Mom d) :
    multiInt μ Φ p q ξ ζ = ∫ s, Φh s * ∏ i, cellInt (p i) (q i) (ξ i) (ζ i) (μ * s i) := by
  have hcont : ∀ i (t : ℝ), Continuous (fun w : Mom d × Mom d =>
      Real.fourierChar (inner ℝ w.1 (ξ i) + inner ℝ w.2 (ζ i) + t * inner ℝ w.1 w.2) •
        cellAmp (p i) (q i) w.1 w.2) :=
    fun i t => (contDiff_cellIntegrand (p i) (q i) (ξ i) (ζ i) t).continuous
  have : SigmaFinite (volume : Measure (ι → Mom d × Mom d)) := Measure.pi.sigmaFinite _
  have hjoint : Integrable (Function.uncurry fun (w : ι → Mom d × Mom d) (s : ι → ℝ) =>
      Φh s * (multiAmp p q ξ ζ w * ∏ i, (Real.fourierChar (s i * (μ * resVec w i)) : ℂ)))
      ((volume : Measure (ι → Mom d × Mom d)).prod volume) := by
    have hp := (integrable_multiAmp p q ξ ζ).mul_prod hrep.1
    refine hp.norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine ((hrep.1.aestronglyMeasurable.comp_snd).mul ?_)
      refine Continuous.aestronglyMeasurable ?_
      refine ((continuous_multiAmp p q ξ ζ).comp continuous_fst).mul
        (continuous_finsetProd _ fun i _ => ?_)
      refine (continuous_subtype_val.comp Real.continuous_fourierChar).comp ?_
      exact ((continuous_apply i).comp continuous_snd).mul
        (continuous_const.mul ((continuous_resVec_apply i).comp continuous_fst))
    · obtain ⟨w, s⟩ := z
      simp only [Function.uncurry_apply_pair, norm_mul, norm_prod_phase, mul_one]
      rw [mul_comm]
  calc multiInt μ Φ p q ξ ζ
      = ∫ w : ι → Mom d × Mom d, ∫ s, Φh s * (multiAmp p q ξ ζ w *
          ∏ i, (Real.fourierChar (s i * (μ * resVec w i)) : ℂ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only
        rw [hrep.2, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    _ = ∫ s, ∫ w : ι → Mom d × Mom d, Φh s * (multiAmp p q ξ ζ w *
          ∏ i, (Real.fourierChar (s i * (μ * resVec w i)) : ℂ)) := integral_integral_swap hjoint
    _ = ∫ s, Φh s * ∏ i, cellInt (p i) (q i) (ξ i) (ζ i) (μ * s i) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only
        rw [integral_const_mul]
        congr 1
        have hprod : ∀ w : ι → Mom d × Mom d, multiAmp p q ξ ζ w *
            ∏ i, (Real.fourierChar (s i * (μ * resVec w i)) : ℂ) =
            ∏ i, (Real.fourierChar (inner ℝ (w i).1 (ξ i) + inner ℝ (w i).2 (ζ i) +
              (μ * s i) * inner ℝ (w i).1 (w i).2) • cellAmp (p i) (q i) (w i).1 (w i).2) := by
          intro w
          rw [multiAmp, ← prod_mul_distrib]
          refine prod_congr rfl fun i _ => ?_
          exact pairAmp_mul_phase _ _ _ _ _ (by simp only [resVec]; ring)
        simp_rw [hprod]
        rw [integral_fintype_prod_volume_eq_prod (𝕜 := ℂ)
          (f := fun i (w : Mom d × Mom d) => Real.fourierChar (inner ℝ w.1 (ξ i) + inner ℝ w.2 (ζ i) +
            (μ * s i) * inner ℝ w.1 w.2) • cellAmp (p i) (q i) w.1 w.2)]
        refine prod_congr rfl fun i _ => ?_
        rw [cellInt_eq_prod]

end WaveTurbulence.ApproxNT
