/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Statement
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier inversion for the amplitude `W` on `(ℝ^d)^{2n}` (packet NT6)

`(Fin n → ℝ^d) × (Fin n → ℝ^d)` is identified with the Euclidean space on
`(Fin n × Fin d) ⊕ (Fin n × Fin d)` by a volume-preserving linear map under which the inner product
is `∑_j ⟨x_j, ξ_j⟩ + ⟨y_j, η_j⟩`. Mathlib's Fourier inversion theorem then gives, for continuous
integrable `W` with integrable `Ŵ`,
`W(x,y) = ∫ Ŵ(ξ,η) e(∑_j ⟨x_j,ξ_j⟩ + ⟨y_j,η_j⟩) dξ dη`.
-/

public section

noncomputable section

open MeasureTheory WithLp Finset
open scoped FourierTransform

namespace WaveTurbulence.ApproxNT

variable {d n : ℕ}

/-- Flattening `n` momenta to `n·d` coordinates. -/
@[expose] def flatE (n d : ℕ) : (Fin n → Mom d) ≃ᵐ (Fin n × Fin d → ℝ) :=
  (MeasurableEquiv.piCongrRight fun _ => (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm).trans
    (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm

theorem flatE_apply (x : Fin n → Mom d) (p : Fin n × Fin d) : flatE n d x p = x p.1 p.2 := rfl

theorem measurePreserving_uncurry (n d : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm := by
  let e := (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm
  refine ⟨e.measurable, ?_⟩
  change Measure.map e volume = Measure.pi (fun _ : Fin n × Fin d => (volume : Measure ℝ))
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [e.map_apply]
  have he : e ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i : Fin n => Set.univ.pi (fun j : Fin d => s (i, j))) := by
    ext x
    simp [e, MeasurableEquiv.coe_curry_symm, Function.uncurry_def, Prod.forall]
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi]
  exact (Fintype.prod_prod_type (fun p : Fin n × Fin d => volume (s p))).symm

theorem measurePreserving_flatE : MeasurePreserving (flatE n d) := by
  refine MeasurePreserving.trans ?_ (measurePreserving_uncurry n d)
  exact volume_preserving_pi fun _ => (PiLp.volume_preserving_toLp (Fin d)).symm
    (MeasurableEquiv.toLp 2 (Fin d → ℝ))

/-- The Euclidean space of a pair of `n`-tuples of momenta. -/
abbrev PairSpace (n d : ℕ) := EuclideanSpace ℝ ((Fin n × Fin d) ⊕ (Fin n × Fin d))

/-- The identification of pairs of momentum tuples with `PairSpace`. -/
@[expose] def pairE (n d : ℕ) : (Fin n → Mom d) × (Fin n → Mom d) ≃ᵐ PairSpace n d :=
  ((flatE n d).prodCongr (flatE n d)).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin n × Fin d) ⊕ (Fin n × Fin d) => ℝ)).symm.trans
      (MeasurableEquiv.toLp 2 _))

theorem pairE_apply_inl (z : (Fin n → Mom d) × (Fin n → Mom d)) (p : Fin n × Fin d) :
    pairE n d z (Sum.inl p) = z.1 p.1 p.2 := rfl

theorem pairE_apply_inr (z : (Fin n → Mom d) × (Fin n → Mom d)) (p : Fin n × Fin d) :
    pairE n d z (Sum.inr p) = z.2 p.1 p.2 := rfl

theorem measurePreserving_pairE : MeasurePreserving (pairE n d) := by
  refine MeasurePreserving.trans (measurePreserving_flatE.prod measurePreserving_flatE) ?_
  refine MeasurePreserving.trans ?_ (PiLp.volume_preserving_toLp _)
  exact (measurePreserving_sumPiEquivProdPi (fun _ : (Fin n × Fin d) ⊕ (Fin n × Fin d) =>
    (volume : Measure ℝ))).symm _

theorem inner_pairE (z w : (Fin n → Mom d) × (Fin n → Mom d)) :
    inner ℝ (pairE n d z) (pairE n d w) =
      ∑ j, (inner ℝ (z.1 j) (w.1 j) + inner ℝ (z.2 j) (w.2 j)) := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type, sum_add_distrib]
  simp only [pairE_apply_inl, pairE_apply_inr, Fintype.sum_prod_type, PiLp.inner_apply]

theorem pairE_symm_apply (v : PairSpace n d) :
    (pairE n d).symm v = (fun j => toLp 2 (fun i => v (Sum.inl (j, i))),
      fun j => toLp 2 (fun i => v (Sum.inr (j, i)))) := by
  apply (pairE n d).injective
  rw [MeasurableEquiv.apply_symm_apply]
  ext k
  rcases k with ⟨j, i⟩ | ⟨j, i⟩ <;> rfl

theorem continuous_pairE_symm : Continuous (pairE n d).symm := by
  have h : ⇑(pairE n d).symm = fun v : PairSpace n d =>
      ((fun j => toLp 2 (fun i => v (Sum.inl (j, i))) : Fin n → Mom d),
        (fun j => toLp 2 (fun i => v (Sum.inr (j, i))) : Fin n → Mom d)) := by
    funext v; exact pairE_symm_apply v
  rw [h]
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_)
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
      (PiLp.continuous_apply 2 _ (Sum.inl (j, i))))
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
      (PiLp.continuous_apply 2 _ (Sum.inr (j, i))))

theorem fourierW_eq_fourier {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (τ : (Fin n → Mom d) × (Fin n → Mom d)) :
    fourierW W τ.1 τ.2 = 𝓕 (Function.uncurry W ∘ (pairE n d).symm) (pairE n d τ) := by
  rw [Real.fourier_eq, fourierW, ← measurePreserving_pairE.integral_comp
    (pairE n d).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply, inner_pairE]
  rfl

/-- The Fourier transform of an integrable `W` is continuous. -/
theorem continuous_fourierW {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hi : Integrable (Function.uncurry W)) :
    Continuous (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2) := by
  have hgi : Integrable (Function.uncurry W ∘ (pairE n d).symm) :=
    (measurePreserving_pairE.symm.integrable_comp_emb (pairE n d).symm.measurableEmbedding).2 hi
  have hc : Continuous (𝓕 (Function.uncurry W ∘ (pairE n d).symm)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hgi
  have hpe : Continuous (pairE n d) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
    rcases k with ⟨j, i⟩ | ⟨j, i⟩
    · exact (PiLp.continuous_apply 2 _ i).comp ((continuous_apply j).comp continuous_fst)
    · exact (PiLp.continuous_apply 2 _ i).comp ((continuous_apply j).comp continuous_snd)
  exact (hc.comp hpe).congr fun τ => (fourierW_eq_fourier τ).symm

/-- Fourier inversion for `W`. -/
theorem fourierW_inversion {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hc : Continuous (Function.uncurry W)) (hi : Integrable (Function.uncurry W))
    (hF : Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW W τ.1 τ.2))
    (x y : Fin n → Mom d) :
    W x y = ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
      (𝐞 (∑ j, (inner ℝ (x j) (τ.1 j) + inner ℝ (y j) (τ.2 j))) : ℂ) := by
  set g : PairSpace n d → ℂ := Function.uncurry W ∘ (pairE n d).symm
  have hmp := measurePreserving_pairE (n := n) (d := d)
  have hgc : Continuous g := hc.comp continuous_pairE_symm
  have hgi : Integrable g := (hmp.symm.integrable_comp_emb (pairE n d).symm.measurableEmbedding).2 hi
  have hFg : ∀ τ, 𝓕 g (pairE n d τ) = fourierW W τ.1 τ.2 := by
    intro τ
    rw [Real.fourier_eq, fourierW, ← hmp.integral_comp (pairE n d).measurableEmbedding]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [g, Function.comp_apply, MeasurableEquiv.symm_apply_apply, inner_pairE]
    rfl
  have hFgi : Integrable (𝓕 g) := by
    have h := (hmp.symm.integrable_comp_emb (pairE n d).symm.measurableEmbedding).2 hF
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Function.comp_apply]
    rw [← hFg, MeasurableEquiv.apply_symm_apply]
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hgc hgi hFgi) (pairE n d (x, y))
  rw [Real.fourierInv_eq, ← hmp.integral_comp (pairE n d).measurableEmbedding] at hinv
  have hgxy : g (pairE n d (x, y)) = W x y := by
    simp [g, Function.uncurry_apply_pair]
  rw [← hgxy, ← hinv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [hFg, Circle.smul_def, smul_eq_mul, inner_pairE]
  rw [mul_comm]
  congr 3
  refine sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (τ.1 j), real_inner_comm (τ.2 j)]

end WaveTurbulence.ApproxNT
