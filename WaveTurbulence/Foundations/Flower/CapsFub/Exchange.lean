/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Kernel
/-! # CAPS-FUBINI: exchange of an `R`-integral over a finite-volume set with the decoration `tsum`
of `kernelKgen` (generic weight family dominated by a summable-kernel weight). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsFub
open Finset MeasureTheory Set GraftGen

variable {w d : ℕ}

/-- The `R`-dependent summand of `kernelKgen` for a weight family `g`. -/
theorem kgf_norm_le (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d n nfl) (a G : ℝ) (h : |a| ≤ |G|) :
    ‖(a : ℂ) * kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ‖ ≤
      ‖(G : ℂ) * kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- **Generic exchange.** -/
theorem kernelKgen_integral_swap (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (S : Set (Fin w → ℝ)) (hS : MeasurableSet S) (hfin : volume S < ⊤)
    (g : (GNode LG.garden.tree → Mom d) → (Fin w → ℝ) → ℝ) (G : (GNode LG.garden.tree → Mom d) → ℝ)
    (hgm : ∀ k, Measurable (g k)) (hbd : ∀ k, ∀ R ∈ S, |g k R| ≤ |G k|)
    (hG : Summable (kernelGenFactor L γ δ F LG fix off G up k₀ (n := n) (nfl := nfl))) :
    IntegrableOn (fun R => kernelKgen L γ δ F LG fix off (fun k => g k R) up k₀ n nfl) S ∧
    kernelKgen L γ δ F LG fix off (fun k => ∫ R in S, g k R) up k₀ n nfl =
      ∫ R in S, kernelKgen L γ δ F LG fix off (fun k => g k R) up k₀ n nfl := by
  set B : GenDecoration LG.garden d n nfl → ℂ :=
    fun κ => kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ with hB
  set kk : GenDecoration LG.garden d n nfl → GNode LG.garden.tree → Mom d :=
    fun κ => cosetDecoration LG.garden L k₀ κ.1 with hkk
  set f : GenDecoration LG.garden d n nfl → (Fin w → ℝ) → ℂ :=
    fun κ R => (g (kk κ) R : ℂ) * B κ with hf
  have hfac : ∀ (wt : (GNode LG.garden.tree → Mom d) → ℝ) κ,
      kernelGenFactor L γ δ F LG fix off wt up k₀ κ = (wt (kk κ) : ℂ) * B κ :=
    fun wt κ => Flower.Polar.kernelGenFactor_eq_mul L γ δ F LG fix off wt up k₀ κ
  have hGn : Summable fun κ => ‖(G (kk κ) : ℂ) * B κ‖ := by
    have := hG.norm
    simpa only [hfac] using this
  have hfint : ∀ κ, IntegrableOn (fun R => f κ R) S := by
    intro κ
    have h1 : IntegrableOn (fun R => g (kk κ) R) S := by
      refine Measure.integrableOn_of_bounded (M := |G (kk κ)|) hfin.ne
        (hgm _).aestronglyMeasurable ?_
      rw [ae_restrict_iff' hS]
      exact Filter.Eventually.of_forall fun R hR => by simpa using hbd _ R hR
    have h2 : IntegrableOn (fun R => ((g (kk κ) R : ℝ) : ℂ)) S := h1.ofReal
    exact h2.mul_const _
  have hfnorm : ∀ κ, ∫ R in S, ‖f κ R‖ ≤ (volume S).toReal * ‖(G (kk κ) : ℂ) * B κ‖ := by
    intro κ
    have h := setIntegral_mono_on (μ := volume) (hfint κ).norm (integrableOn_const hfin.ne) hS
      (fun R hR => kgf_norm_le L γ δ F LG fix off up k₀ κ (g (kk κ) R) (G (kk κ)) (hbd _ R hR))
    rw [setIntegral_const] at h
    simpa [Measure.real, mul_comm] using h
  have hsumI : Summable fun κ => ∫ R in S, ‖f κ R‖ :=
    Summable.of_nonneg_of_le (fun κ => integral_nonneg fun R => norm_nonneg _) hfnorm
      (hGn.mul_left _)
  have hHas := hasSum_integral_of_summable_integral_norm (μ := volume.restrict S) hfint hsumI
  have hfm : ∀ κ, Measurable (f κ) := fun κ =>
    (Complex.measurable_ofReal.comp (hgm _)).mul_const _
  -- pointwise bound of the tsum on S
  have hfS : ∀ R ∈ S, ∀ κ, ‖f κ R‖ ≤ ‖(G (kk κ) : ℂ) * B κ‖ := fun R hR κ =>
    kgf_norm_le L γ δ F LG fix off up k₀ κ _ _ (hbd _ R hR)
  have hsumS : ∀ R ∈ S, Summable fun κ => f κ R := fun R hR =>
    Summable.of_norm_bounded hGn (hfS R hR)
  have hTmeas : AEStronglyMeasurable (fun R => ∑' κ, f κ R) (volume.restrict S) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun (s : Finset (GenDecoration LG.garden d n nfl)) R => ∑ κ ∈ s, f κ R) ?_ ?_
    · intro s
      exact (Finset.measurable_sum s fun κ _ => hfm κ).aestronglyMeasurable
    · rw [ae_restrict_iff' hS]
      exact Filter.Eventually.of_forall fun R hR => (hsumS R hR).hasSum
  have hTint : IntegrableOn (fun R => ∑' κ, f κ R) S := by
    refine (integrableOn_const (C := ∑' κ, ‖(G (kk κ) : ℂ) * B κ‖) hfin.ne).mono' hTmeas ?_
    rw [ae_restrict_iff' hS]
    exact Filter.Eventually.of_forall fun R hR =>
      (norm_tsum_le_tsum_norm ((hGn.of_nonneg_of_le (fun _ => norm_nonneg _) (hfS R hR)))).trans
        (Summable.tsum_le_tsum (hfS R hR) (hGn.of_nonneg_of_le (fun _ => norm_nonneg _) (hfS R hR)) hGn)
  have hK : ∀ R, kernelKgen L γ δ F LG fix off (fun k => g k R) up k₀ n nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta * ∑' κ, f κ R := by
    intro R
    rw [kernelKgen_eq_tsum]
    simp only [hfac]
    rfl
  have hK2 : kernelKgen L γ δ F LG fix off (fun k => ∫ R in S, g k R) up k₀ n nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta * ∑' κ, ∫ R in S, f κ R := by
    rw [kernelKgen_eq_tsum]
    congr 1
    refine tsum_congr fun κ => ?_
    rw [hfac]
    simp only [hf]
    rw [integral_mul_const, integral_complex_ofReal]
  refine ⟨?_, ?_⟩
  · simp_rw [hK]
    exact hTint.const_mul _
  · simp_rw [hK]
    rw [integral_const_mul, hK2, hHas.tsum_eq]

end WaveTurbulence.Flower.CapsFub
