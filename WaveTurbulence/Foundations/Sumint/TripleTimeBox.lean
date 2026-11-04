/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PairBoxIntegral
import Mathlib.Tactic

/-!
# Exact normal-time box measure with the third time integrated last

The normal sum's spatial modulations are fixed by its third time.
The coordinate permutation z ↦ (z₂,z₀,z₁) preserves Lebesgue measure,
giving the exact outer-third-time integration order of the landed bound.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- Put the normal third time first in the product-space integration order. -/
@[expose] def tripleTimeEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × ℝ × ℝ where
  toFun z := (z 2,z 0,z 1)
  invFun z := ![z.2.1,z.2.2,z.1]
  left_inv z := by funext j; fin_cases j <;> rfl
  right_inv z := by rcases z with ⟨u,v,w⟩; rfl
  measurable_toFun := by
    change Measurable (fun z : Fin 3 → ℝ => (z 2,z 0,z 1))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × ℝ × ℝ => ![z.2.1,z.2.2,z.1])
    fun_prop

/-- The coordinate permutation preserves the actual product Lebesgue measure. -/
theorem volume_preserving_tripleTimeEquiv : MeasurePreserving tripleTimeEquiv volume volume := by
  let e := tripleTimeEquiv
  have hi : MeasurePreserving e.symm volume volume := by
    refine ⟨e.symm.measurable,(Measure.pi_eq fun s hs => ?_).symm⟩
    have hp : e.symm ⁻¹' Set.pi Set.univ s = s 2 ×ˢ (s 0 ×ˢ s 1) := by
      ext z
      simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_prod]
      constructor
      · intro h
        exact ⟨h 2,h 0,h 1⟩
      · rintro ⟨h2,h0,h1⟩ j
        fin_cases j
        · exact h0
        · exact h1
        · exact h2
    rw [e.symm.map_apply,hp]
    simp only [Measure.volume_eq_prod,Measure.prod_prod,Fin.prod_univ_three]
    ring
  exact MeasurePreserving.symm e.symm hi

/-- The normal box is exactly the inverse image of its third/first/second product box. -/
theorem preimage_triple_time_box (lo hi : Fin 3 → ℝ) :
    tripleTimeEquiv ⁻¹' (Icc (lo 2) (hi 2) ×ˢ (Icc (lo 0) (hi 0) ×ˢ Icc (lo 1) (hi 1))) = Icc lo hi := by
  ext z
  constructor
  · rintro ⟨h2,h0,h1⟩
    constructor <;> intro j <;> fin_cases j
    · exact h0.1
    · exact h1.1
    · exact h2.1
    · exact h0.2
    · exact h1.2
    · exact h2.2
  · intro h
    exact ⟨⟨h.1 2,h.2 2⟩,⟨h.1 0,h.2 0⟩,⟨h.1 1,h.2 1⟩⟩

/-- Exact nonnegative normal-box Fubini in the outer-third-time order. -/
theorem lintegral_triple_time_box (f : (Fin 3 → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (lo hi : Fin 3 → ℝ) :
    (∫⁻ z in Icc lo hi, f z) =
      ∫⁻ s₂ in Icc (lo 2) (hi 2), ∫⁻ s₀ in Icc (lo 0) (hi 0),
        ∫⁻ s₁ in Icc (lo 1) (hi 1), f ![s₀,s₁,s₂] := by
  let B := Icc (lo 2) (hi 2) ×ˢ (Icc (lo 0) (hi 0) ×ˢ Icc (lo 1) (hi 1))
  have hB : MeasurableSet B := measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hp := volume_preserving_tripleTimeEquiv.restrict_preimage hB
  rw [preimage_triple_time_box] at hp
  have he := hp.lintegral_comp_emb tripleTimeEquiv.measurableEmbedding (fun z => f (tripleTimeEquiv.symm z))
  simp only [MeasurableEquiv.symm_apply_apply] at he
  rw [he]
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  have hm : Measurable (fun z : ℝ × ℝ × ℝ => f (tripleTimeEquiv.symm z)) := hf.comp tripleTimeEquiv.symm.measurable
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro s₂
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  exact lintegral_prod _ ((hm.comp (measurable_const.prodMk measurable_id)).aemeasurable)

/-- Exact real normal-box Fubini in the same outer-third-time order. -/
theorem integral_triple_time_box (f : (Fin 3 → ℝ) → ℝ) (hf : Continuous f)
    (lo hi : Fin 3 → ℝ) :
    (∫ z in Icc lo hi, f z) =
      ∫ s₂ in Icc (lo 2) (hi 2), ∫ s₀ in Icc (lo 0) (hi 0),
        ∫ s₁ in Icc (lo 1) (hi 1), f ![s₀,s₁,s₂] := by
  let B := Icc (lo 2) (hi 2) ×ˢ (Icc (lo 0) (hi 0) ×ˢ Icc (lo 1) (hi 1))
  have hB : MeasurableSet B := measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hp := volume_preserving_tripleTimeEquiv.restrict_preimage hB
  rw [preimage_triple_time_box] at hp
  have he := hp.integral_comp' (fun z => f (tripleTimeEquiv.symm z))
  simp only [MeasurableEquiv.symm_apply_apply] at he
  rw [he]
  change (∫ z in B, f ![z.2.1,z.2.2,z.1]) = _
  have hc : Continuous (fun z : ℝ × ℝ × ℝ => f ![z.2.1,z.2.2,z.1]) := hf.comp (by fun_prop)
  have hIB : IntegrableOn (fun z : ℝ × ℝ × ℝ => f ![z.2.1,z.2.2,z.1]) B :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  rw [Measure.volume_eq_prod] at hIB ⊢
  rw [setIntegral_prod _ hIB]
  apply integral_congr_ae
  exact ae_of_all _ (fun s₂ => by
    have hc₂ : Continuous (fun z : ℝ × ℝ => f ![z.1,z.2,s₂]) := hf.comp (by fun_prop)
    have hi₂ : IntegrableOn (fun z : ℝ × ℝ => f ![z.1,z.2,s₂])
        (Icc (lo 0) (hi 0) ×ˢ Icc (lo 1) (hi 1)) :=
      hc₂.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    rw [Measure.volume_eq_prod] at hi₂ ⊢
    exact setIntegral_prod _ hi₂)

/-- Real and nonnegative normal-box integrals agree for continuous nonnegative factors. -/
theorem ofReal_integral_triple_time_box (f : (Fin 3 → ℝ) → ℝ) (hf : Continuous f)
    (hn : ∀ z, 0 ≤ f z) (lo hi : Fin 3 → ℝ) :
    ENNReal.ofReal (∫ s₂ in Icc (lo 2) (hi 2), ∫ s₀ in Icc (lo 0) (hi 0),
      ∫ s₁ in Icc (lo 1) (hi 1), f ![s₀,s₁,s₂]) =
      ∫⁻ z in Icc lo hi, ENNReal.ofReal (f z) := by
  rw [← integral_triple_time_box f hf lo hi]
  exact ofReal_integral_eq_lintegral_ofReal hf.integrableOn_Icc (ae_of_all _ hn)

end WaveTurbulence.Sumint
