/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.NormalizedWeyl
public import WaveTurbulence.Foundations.WeylSums.RefinedMomentPowers

/-! # Refined moments of the normalized nonzero-rational part -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- The nonzero part retains the denominator gain on every finite time window. -/
theorem exists_nonzeroWeylPart_moment_bound (a ρ : ℝ) (_ha : 2 < a)
    (hρ : 0 < ρ) (hρa : ρ < a-2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T : ℝ, 2 ≤ M → 0 < T →
      IntegrableOn (fun t => nonzeroWeylPart M t^a) {t : ℝ | |t| ≤ T} ∧
      (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^a) ≤
        C*M^(a-2)*T^(a-1-ρ) := by
  obtain ⟨C,hC,hb⟩ := exists_weylSupremum_refined_moment (2*a) ρ (by linarith) hρ (by linarith)
  refine ⟨C,hC,?_⟩
  intro M T hM hT
  have hMp : 0 < M := by linarith
  have hap : 0 < a := by linarith
  let S := {t : ℝ | 1/M < |t|}
  let W := {t : ℝ | |t| ≤ T}
  let R := {t : ℝ | 1/M ≤ |t| ∧ |t| ≤ T}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hpow (t : ℝ) : normalizedWeyl M t^a = weylSupremum M t^(2*a)/M^a := by
    dsimp [normalizedWeyl]
    rw [Real.div_rpow (sq_nonneg _) hMp.le, ← Real.rpow_two, ← Real.rpow_mul (weylSupremum_nonneg hMp t)]
  have hNpow : (fun t => nonzeroWeylPart M t^a) = S.indicator (fun t => weylSupremum M t^(2*a)/M^a) := by
    funext t
    change (S.indicator (normalizedWeyl M) t)^a = _
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht,indicator_of_mem ht,hpow]
    · rw [indicator_of_notMem ht,indicator_of_notMem ht,Real.zero_rpow hap.ne']
  obtain ⟨hiRaw,hRaw⟩ := hb M T hM hT
  have hiDiv : IntegrableOn (fun t => weylSupremum M t^(2*a)/M^a) R := hiRaw.div_const _
  have hsub : S ∩ W ⊆ R := fun t ht => ⟨ht.1.le,ht.2⟩
  have hi : IntegrableOn (fun t => nonzeroWeylPart M t^a) W := by
    rw [hNpow]
    exact (integrableOn_indicator_iff hS.nullMeasurableSet).mpr (hiDiv.mono_set hsub)
  refine ⟨hi,?_⟩
  rw [hNpow,setIntegral_indicator hS]
  calc
    _ ≤ ∫ t in R, weylSupremum M t^(2*a)/M^a := setIntegral_mono_set hiDiv
      (Filter.Eventually.of_forall (fun t => div_nonneg (Real.rpow_nonneg (weylSupremum_nonneg hMp t) _) (by positivity)))
      (Filter.Eventually.of_forall (fun t ht => hsub ⟨ht.2,ht.1⟩))
    _ = (∫ t in R, weylSupremum M t^(2*a))/M^a := integral_div _ _
    _ ≤ (C*M^(2*a-2)*T^((2*a)/2-1-ρ))/M^a :=
      div_le_div_of_nonneg_right hRaw (by positivity)
    _ = C*M^(a-2)*T^(a-1-ρ) := by
      have heq : (2*a)/2-1-ρ = a-1-ρ := by ring
      rw [heq]
      have hMpow : M^(2*a-2)/M^a = M^(a-2) := by
        rw [← Real.rpow_sub hMp]
        congr 1
        ring
      calc
        _ = C*(M^(2*a-2)/M^a)*T^(a-1-ρ) := by ring
        _ = _ := by rw [hMpow]

end WaveTurbulence.WeylSums
