/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceExitAmplitude

/-!
# Sparse transforms of the actual selected source endpoint amplitudes

After the coordinate endpoint has been selected, only its input time
and the distinguished first time carry Fourier characters. The input
amplitudes retain the full actual local domain and all source cancellation.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- The sparse input character at the selected and distinguished input times. -/
@[expose] noncomputable def sourceExitPhase {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (v : D.S.TVar) (α ζ : ℝ) (u : D.S.TVar → ℝ) : ℂ :=
  Real.fourierChar (α*u v-ζ*u (firstTime D hI))

/-- The endpoint character depending only on the frequency and fixed source label. -/
@[expose] noncomputable def sourceExitOuterPhase {d : ℕ} (D : SumintDatum d)
    (upper : Bool) (v : D.S.TVar) (α : ℝ) : ℂ :=
  Real.fourierChar (-α*((D.q v:ℝ)+(if upper then 1 else 0)))

/-- The actual selected endpoint amplitude transformed in its two possible input coordinates. -/
@[expose] noncomputable def sourceExitTransform {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (F : (D.S.TVar → ℝ) → ℂ) (c h α ζ : ℝ) : ℂ :=
  ∫ u in localInputTimeDomain D c h, sourceExitAmplitude D hI upper v F u*sourceExitPhase D hI v α ζ u

/-- The sparse phase is continuous in all input coordinates. -/
theorem continuous_sourceExitPhase {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (v : D.S.TVar) (α ζ : ℝ) : Continuous (sourceExitPhase D hI v α ζ) := by
  unfold sourceExitPhase
  simp_rw [Real.fourierChar_apply]
  fun_prop

/-- Sparse and outer phases both have unit norm. -/
theorem norm_sourceExitPhase {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (v : D.S.TVar) (α ζ : ℝ) (u : D.S.TVar → ℝ) : ‖sourceExitPhase D hI v α ζ u‖ = 1 :=
  Circle.norm_coe _

/-- The outer endpoint phase has unit norm independently of every source label. -/
theorem norm_sourceExitOuterPhase {d : ℕ} (D : SumintDatum d)
    (upper : Bool) (v : D.S.TVar) (α : ℝ) : ‖sourceExitOuterPhase D upper v α‖ = 1 :=
  Circle.norm_coe _

/-- The actual sparse-transform integrand is integrable on the native local domain. -/
theorem integrableOn_sourceExitTransform_integrand {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (F : (D.S.TVar → ℝ) → ℂ) (hFm : Measurable F)
    (c h : ℝ) (hFi : IntegrableOn F (localInputTimeDomain D c h)) (α ζ : ℝ) :
    IntegrableOn (fun u => sourceExitAmplitude D hI upper v F u*sourceExitPhase D hI v α ζ u)
      (localInputTimeDomain D c h) :=
  (integrableOn_sourceExitAmplitude D hI upper v F hFm c h hFi).mul_bdd
    (continuous_sourceExitPhase D hI v α ζ).aestronglyMeasurable
    (ae_of_all _ (fun u => (norm_sourceExitPhase D hI v α ζ u).le))

/-- The coordinate term in the numerator is exactly the frequency-free amplitude times its sparse phases. -/
theorem selected_endpoint_term_eq {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (upper : Bool) (v : D.S.TVar) (F : (D.S.TVar → ℝ) → ℂ) (u : D.S.TVar → ℝ) (ξ : Fin 3 → ℝ) :
    (if lowerTimeExit D hI u ≤ upperTimeExit D hI u then
      F u*(timeExitWeight D hI upper v u:ℂ)*
        boxEndpointTerm (timeExitCoordinate D upper v u) (u (firstTime D hI)) ξ else 0) =
      sourceExitOuterPhase D upper v (ξ 0)*
        (sourceExitAmplitude D hI upper v F u*sourceExitPhase D hI v (ξ 0) (ξ 1+ξ 2) u) := by
  rw [source_boxEndpointTerm_eq_characters]
  unfold sourceExitAmplitude sourceExitOuterPhase sourceExitPhase
  split_ifs <;> push_cast <;> ring

/-- Exact sparse-coordinate decomposition of the actual input times its endpoint numerator. -/
theorem source_input_mul_endpoint_numerator_eq {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (F : (D.S.TVar → ℝ) → ℂ) (u : D.S.TVar → ℝ) (ξ : Fin 3 → ℝ) :
    F u*boxEndpointNumerator (lowerTimeExit D hI u) (upperTimeExit D hI u) (u (firstTime D hI)) ξ =
      (∑ v, sourceExitOuterPhase D true v (ξ 0)*
        (sourceExitAmplitude D hI true v F u*sourceExitPhase D hI v (ξ 0) (ξ 1+ξ 2) u))-
      (∑ v, sourceExitOuterPhase D false v (ξ 0)*
        (sourceExitAmplitude D hI false v F u*sourceExitPhase D hI v (ξ 0) (ξ 1+ξ 2) u)) := by
  have hp (upper : Bool) :
      (if lowerTimeExit D hI u ≤ upperTimeExit D hI u then
        F u*(∑ v, (timeExitWeight D hI upper v u:ℂ)*
          boxEndpointTerm (timeExitCoordinate D upper v u) (u (firstTime D hI)) ξ) else 0) =
      ∑ v, sourceExitOuterPhase D upper v (ξ 0)*
        (sourceExitAmplitude D hI upper v F u*sourceExitPhase D hI v (ξ 0) (ξ 1+ξ 2) u) := by
    by_cases hab : lowerTimeExit D hI u ≤ upperTimeExit D hI u
    · rw [ite_eq_left hab,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      have he := selected_endpoint_term_eq D hI upper v F u ξ
      rw [ite_eq_left hab] at he
      simpa only [mul_assoc] using he
    · simp only [sourceExitAmplitude,ite_eq_right hab,zero_mul,mul_zero,Finset.sum_const_zero]
  rw [source_boxEndpointNumerator_eq_weighted_sums]
  have he (a b : ℂ) (P : Prop) [Decidable P] :
      F u*(if P then a-b else 0) = (if P then F u*a else 0)-(if P then F u*b else 0) := by
    split_ifs <;> ring
  rw [he,hp true,hp false]

end WaveTurbulence.Sumint
