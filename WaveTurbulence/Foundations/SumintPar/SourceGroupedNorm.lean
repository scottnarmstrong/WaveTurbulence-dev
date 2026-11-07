/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTimeNormFactors
public import WaveTurbulence.Foundations.SumintPar.CutoffPhaseSumRegularity
public import WaveTurbulence.Foundations.SumintPar.GroupedTimeMeasure

/-!
# The literal source norm in grouped time-family coordinates

The distinguished linear factors, pairs with their case-(c) gap
amplitudes, and normal triples are written in the exact Tonelli order.
All time modulation parameters remain in the zero-input phase and drop
out of its norm, as established by the literal phase identity.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- The exact cutoff source norm as a function of the grouped time families. -/
@[expose] noncomputable def groupedSourceNorm {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (z : GroupedTimes D.S) : ℝ :=
  (∏ i : Fin D.S.I, ‖linearTimeSum D L γ δ p ν r t i (z.1 i)‖) *
  (∏ a : Σ i : Fin D.S.I, Fin (D.S.m i),
    pairGapAmplitude D η a (z.2.1 a)*‖pairTimeSum D L γ δ p ν r t a (z.2.1 a)‖) *
  (∏ i : {i : Fin D.S.I // D.S.nor i = true}, ‖normalTimeSum D L γ δ p ν r t i (z.2.2 i)‖)

/-- The actual source cutoff norm is the explicit grouped product. -/
theorem norm_cutoffPhaseSum_eq_groupedSourceNorm {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ =
      groupedSourceNorm D L γ δ η p ν r t (measurableTimeGrouping D.S τ) := by
  classical
  rw [norm_cutoffPhaseSum_eq_time_factor_product D hL γ δ η p ν r t τ,
    Fintype.prod_sum_type,Fintype.prod_sum_type]
  simp only [sourceTimeNormFactor,timeGapFactor,plainTimeNormFactor,one_mul]
  change _ = (∏ i : Fin D.S.I, ‖linearTimeSum D L γ δ p ν r t i (τ (.inl ⟨i,0⟩))‖) *
    (∏ a : Σ i : Fin D.S.I, Fin (D.S.m i),
      pairGapAmplitude D η a (τ (.inl ⟨a.1,a.2.succ⟩),τ (.inr (.inl a)))*
        ‖pairTimeSum D L γ δ p ν r t a (τ (.inl ⟨a.1,a.2.succ⟩),τ (.inr (.inl a)))‖) *
    (∏ i : {i : Fin D.S.I // D.S.nor i = true},
      ‖normalTimeSum D L γ δ p ν r t i (fun j => τ (.inr (.inr ⟨i,j⟩)))‖)
  have hx (a : Σ i : Fin D.S.I, Fin (D.S.m i)) := (timeCoordinateGrouping_pair D.S τ a).1
  have hy (a : Σ i : Fin D.S.I, Fin (D.S.m i)) := (timeCoordinateGrouping_pair D.S τ a).2
  have hn (i : {i : Fin D.S.I // D.S.nor i = true}) :
      timeCoordinateGrouping D.S τ (.inr (.inr i)) = fun j => τ (.inr (.inr ⟨i,j⟩)) :=
    funext (fun j => timeCoordinateGrouping_normal D.S τ i j)
  simp_rw [timeCoordinateGrouping_linear,hx,hy,hn]
  ring

/-- The explicit grouped source norm is measurable under its actual product time measure. -/
theorem measurable_groupedSourceNorm {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) :
    Measurable (groupedSourceNorm D L γ δ η p ν r t) := by
  have he (z : GroupedTimes D.S) : groupedSourceNorm D L γ δ η p ν r t z =
      ‖cutoffPhaseSum D L γ δ η p ν r t ((measurableTimeGrouping D.S).symm z)‖ := by
    rw [norm_cutoffPhaseSum_eq_groupedSourceNorm D hL γ δ η p ν r t]
    rw [MeasurableEquiv.apply_symm_apply]
  rw [funext he]
  exact (measurable_cutoffPhaseSum D hL γ δ η p ν r t).norm.comp
    (measurableTimeGrouping D.S).symm.measurable

/-- Exact time-family integral representation of the actual nonnegative source norm. -/
theorem lintegral_norm_cutoffPhaseSum_grouped {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) :
    (∫⁻ τ : D.S.TVar → ℝ, ENNReal.ofReal ‖cutoffPhaseSum D L γ δ η p ν r t τ‖) =
      ∫⁻ u : Fin D.S.I → ℝ,
        ∫⁻ q : (Σ i : Fin D.S.I, Fin (D.S.m i)) → ℝ × ℝ,
          ∫⁻ n : {i : Fin D.S.I // D.S.nor i = true} → Fin 3 → ℝ,
            ENNReal.ofReal (groupedSourceNorm D L γ δ η p ν r t (u,q,n)) := by
  simp_rw [norm_cutoffPhaseSum_eq_groupedSourceNorm D hL γ δ η p ν r t]
  exact lintegral_grouped_time_families D.S _
    (ENNReal.measurable_ofReal.comp (measurable_groupedSourceNorm D hL γ δ η p ν r t))

end WaveTurbulence.SumintPar
