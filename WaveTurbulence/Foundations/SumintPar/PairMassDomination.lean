/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorMasses
public import WaveTurbulence.Foundations.SumintPar.SourceMassWindows
public import WaveTurbulence.Foundations.SumintPar.SourceWindowGeometry
public import WaveTurbulence.Foundations.SumintPar.OrderedPairClasses

/-!
# Discarding pair restrictions while retaining the source gap bound

The case-(c) first-pair amplitude is bounded by the maximum physical
input gap. All other pair amplitudes are one. This is used only for the
incoherence comparison, alongside the stronger bad-pair estimate.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- The pair mass with neither an ordering restriction nor a gap amplitude. -/
@[expose] noncomputable def plainPairMass {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (lo hi : D.S.TVar → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : ℝ≥0∞ :=
  ∫⁻ z in Icc (lo (.inl ⟨a.1,a.2.succ⟩),lo (.inr (.inl a)))
    (hi (.inl ⟨a.1,a.2.succ⟩),hi (.inr (.inl a))), ‖pairTimeSum D L γ δ p ν r t a z‖ₑ

/-- The maximum source gap costs a factor only at case-(c) first pairs. -/
@[expose] noncomputable def pairGapBound {d : ℕ} (D : SumintDatum d) (η : ℝ) (N : ℕ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) : ℝ :=
  if caseCPair D a then ((N:ℝ)+2)^(1-3*η) else 1

/-- Discarding an ordering restriction can only increase its nonnegative pair factor. -/
theorem orderedPairNorm_le_unrestricted {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (z : ℝ × ℝ) :
    orderedPairNorm D L γ δ η p ν r t u a z ≤
      pairGapAmplitude D η a z*‖pairTimeSum D L γ δ p ν r t a z‖ := by
  unfold orderedPairNorm
  split_ifs <;> first
    | exact le_rfl
    | exact mul_nonneg (pairGapAmplitude_nonneg D η a z) (norm_nonneg _)

/-- The literal gap amplitude is bounded on the actual enlarged pair box. -/
theorem pairGapAmplitude_le_bound {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hη : 0 ≤ 1-3*η)
    (c : ℝ) {h : ℝ} (hh : h ≤ 1) (a : Σ i : Fin D.S.I, Fin (D.S.m i))
    (z : ℝ × ℝ) (hz : z ∈ Icc
      (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeLower D c h (.inr (.inl a)))
      (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeUpper D c h (.inr (.inl a)))) :
    pairGapAmplitude D η a z ≤ pairGapBound D η N a := by
  by_cases hc : caseCPair D a
  · rw [pairGapAmplitude_eq_rpow_of_caseCPair D η a hc,pairGapBound,ite_eq_left hc]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hη
    exact enlarged_input_gap_le (admissible_time_label_lt D hD (.inl ⟨a.1,a.2.succ⟩))
      (admissible_time_label_lt D hD (.inr (.inl a))) hh
      ⟨hz.1.1,hz.2.1⟩ ⟨hz.1.2,hz.2.2⟩
  · rw [pairGapAmplitude_eq_one_of_not_caseCPair D η a hc,pairGapBound,ite_eq_right hc]

/-- The ordered pair mass is bounded by its plain mass times the explicit physical gap factor. -/
theorem orderedPairMass_le_gapBound_mul_plain {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hη : 0 ≤ 1-3*η)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
    {h : ℝ} (hh : h ≤ 1) (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) :
    orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a ≤
      ENNReal.ofReal (pairGapBound D η N a)*
        plainPairMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) a := by
  unfold orderedPairMass plainPairMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
  rw [← ofReal_norm,← ENNReal.ofReal_mul (by unfold pairGapBound; split_ifs <;> positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact (orderedPairNorm_le_unrestricted D L γ δ η p ν r t u a z).trans
    (mul_le_mul_of_nonneg_right (pairGapAmplitude_le_bound D hD hη c hh a z hz) (norm_nonneg _))

end WaveTurbulence.SumintPar
