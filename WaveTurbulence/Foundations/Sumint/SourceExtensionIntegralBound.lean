/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceExtensionRecombinationRegularity
public import WaveTurbulence.Foundations.Sumint.NormIntegralMinkowski
public import WaveTurbulence.Foundations.Sumint.NormScalar
public import WaveTurbulence.Foundations.Sumint.OutputMultiplier

/-!
# Spatial coefficient integration preserves the actual mixed extension bound

This auxiliary Minkowski estimate keeps the output supremum inside the
Fourier integral and uses the proved finite-rank product integrability.
-/

public section
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Sumint

/-- A uniform actual-extension bound survives integration against an integrable spatial coefficient. -/
theorem XNorm00_integral_weightedSourceExtension_le {α V : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] [Countable V] {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {L : ℝ} (hL : 0 < L) (γ δ η : ℝ)
    (hη : η ≤ 1/3) (p : D.S.VIdx → Fin d → ℝ) (ν : α → D.S.VIdx → Mom d)
    (hν : Measurable ν) (r : V → Mom d) (C : α → ℂ) (hCm : Measurable C)
    (hCi : Integrable C μ) (χ : α → V → ℂ) (hχ : ∀ v, Measurable (fun a => χ a v))
    (hχnorm : ∀ a v, ‖χ a v‖ ≤ 1) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ a, XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p (ν a) (r v) t) ≤ B) :
    XNorm00 θ (fun t v => ∫ a, C a*χ a v*
      weightedSourceExtension D hI N h L γ δ η p (ν a) (r v) t ∂μ) ≤
      (∫⁻ a, ‖C a‖ₑ ∂μ)*B := by
  let F := fun a t v => C a*χ a v*weightedSourceExtension D hI N h L γ δ η p (ν a) (r v) t
  have hm (v : V) : Measurable (fun q : α × (Fin 3 → ℝ) => F q.1 q.2 v) := by
    have hp : Measurable (Prod.fst : α × (Fin 3 → ℝ) → α) := measurable_fst
    have hc := (hCm.mul (hχ v)).comp hp
    exact hc.mul (measurable_weightedSourceExtension_joint D hI N h hL γ δ η hη p ν hν (r v))
  have hi (v : V) : Integrable (fun q : α × (Fin 3 → ℝ) => F q.1 q.2 v) (μ.prod volume) :=
    integrable_coefficient_weightedSourceExtension D hI N h hL γ δ η hη p ν hν (r v) C
      (fun a => χ a v) hCi (hχ v) (fun a => hχnorm a v)
  have hs (a : α) (v : V) : Integrable (fun t => F a t v) :=
    (integrable_weightedSourceExtension D hI N h hL γ δ η hη p (ν a) (r v)).const_mul _
  apply (XNorm00_integral_le θ F hm hi hs).trans
  calc
    _ ≤ ∫⁻ a, ‖C a‖ₑ*B ∂μ := by
      apply lintegral_mono
      intro a
      change XNorm00 θ (F a) ≤ ‖C a‖ₑ*B
      have he : F a = fun t v => C a • (χ a v*
          weightedSourceExtension D hI N h L γ δ η p (ν a) (r v) t) := by
        funext t v
        dsimp [F]
        simp only [mul_assoc]
      rw [he,XNorm00_smul]
      apply mul_le_mul' le_rfl
      exact (XNorm00_output_mul_le θ _ (χ a) (fun v => by
        rw [← ofReal_norm]
        exact (ENNReal.ofReal_le_ofReal (hχnorm a v)).trans_eq ENNReal.ofReal_one)).trans (hF a)
    _ = _ := lintegral_mul_const _ hCm.enorm

end WaveTurbulence.Sumint
