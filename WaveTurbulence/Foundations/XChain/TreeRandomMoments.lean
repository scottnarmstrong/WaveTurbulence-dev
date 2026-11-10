/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeNormBounds
public import WaveTurbulence.Foundations.XChain.TreeRandomMeasurability
public import WaveTurbulence.Foundations.XChain.AllMomentPowers
public import WaveTurbulence.Foundations.XChain.InitialL1Moments
/-! All finite moments of literal tree terms from summable random data. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Tree terms inherit every finite moment from the data's absolute lattice sum. -/
theorem memLp_treeTerm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {d : ℕ} (L γ δ : ℝ) (p : ℕ) (S : TTree) (c : Ω → (Fin d → ℤ) → ℂ)
    (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : ℝ) (n : Fin d → ℤ) (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => treeTerm L γ δ p S (c ω) t n) (q : ℝ≥0∞) μ := by
  have hpow := memLp_pow_of_all (fun ω => ∑' n, ‖c ω n‖) hM
    (fun ω => tsum_nonneg fun n => norm_nonneg _) (Fintype.card (GLeaf (single S))) q hq
  have henv := hpow.const_mul (‖SysAPI.treePrefactor L γ δ d S‖ * SysAPI.boxVol S p t)
  apply henv.mono' (aestronglyMeasurable_treeTerm L γ δ p S c hcm hcs t n)
  exact hcs.mono (fun ω hω => norm_treeTerm_le_l1 L γ δ p S hω t n)

end WaveTurbulence.Induct
