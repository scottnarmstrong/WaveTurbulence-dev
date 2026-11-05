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

/-- In particular Gaussian Schwartz initial coefficients satisfy all tree moment side conditions. -/
theorem memLp_treeTerm_initial {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (φ : SchwartzMap (Mom d) ℝ) (g : (Fin d → ℤ) → Ω → ℂ)
    (hg : ∀ n, HasLaw (g n) stdComplexGaussian μ) (p : ℕ) (S : TTree)
    (t : ℝ) (n : Fin d → ℤ) (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => treeTerm L γ δ p S (initialCoeff L φ g ω) t n) (q : ℝ≥0∞) μ := by
  have hcm (n : Fin d → ℤ) : AEStronglyMeasurable (fun ω => initialCoeff L φ g ω n) μ :=
    (hg n).aemeasurable.aestronglyMeasurable.const_mul _
  have hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖initialCoeff L φ g ω n‖ := by
    filter_upwards [Probability.ae_initialCoeff_isRapidDecay hL φ g hg] with ω hω
    simpa only [pow_zero, mul_one] using hω.summable_norm_mul_pow 0
  exact memLp_treeTerm L γ δ p S (initialCoeff L φ g) hcm hcs
    (fun q hq => memLp_initial_l1 hL φ g hg q hq) t n q hq

end WaveTurbulence.Induct
