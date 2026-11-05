/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
/-! Lp control of weighted countable random sums, for the all-order ansatz integrability. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory
open scoped ENNReal

/-- An absolutely summable series of Lp norms defines an Lp random variable. -/
theorem memLp_tsum_of_norm_sum {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ι → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) p μ) (hs : ∑' i, eLpNorm (f i) p μ ≠ ⊤) :
    MemLp (fun ω => ∑' i, f i ω) p μ := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let F : ι → Lp ℝ p μ := fun i => (hf i).toLp (f i)
  have hF : ∑' i, ‖F i‖ₑ ≠ ⊤ := by simpa only [F, Lp.enorm_toLp] using hs
  have hae : (⇑(∑' i, F i)) =ᵐ[μ] fun ω => ∑' i, f i ω := by
    filter_upwards [Lp.coeFn_tsum hF, ae_all_iff.mpr (fun i => (hf i).coeFn_toLp)] with ω hω hcoeff
    exact hω.trans (tsum_congr hcoeff)
  exact (Lp.memLp (∑' i, F i)).ae_eq hae

/-- A summable deterministic envelope times random variables with uniformly bounded Lp norms
has every finite Lp moment available from that uniform bound. -/
theorem memLp_weighted_tsum {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ι → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) p μ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsa : Summable a)
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hbound : ∀ i, eLpNorm (f i) p μ ≤ K) :
    MemLp (fun ω => ∑' i, a i * f i ω) p μ := by
  apply memLp_tsum_of_norm_sum hp _ (fun i => (hf i).const_mul (a i))
  have he (i : ι) : eLpNorm (fun ω => a i * f i ω) p μ ≤ ENNReal.ofReal (a i) * K := by
    change eLpNorm (a i • f i) p μ ≤ _
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg (ha i)]
    exact mul_le_mul' le_rfl (hbound i)
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum he)
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top hsa.tsum_ofReal_ne_top hK

end WaveTurbulence.Induct
