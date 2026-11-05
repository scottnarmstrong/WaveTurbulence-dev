/- Copy of INDUCT ../induct/MeasurableCoefficient.lean (sha256 0e3da1cc3655208a7bd65df22cf3dc5d2fc83cf6828cd5a7f04b62d312b1b060); only the namespace and imports changed. -/
/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SysDraft.API
public import WaveTurbulence.Foundations.NLS.Measurability
/-! Measurability of chosen classed a-system coefficients on a measurable rapid-data event. -/
public section
namespace WaveTurbulence.Fixedpt
open MeasureTheory Set Filter Topology
open NLS
open scoped ENNReal
variable {d : ℕ}

theorem measurable_indicator_complex_comp_ofFun {ψ : L1 d → ℂ} (hψ : Continuous ψ) :
    Measurable ({c : (Fin d → ℤ) → ℂ | IsRapidDecay c}.indicator
      fun c => ψ (L1.ofFun (weightUp c))) := by
  set S := {c : (Fin d → ℤ) → ℂ | IsRapidDecay c}
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (Fin d → ℤ)))
    (f := fun F => S.indicator fun c =>
      ψ (∑ n ∈ F, lp.single (E := fun _ : Fin d → ℤ => ℂ) 1 n (weightUp c n)))
    (fun F => ((hψ.comp (continuous_sum_single_weightUp F)).measurable).indicator
      measurableSet_isRapidDecay) (tendsto_pi_nhds.2 fun c => ?_)
  by_cases hc : c ∈ S
  · simp only [indicator_of_mem hc]
    have h := lp.hasSum_single ENNReal.one_ne_top (L1.ofFun (weightUp c) : L1 d)
    simp only [L1.ofFun_apply (IsRapidDecay.summable_norm_weightUp hc)] at h
    exact (hψ.tendsto _).comp h
  · simp only [indicator_of_notMem hc]
    exact tendsto_const_nhds

/-- A pointwise chosen classed solution is measurable coefficientwise after restriction to a
measurable event with rapidly decreasing data. The proof uses continuous truncated flows. -/
theorem measurable_indicator_a_coefficient {Ω : Type*} [MeasurableSpace Ω]
    {L γ δ T : ℝ} (hL : 0 < L) (φ : Mom d → ℝ)
    {g : (Fin d → ℤ) → Ω → ℂ} (hg : ∀ n, Measurable (g n))
    (F : Set Ω) (hF : MeasurableSet F) (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hrapid : ∀ ω ∈ F, IsRapidDecay (initialCoeff L φ g ω))
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    Measurable (F.indicator fun ω => a ω t n) := by
  let ψ : ℕ → L1 d → ℂ := fun R x =>
    lp.evalCLM ℝ (fun _ : Fin d → ℤ => ℂ) 1 n (truncFlow L γ δ R T x t) / (flowWeight n : ℂ)
  have hψ (R : ℕ) : Continuous (ψ R) :=
    (((lp.evalCLM ℝ (fun _ : Fin d → ℤ => ℂ) 1 n).continuous.comp
      (continuous_truncFlow_data (Nat.cast_nonneg R) ht)).div_const _)
  refine measurable_of_tendsto_metrizable (f := fun R => F.indicator fun ω =>
    ({c : (Fin d → ℤ) → ℂ | IsRapidDecay c}.indicator fun c => ψ R (L1.ofFun (weightUp c)))
      (initialCoeff L φ g ω))
    (fun R => ((measurable_indicator_complex_comp_ofFun (hψ R)).comp
      (measurable_initialCoeff L φ hg)).indicator hF) (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ F
  · have hsol := SysAPI.IsASolution.toNLS (ha ω hω)
    have hc := hrapid ω hω
    obtain ⟨Y, hY⟩ := hsol.exists_norm_ofFun_le hL hc
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈Y⌉₊) fun R hR => ?_
    have hRY : ∀ s ∈ Icc 0 T,
        ‖(L1.ofFun (weightUp (a ω s)) : L1 d)‖ ≤ (R : ℝ) :=
      fun s hs => (hY s hs).trans ((Nat.le_ceil Y).trans (Nat.cast_le.mpr hR))
    rw [indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem hc]
    dsimp only [ψ]
    rw [hsol.truncFlow_eq hL hc hRY t ht]
    change (L1.ofFun (weightUp (a ω t)) : L1 d) n / (flowWeight n : ℂ) = a ω t n
    rw [L1.ofFun_apply (hsol.summable_norm_weightUp hL hc ht), weightUp,
      mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (flowWeight_pos n).ne')]
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

end WaveTurbulence.Fixedpt
