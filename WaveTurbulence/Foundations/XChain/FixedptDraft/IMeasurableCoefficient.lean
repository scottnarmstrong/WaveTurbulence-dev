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

end WaveTurbulence.Fixedpt
