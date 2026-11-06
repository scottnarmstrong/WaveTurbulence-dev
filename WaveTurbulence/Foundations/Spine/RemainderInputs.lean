/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SchwartzCosetSummability
public import WaveTurbulence.Foundations.Spine.NormAssembly
public import WaveTurbulence.Foundations.Spine.IncoherentSourceType
/-! Convert the exact high-order layergarden remainder hypothesis to the source regular-object inputs. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem forty_dim_le_Lambda (P : WTParams) (hd : 1 ≤ P.d) {r : ℕ} (hr : r ≤ P.D) :
    40 * P.d ≤ P.Lambda r := by
  unfold WTParams.Lambda
  exact le_self_pow₀ (by omega : 1 ≤ 40 * P.d) (by omega)

theorem InputRemainder_of_RemainderBound (P : WTParams) (R : ℕ → Mom P.d → ℝ)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) {p r : ℕ} (hp : p ≤ P.D)
    (hR : RemainderBound P R p) (hr : r ≤ p) : InputRemainder P (R r) r := by
  have h40 := forty_dim_le_Lambda P hd (hr.trans hp)
  have hnonzero : P.Lambda r ≠ 0 := by omega
  have hbound : SNorm (P.Lambda r) (P.Lambda r) (fun k => (R r k : ℂ)) ≤
      ENNReal.ofReal (P.L ^ (-P.theta r)) := hR r hr
  have hC : 0 ≤ P.L ^ (-P.theta r) := Real.rpow_nonneg (by linarith) _
  have hc := contDiff_of_SNorm_bound hnonzero _ _ hbound
  exact SNorm_mono_bound h40 h40 _ hc _ hC hbound

theorem summable_inputsF_of_RemainderBound (P : WTParams) (R : ℕ → Mom P.d → ℝ)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) {p r : ℕ} (hp : p ≤ P.D)
    (hR : RemainderBound P R p) (hr : r ≤ p) (k : Mom P.d) :
    Summable (fun n : Fin P.d → ℤ => |inputsF P R r (k + latticePoint P.L n)|) := by
  have h40 := forty_dim_le_Lambda P hd (hr.trans hp)
  exact summable_abs_inputsF_coset P R hL r (by omega) (hR r hr) k

end WaveTurbulence.LGSpine
