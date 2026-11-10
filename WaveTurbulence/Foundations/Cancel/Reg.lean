/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Gauss

/-!
# The Gaussian principal value `[G]∫` (DH21 (gausspv))

`greg θ F = ∫ F(x) e^{-πθ²x²} dx`; DH21 (gausspv) (L1713) is `[G]∫ F = lim_{θ→0} greg θ F`.

* `tendsto_greg`: for `F ∈ L¹`, `greg θ F → ∫ F` (DH21 L1714: "if `F ∈ L¹` then `[G]∫` coincides with the
  usual Lebesgue integration").
* `greg_intervalIntegral`: `greg` commutes with an interval integral of a jointly continuous bounded
  integrand (Fubini). This moves the regularization through Volterra operators and kernel compositions.
* `greg_phase`: `greg θ (x ↦ e^{πiεxu}) = gk θ u` for `ε = ±1`.
* `greg_odd`: `greg θ F = 0` for odd `F`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral
open scoped Real Topology

namespace WaveTurbulence.Cancel

/-- **The Gaussian regularization** `∫ F(x) e^{-πθ²x²} dx` (DH21 (gausspv)). -/
@[expose] noncomputable def greg (θ : ℝ) (F : ℝ → ℂ) : ℂ := ∫ x, (gw θ x : ℂ) * F x

theorem gw_nonneg (θ x : ℝ) : 0 ≤ gw θ x := (gw_pos θ x).le

theorem tendsto_gw (x : ℝ) : Tendsto (fun θ => gw θ x) (𝓝[>] 0) (𝓝 1) := by
  have h : Continuous fun θ : ℝ => gw θ x := by unfold gw; fun_prop
  have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa [gw] using this

/-- **The regularization of an odd function vanishes.** -/
theorem greg_odd {θ : ℝ} {F : ℝ → ℂ} (hodd : ∀ x, F (-x) = -F x) : greg θ F = 0 := by
  unfold greg
  have h := integral_neg_eq_self (fun x => (gw θ x : ℂ) * F x) volume
  have e : (fun x => (gw θ (-x) : ℂ) * F (-x)) = fun x => -((gw θ x : ℂ) * F x) := by
    funext x; rw [hodd, show gw θ (-x) = gw θ x by simp [gw]]; ring
  simp only [e, MeasureTheory.integral_neg] at h
  have : (2 : ℂ) * ∫ x, (gw θ x : ℂ) * F x = 0 := by linear_combination -h
  simpa using this

end WaveTurbulence.Cancel
