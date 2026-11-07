/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB4
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: interchange of the mode sum and the decoration sum (abstract form)

`hasSum_tsum_interchange`: a family `Tm ξ κ` dominated by `kb ξ (e κ)` with uniformly bounded sums, whose weighted
pointwise mode series converges to `T0 κ`, has `Σ_κ T0 κ = Σ_ξ w_ξ Σ_κ Tm ξ κ`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open MeasureTheory

theorem hasSum_tsum_interchange {ι κ P : Type*} (wt : ι → ℝ) (hwt0 : ∀ ξ, 0 ≤ wt ξ) (hwt : Summable wt)
    (e : κ ≃ P) (kb : ι → P → ℝ) (hkb0 : ∀ ξ p, 0 ≤ kb ξ p) (hkbs : ∀ ξ, Summable (kb ξ)) (B : ℝ)
    (hB : ∀ ξ, ∑' p, kb ξ p ≤ B) (Tm : ι → κ → ℂ) (T0 : κ → ℂ)
    (hn : ∀ ξ κ', ‖Tm ξ κ'‖ ≤ kb ξ (e κ'))
    (hper : ∀ κ', HasSum (fun ξ => (wt ξ : ℂ) * Tm ξ κ') (T0 κ')) :
    HasSum (fun ξ => (wt ξ : ℂ) * ∑' κ', Tm ξ κ') (∑' κ', T0 κ') := by
  have hks : ∀ ξ, Summable (fun κ' => kb ξ (e κ')) := fun ξ => (e.summable_iff.2 (hkbs ξ))
  have hkt : ∀ ξ, ∑' κ', kb ξ (e κ') = ∑' p, kb ξ p := fun ξ => e.tsum_eq (kb ξ)
  let g : ι × κ → ℝ := fun q => wt q.1 * kb q.1 (e q.2)
  have hg0 : ∀ q, 0 ≤ g q := fun q => mul_nonneg (hwt0 _) (hkb0 _ _)
  have hg : Summable g := by
    have h1 : ∀ ξ, Summable fun κ' => g (ξ, κ') := fun ξ => (hks ξ).mul_left (wt ξ)
    refine (summable_prod_of_nonneg hg0).2 ⟨h1, ?_⟩
    refine Summable.of_nonneg_of_le (fun ξ => tsum_nonneg fun p => hg0 (ξ, p)) (fun ξ => ?_) (hwt.mul_right B)
    show ∑' κ', wt ξ * kb ξ (e κ') ≤ _
    rw [tsum_mul_left, hkt]
    exact mul_le_mul_of_nonneg_left (hB ξ) (hwt0 ξ)
  let f : ι → κ → ℂ := fun ξ κ' => (wt ξ : ℂ) * Tm ξ κ'
  have hfn : ∀ q : ι × κ, ‖f q.1 q.2‖ ≤ g q := fun q => by
    show ‖(wt q.1 : ℂ) * Tm q.1 q.2‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hwt0 _)]
    exact mul_le_mul_of_nonneg_left (hn _ _) (hwt0 _)
  have hsf : Summable (Function.uncurry f) := Summable.of_norm_bounded hg hfn
  have hA := hsf.hasSum
  have H1 := hA.prod_fiberwise (fun ξ => (hsf.prod_factor ξ).hasSum)
  have H2 : HasSum (fun κ' => T0 κ') (∑' q, Function.uncurry f q) := by
    have hA' := (Equiv.prodComm _ _).hasSum_iff.mpr hA
    exact hA'.prod_fiberwise (fun κ' => hper κ')
  rw [H2.tsum_eq]
  refine H1.congr_fun fun ξ => ?_
  symm
  show ∑' κ', f ξ κ' = _
  simp only [f]
  rw [tsum_mul_left]

end WaveTurbulence.Represents
