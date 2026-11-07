/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH10
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm11
public import WaveTurbulence.Foundations.Stage1.Represents.RepFub1

/-!
# S2 REPRESENTS, VINE-D (11): the outer form is a superposition of spliced kernels with hinges

`value_eqH`: the outer form of a vine piece (`outerVal`, with the selection weight `[selSk]`, the slot kernels `A.Fn` and
the vine factors `A.Hk`) equals `Σ_{ξh} (ζ(G_sb) · constWH ξh) · K_{G_sb}(DH ξh)`: TARGET (redvine) → (redvine2), with
`K†` the product of the vine amplitudes (L1965-L1969).  Fubini is justified by `sum_lintegral_gIH_ne_top`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

namespace AsmCtxH
variable (A : AsmCtxH S d)

open scoped Classical in
theorem value_eqH :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
      ∑' κ : GenDecoration S d A.roots 0, (if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        ∫ τ, (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ =
      ∑' ξh : A.Xi, (S.zeta * A.constWH ξh) * splicedKernel S (A.DH ξh) A.L A.γ A.η A.δ A.base A.roots := by
  have h1 : ∀ κ : GenDecoration S d A.roots 0,
      (if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        ∫ τ, (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ =
      ∫ τ, ∑' ξh, A.gIH ξh κ τ := by
    intro κ
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ => ((A.hasSum_gIH κ τ).tsum_eq).symm)
  simp_rw [h1]
  have hswap := (sum_integral_sum_swap (volume : Measure (GBranch S.tree → ℝ)) A.gIH
    A.meas_gIH A.sum_lintegral_gIH_ne_top).1
  rw [hswap]
  calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
        ∑' ξh : A.Xi, ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gIH ξh κ τ
      = ∑' ξh : A.Xi, (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
          ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gIH ξh κ τ := by rw [tsum_mul_left]
    _ = _ := by
      refine tsum_congr fun ξh => ?_
      have := A.tsum_int_gIH ξh
      calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
            ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gIH ξh κ τ
          = S.zeta * ((coupling d A.L A.γ A.δ : ℂ) ^ S.order *
            ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gIH ξh κ τ) := by ring
        _ = _ := by rw [this]; ring

open scoped Classical in
/-- `value_eqH` in the form of the interface `outerVal` (selection weight `[selSk]`). -/
theorem outerVal_eq_tsum :
    outerVal S A.hS A.L A.γ A.δ A.base A.roots A.tt A.layer0 A.hinges
        (fun z => if A.selSk z then 1 else 0) A.Fn A.hclk A.hmom A.Hk =
      ∑' ξh : A.Xi, (S.zeta * A.constWH ξh) * splicedKernel S (A.DH ξh) A.L A.γ A.η A.δ A.base A.roots := by
  rw [← A.value_eqH]
  unfold outerVal
  congr 1
  refine tsum_congr fun κ => ?_
  by_cases hsel : A.selSk κ
  · simp only [hsel, ite_true, Complex.ofReal_one, mul_one]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    by_cases hτ : τ ∈ splicedTimeDomain S A.layer0 A.tt
    · simp only [Set.indicator_of_mem hτ, AsmCtx.skel, hk]
      ring
    · simp only [Set.indicator_of_notMem hτ]
  · simp only [hsel, ite_false, Complex.ofReal_zero, mul_zero, zero_mul]

end AsmCtxH
end WaveTurbulence.Represents
