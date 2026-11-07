/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm10
public import WaveTurbulence.Foundations.Stage1.Represents.RepFub1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the value of the skeleton expression is the sum over assembled modes of the spliced kernels
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf
open scoped ENNReal

variable {w d : ℕ} {S : Garden w} (A : AsmCtx S d)

instance genDecoration_countable {w d : ℕ} (G : Garden w) (n : Fin w → Fin d → ℤ) (n' : Fin d → ℤ) :
    Countable (GenDecoration G d n n') := by
  unfold GenDecoration
  infer_instance

open scoped Classical in
theorem AsmCtx.value_eq :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
      ∑' κ : GenDecoration S d A.roots 0, (if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) *
        ∫ τ, (coreTimeDomainW A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.skel κ τ) τ else 0) =
      ∑' ξ : XiT A.fam, (S.zeta * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ) *
        splicedKernel S (A.D ξ) A.L A.γ A.η A.δ A.base A.roots := by
  have : ∀ s, Countable (A.fam.Λ s) := A.fam.cnt
  have h1 : ∀ κ : GenDecoration S d A.roots 0, (if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) *
        ∫ τ, (coreTimeDomainW A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.skel κ τ) τ else 0) =
      ∫ τ, ∑' ξ, A.gI ξ κ τ := by
    intro κ
    have e1 : ∫ τ, ∑' ξ, A.gI ξ κ τ = ∫ τ, (if A.selSk κ then ((epsDec S κ.1 : ℝ) : ℂ) else 0) *
        (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.skel κ τ) τ :=
      integral_congr_ae (Filter.Eventually.of_forall fun τ => A.tsum_gI κ τ)
    rw [e1, integral_const_mul, ← integral_core_eq_spliced S A.layer0 A.tt]
    split_ifs <;> simp
  simp_rw [h1]
  have hswap := (sum_integral_sum_swap (volume : Measure (GBranch S.tree → ℝ)) A.gI
    A.meas_gI A.sum_lintegral_ne_top).1
  rw [hswap]
  calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
        ∑' ξ : XiT A.fam, ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gI ξ κ τ
      = ∑' ξ : XiT A.fam, (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
          ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gI ξ κ τ := by rw [tsum_mul_left]
    _ = _ := by
      refine tsum_congr fun ξ => ?_
      have := A.tsum_int_gI ξ
      calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
            ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gI ξ κ τ
          = S.zeta * ((coupling d A.L A.γ A.δ : ℂ) ^ S.order *
            ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gI ξ κ τ) := by ring
        _ = _ := by rw [this]; ring

end WaveTurbulence.Represents
