/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm7
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the decoration sum of the assembled mode is the spliced kernel
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ} {S : Garden w} (A : AsmCtx S d)

open scoped Classical in
theorem AsmCtx.tsum_int_gI (ξ : XiT A.fam) :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order * ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gI ξ κ τ =
      constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ *
        splicedKernel S (A.D ξ) A.L A.γ A.η A.δ A.base A.roots := by
  have key : ∀ κ : GenDecoration S d A.roots 0, ∫ τ, A.gI ξ κ τ =
      constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ *
        ((splicedEpsilon S (A.D ξ).hinges κ.1 : ℂ) * (splicedGapIndicator S (A.D ξ) A.L A.γ A.η A.base κ.1 : ℂ) *
          (∏ x ∈ S.molecule.bonds, (A.D ξ).edgeAmplitude x (A.base + latticePoint A.L (bondIndex S κ.1 x))) *
          (A.D ξ).hingeAmplitude (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) *
          splicedTimeIntegral S (A.D ξ) A.L A.γ A.δ A.base κ.1) := by
    intro κ
    unfold AsmCtx.gI
    rw [integral_const_mul]
    have hgap := A.hgs (A.D ξ) rfl κ
    have heps : splicedEpsilon S (A.D ξ).hinges κ.1 = epsDec S κ.1 := splicedEpsilon_empty S κ.1
    rw [hgap, heps]
    have hI : ∫ a, (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * timeFac A.fam A.hS ξ τ) a =
        splicedTimeIntegral S (A.D ξ) A.L A.γ A.δ A.base κ.1 := rfl
    have hE : A.E ξ κ = ∏ x ∈ S.molecule.bonds, (A.D ξ).edgeAmplitude x
        (A.base + latticePoint A.L (bondIndex S κ.1 x)) := rfl
    have hh : (A.D ξ).hingeAmplitude (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) = 1 := rfl
    rw [hI, hE, hh]
    by_cases hsel : A.selSk κ
    · simp only [hsel, ite_true, Complex.ofReal_one]
      ring
    · simp only [hsel, ite_false, Complex.ofReal_zero]
      simp
  unfold splicedKernel
  simp_rw [key]
  rw [tsum_mul_left]
  ring

end WaveTurbulence.Represents
