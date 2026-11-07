/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH8
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm9
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm10

/-!
# S2 REPRESENTS, VINE-D (9): one assembled mode is a spliced kernel; absolute bounds

* `tsum_int_gIH`: summed over the decorations and integrated over the times, the summand of one assembled mode `ξh` is
  `constWH ξh · K_{G_sb}(DH ξh)` (the literal `splicedKernel` with hinges, hinge amplitude and frequencies).
* `norm_gIH_le`, `lintegral_gIH_le`, `sum_lintegral_gIH_ne_top`: the absolute mass of the expansion is finite (Fubini).
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

instance countable_Xi : Countable A.Xi := by
  have : ∀ s, Countable (A.fam.Λ s) := A.fam.cnt
  have : ∀ j c, Countable (A.H.Λ j c) := A.H.cnt
  unfold Xi XiH XiT
  infer_instance

open scoped Classical in
theorem tsum_int_gIH (ξh : A.Xi) :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order * ∑' κ : GenDecoration S d A.roots 0, ∫ τ, A.gIH ξh κ τ =
      A.constWH ξh * splicedKernel S (A.DH ξh) A.L A.γ A.η A.δ A.base A.roots := by
  have key : ∀ κ : GenDecoration S d A.roots 0, ∫ τ, A.gIH ξh κ τ =
      A.constWH ξh *
        ((splicedEpsilon S (A.DH ξh).hinges κ.1 : ℂ) *
          (splicedGapIndicator S (A.DH ξh) A.L A.γ A.η A.base κ.1 : ℂ) *
          (∏ x ∈ S.molecule.bonds, (A.DH ξh).edgeAmplitude x (A.base + latticePoint A.L (bondIndex S κ.1 x))) *
          (A.DH ξh).hingeAmplitude (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) *
          splicedTimeIntegral S (A.DH ξh) A.L A.γ A.δ A.base κ.1) := by
    intro κ
    unfold gIH
    rw [integral_const_mul]
    have hgap := A.hgs (A.DH ξh) rfl κ
    rw [hgap]
    have hI : ∫ a, (splicedTimeDomain S A.layer0 A.tt).indicator (fun τ =>
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * A.timeFacH ξh τ) a =
        splicedTimeIntegral S (A.DH ξh) A.L A.γ A.δ A.base κ.1 := rfl
    have hE : A.E ξh.1 κ = ∏ x ∈ S.molecule.bonds, (A.DH ξh).edgeAmplitude x
        (A.base + latticePoint A.L (bondIndex S κ.1 x)) := rfl
    have hh : (A.DH ξh).hingeAmplitude (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) =
        A.hingeAmp ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1)) := rfl
    have hhin : (A.DH ξh).hinges = A.hinges := rfl
    rw [hI, hE, hh, hhin]
    by_cases hsel : A.selSk κ
    · simp only [hsel, ite_true, Complex.ofReal_one]
      ring
    · simp only [hsel, ite_false, Complex.ofReal_zero]
      simp
  unfold splicedKernel
  simp_rw [key]
  rw [tsum_mul_left]
  ring

theorem continuous_timeFacH (ξh : A.Xi) : Continuous (fun τ : GBranch S.tree → ℝ => A.timeFacH ξh τ) := by
  unfold timeFacH
  refine continuous_finsetProd _ fun b _ => ?_
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_apply b))).mul continuous_const)

theorem meas_gIH (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) :
    AEStronglyMeasurable (A.gIH ξh κ) volume := by
  classical
  unfold gIH
  refine aestronglyMeasurable_const.mul ?_
  refine (Continuous.aestronglyMeasurable ?_).indicator (measurableSet_splicedTimeDomain S A.layer0 A.tt)
  exact (continuous_phaseProd _ _ _ _).mul (A.continuous_timeFacH ξh)

theorem norm_splicedEpsilon_le (G : Garden w) (hinges : Finset (GBranch G.tree)) (z : GNode G.tree → Fin d → ℤ) :
    |splicedEpsilon G hinges z| ≤ 1 := by
  unfold splicedEpsilon
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun v _ => ?_
  unfold epsCoef
  split_ifs <;> simp

theorem norm_hingeAmp_le (ξh : A.Xi) (K : HingeDarts S A.hinges → Mom d) : ‖A.hingeAmp ξh K‖ ≤ 1 := by
  classical
  unfold hingeAmp
  rw [norm_mul, norm_prod]
  have h1 : ∏ j, ‖A.H.a j _ (ξh.2 j) (A.hmomOf j K)‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => A.H.a_one j _ _ _
  have h2 : ‖(if ∀ x : HingeDarts S A.hinges, ‖K x - cenS A.fam ξh.1 (slotOfDart A.hS x.1)‖ ≤ 1
      then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> simp
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_rootHPhase (ξh : A.Xi) : ‖A.rootHPhase ξh‖ = 1 := by
  unfold rootHPhase
  rw [norm_prod]
  exact Finset.prod_eq_one fun _ _ => Complex.norm_exp_ofReal_mul_I _

theorem norm_timeFacH (ξh : A.Xi) (τ : GBranch S.tree → ℝ) : ‖A.timeFacH ξh τ‖ = 1 := by
  unfold timeFacH
  rw [norm_prod]
  exact Finset.prod_eq_one fun _ _ => Complex.norm_exp_ofReal_mul_I _

theorem norm_constWH (ξh : A.Xi) :
    ‖A.constWH ξh‖ = ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξh.1‖ * ∏ j, A.H.w j _ (ξh.2 j) := by
  unfold constWH
  rw [norm_mul, norm_mul, A.norm_rootHPhase, mul_one, norm_prod]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [Complex.norm_real, Real.norm_of_nonneg (A.H.w_nn j _ _)]

theorem norm_gIH_le (ξh : A.Xi) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ) :
    ‖A.gIH ξh κ τ‖ ≤ (splicedTimeDomain S A.layer0 A.tt).indicator
      (fun _ => ‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖) τ := by
  classical
  unfold gIH
  by_cases hτ : τ ∈ splicedTimeDomain S A.layer0 A.tt
  · simp only [Set.indicator_of_mem hτ]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_phaseProd_le, one_mul, A.norm_timeFacH, mul_one]
    have h1 : ‖(if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0)‖ ≤ 1 := by
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs]; exact norm_splicedEpsilon_le S A.hinges κ.1
      · simp
    have h2 := A.norm_hingeAmp_le ξh (fun x => A.base + latticePoint A.L (bondIndex S κ.1 x.1))
    calc _ ≤ 1 * (‖A.constWH ξh‖ * ‖A.E ξh.1 κ‖ * 1) := by gcongr
      _ = _ := by ring
  · simp [Set.indicator_of_notMem hτ]

end AsmCtxH
end WaveTurbulence.Represents
