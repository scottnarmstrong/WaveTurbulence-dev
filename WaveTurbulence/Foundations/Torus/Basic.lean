/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Fourier coefficients on the torus `𝕋_L^d = [0, L]^d`

TARGET (1.2) (`fourier`, L286) fixes the space Fourier transform
`û(k) = L^{-d/2} ∫_{𝕋_L^d} u(x) e^{-2πi k·x} dx` for `k ∈ ℤ_L^d = (L⁻¹ℤ)^d`. Lattice points are
`n : Fin d → ℤ` with `k = n / L`; the coefficient is the frozen `torusFourierCoeff L f n`
(`WaveTurbulence.Frozen.Defs.TorusFourierCoeff`, ruling D6).

This file bridges `torusFourierCoeff` to Mathlib's Fourier theory on `UnitAddTorus (Fin d)` by the
rescaling `x ↦ x / L`. The function `torusLift L f` on the unit torus is `y ↦ f (L • ỹ)`, where
`ỹ = torusRep y ∈ (0,1]^d` is the representative of `y`, and

* `setIntegral_Icc_eq_smul_integral_torusLift`: `∫_{[0,L]^d} F = L^d ∫_{𝕋^d} torusLift L F`;
* `torusFourierCoeff_eq_mFourierCoeff`: `f̂(n) = L^{d/2} · mFourierCoeff (torusLift L f) n`.

Both hold for every `f`. For `L`-periodic `f` (`IsTorusPeriodic`):
`torusLift L f (torusProj L x) = f x`, the lift is continuous when `f` is
(`continuous_torusLift`), integrals over `[0,L]^d` are translation invariant
(`setIntegral_Icc_comp_add`), and translation multiplies coefficients by a character
(`torusFourierCoeff_comp_add`).

The unit torus carries Mathlib's normalized Haar measure (total mass `1`), the measure used by
`UnitAddTorus.mFourierCoeff`; it is made the local `volume` instance here exactly as in
`Mathlib.Analysis.Fourier.AddCircleMulti`.
-/

public section

noncomputable section

open MeasureTheory Complex Set
open scoped Pointwise

namespace WaveTurbulence

attribute [local instance] instMeasureSpaceUnitAddCircle instIsAddHaarMeasureUnitAddCircleVolume
  instIsProbabilityMeasureUnitAddCircleVolume

variable {d : ℕ}

/-! ### Periodicity -/

section Periodic

variable {E F : Type*}

/-- `f : ℝ^d → E` is `L`-periodic in each coordinate: `f (x + L eⱼ) = f x` for every `j`. -/
@[expose] def IsTorusPeriodic (L : ℝ) (f : (Fin d → ℝ) → E) : Prop :=
  ∀ (j : Fin d) (x : Fin d → ℝ), f (x + Pi.single j L) = f x

namespace IsTorusPeriodic

variable {L : ℝ} {f : (Fin d → ℝ) → E}

theorem add_single_int_mul (hf : IsTorusPeriodic L f) (j : Fin d) (m : ℤ) (x : Fin d → ℝ) :
    f (x + Pi.single j ((m : ℝ) * L)) = f x := by
  have hper : Function.Periodic (fun r : ℝ => f (x + Pi.single j r)) L := by
    intro r
    simp only [Pi.single_add, ← add_assoc]
    exact hf j _
  simpa using hper.int_mul_eq m

/-- Periodicity under every shift in `L ℤ^d`. -/
theorem add_int_mul (hf : IsTorusPeriodic L f) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    f (x + fun j => (k j : ℝ) * L) = f x := by
  classical
  have key : ∀ s : Finset (Fin d), ∀ y,
      f (y + ∑ j ∈ s, Pi.single j ((k j : ℝ) * L)) = f y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [Finset.sum_insert ha, add_comm (Pi.single a _) _, ← add_assoc,
        hf.add_single_int_mul, ih]
  have hsum : (fun j => (k j : ℝ) * L) = ∑ j, Pi.single j ((k j : ℝ) * L) :=
    (Finset.univ_sum_single _).symm
  rw [hsum]
  exact key _ x

theorem comp (hf : IsTorusPeriodic L f) (g : E → F) : IsTorusPeriodic L (fun x => g (f x)) :=
  fun j x => by simp only [hf j x]

theorem mul [Mul E] {g : (Fin d → ℝ) → E} (hf : IsTorusPeriodic L f) (hg : IsTorusPeriodic L g) :
    IsTorusPeriodic L (fun x => f x * g x) :=
  fun j x => by simp only [hf j x, hg j x]

theorem const (c : E) : IsTorusPeriodic L (fun _ : Fin d → ℝ => c) := fun _ _ => rfl

end IsTorusPeriodic

end Periodic

/-! ### The characters `e^{2πi (n/L)·x}` -/

section Character

variable {L : ℝ}

/-- The character `x ↦ e^{2πi (n/L)·x}` of `𝕋_L^d` at the frequency `k = n / L`. -/
@[expose] def torusChar (L : ℝ) (n : Fin d → ℤ) (x : Fin d → ℝ) : ℂ :=
  exp ((2 * Real.pi * ∑ j, (n j : ℝ) / L * x j : ℝ) * I)

theorem torusChar_add_index (L : ℝ) (m n : Fin d → ℤ) (x : Fin d → ℝ) :
    torusChar L (m + n) x = torusChar L m x * torusChar L n x := by
  simp only [torusChar, ← Complex.exp_add, ← add_mul, ← ofReal_add]
  congr 3
  simp only [Pi.add_apply, Int.cast_add, add_div, add_mul, Finset.sum_add_distrib]
  ring

theorem torusChar_add (L : ℝ) (n : Fin d → ℤ) (x y : Fin d → ℝ) :
    torusChar L n (x + y) = torusChar L n x * torusChar L n y := by
  simp only [torusChar, ← Complex.exp_add, ← add_mul, ← ofReal_add]
  congr 3
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem torusChar_zero_index (L : ℝ) (x : Fin d → ℝ) : torusChar L 0 x = 1 := by
  simp [torusChar]

theorem torusChar_neg_index (L : ℝ) (n : Fin d → ℤ) (x : Fin d → ℝ) :
    torusChar L (-n) x = (starRingEnd ℂ) (torusChar L n x) := by
  simp only [torusChar, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I]
  congr 1
  push_cast
  simp only [Pi.neg_apply, Int.cast_neg, neg_div, neg_mul, Finset.sum_neg_distrib]
  ring

theorem torusChar_mul_torusChar_neg (L : ℝ) (n : Fin d → ℤ) (x : Fin d → ℝ) :
    torusChar L n x * torusChar L (-n) x = 1 := by
  rw [← torusChar_add_index, add_neg_cancel, torusChar_zero_index]

@[simp] theorem norm_torusChar (L : ℝ) (n : Fin d → ℤ) (x : Fin d → ℝ) :
    ‖torusChar L n x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

@[fun_prop] theorem continuous_torusChar (L : ℝ) (n : Fin d → ℤ) : Continuous (torusChar L n) := by
  unfold torusChar
  fun_prop

theorem isTorusPeriodic_torusChar (hL : L ≠ 0) (n : Fin d → ℤ) :
    IsTorusPeriodic L (torusChar L n) := by
  intro j x
  rw [torusChar_add]
  have : torusChar L n (Pi.single j L) = 1 := by
    have hs : ∑ k, (n k : ℝ) / L * (Pi.single j L : Fin d → ℝ) k = n j := by
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp only [Pi.single_eq_same]
      field_simp
    simp only [torusChar, hs]
    rw [← Complex.exp_int_mul_two_pi_mul_I (n j)]
    congr 1
    push_cast
    ring
  rw [this, mul_one]

/-- The coefficient integral written with the character `torusChar L (-n)`. -/
theorem torusFourierCoeff_eq_integral (L : ℝ) (f : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ) :
    torusFourierCoeff L f n = ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
      ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), f x * torusChar L (-n) x := by
  unfold torusFourierCoeff torusChar
  congr 2
  funext x
  congr 2
  push_cast
  simp only [Pi.neg_apply, Int.cast_neg, neg_div, neg_mul, Finset.sum_neg_distrib, mul_neg]

end Character

/-! ### The unit torus: representatives, projection and lift -/

section Lift

variable {E : Type*} {L : ℝ}

/-- The representative in `(0, 1]^d` of a point of the unit torus. -/
@[expose] def torusRep (y : UnitAddTorus (Fin d)) : Fin d → ℝ :=
  fun j => (AddCircle.equivIoc (1 : ℝ) 0 (y j) : ℝ)

/-- The projection `x ↦ x / L mod ℤ^d` from `ℝ^d` to the unit torus. -/
@[expose] def torusProj (L : ℝ) (x : Fin d → ℝ) : UnitAddTorus (Fin d) :=
  fun j => ((x j / L : ℝ) : UnitAddCircle)

/-- The function on the unit torus corresponding to `f` on `[0, L]^d`: `y ↦ f (L • torusRep y)`. -/
@[expose] def torusLift (L : ℝ) (f : (Fin d → ℝ) → E) : UnitAddTorus (Fin d) → E :=
  fun y => f (L • torusRep y)

theorem coe_torusRep (y : UnitAddTorus (Fin d)) (j : Fin d) :
    ((torusRep y j : ℝ) : UnitAddCircle) = y j :=
  AddCircle.coe_equivIoc

theorem torusRep_coe_of_mem {x : Fin d → ℝ} (hx : ∀ j, x j ∈ Ioc (0 : ℝ) 1) :
    torusRep (fun j => (x j : UnitAddCircle)) = x := by
  funext j
  exact AddCircle.equivIoc_coe_of_mem (by simpa using hx j)

theorem torusProj_smul_torusRep (hL : L ≠ 0) (y : UnitAddTorus (Fin d)) :
    torusProj L (L • torusRep y) = y := by
  funext j
  simp only [torusProj, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hL]
  exact coe_torusRep y j

theorem torusProj_add (L : ℝ) (x y : Fin d → ℝ) :
    torusProj L (x + y) = torusProj L x + torusProj L y := by
  funext j
  simp [torusProj, add_div]

theorem exists_torusRep_torusProj (hL : L ≠ 0) (x : Fin d → ℝ) :
    ∃ k : Fin d → ℤ, L • torusRep (torusProj L x) = x + fun j => (k j : ℝ) * L := by
  have h : ∀ j, ∃ k : ℤ, torusRep (torusProj L x) j = x j / L + k := by
    intro j
    have hc : ((torusRep (torusProj L x) j - x j / L : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, coe_torusRep, sub_eq_zero]
      rfl
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 hc
    exact ⟨k, by rw [zsmul_eq_mul, mul_one] at hk; linarith⟩
  choose k hk using h
  refine ⟨k, funext fun j => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hk, Pi.add_apply]
  field_simp

theorem torusLift_torusProj (hL : L ≠ 0) {f : (Fin d → ℝ) → E} (hf : IsTorusPeriodic L f)
    (x : Fin d → ℝ) : torusLift L f (torusProj L x) = f x := by
  obtain ⟨k, hk⟩ := exists_torusRep_torusProj hL x
  simp only [torusLift, hk, hf.add_int_mul]

theorem torusLift_comp_add (hL : L ≠ 0) {f : (Fin d → ℝ) → E} (hf : IsTorusPeriodic L f)
    (h : Fin d → ℝ) :
    torusLift L (fun x => f (x + h)) = fun y => torusLift L f (y + torusProj L h) := by
  funext y
  have hy : y + torusProj L h = torusProj L (L • torusRep y + h) := by
    rw [torusProj_add, torusProj_smul_torusRep hL]
  rw [hy, torusLift_torusProj hL hf]
  rfl

/-- The lift of a continuous periodic function is continuous. -/
theorem continuous_torusLift [TopologicalSpace E] (hL : L ≠ 0) {f : (Fin d → ℝ) → E}
    (hf : Continuous f) (hp : IsTorusPeriodic L f) : Continuous (torusLift L f) := by
  have hq : Topology.IsQuotientMap (Pi.map fun (_ : Fin d) => ((↑) : ℝ → UnitAddCircle)) :=
    (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap
  rw [hq.continuous_iff]
  have hcomp : torusLift L f ∘ Pi.map (fun _ => ((↑) : ℝ → UnitAddCircle)) =
      fun y => f (L • y) := by
    funext y
    have hy : Pi.map (fun _ => ((↑) : ℝ → UnitAddCircle)) y = torusProj L (L • y) := by
      funext j
      simp [torusProj, Pi.map, mul_div_cancel_left₀ _ hL]
    simp only [Function.comp_apply, hy, torusLift_torusProj hL hp]
  rw [hcomp]
  exact hf.comp (continuous_const_smul L)

theorem torusLift_torusChar (hL : L ≠ 0) (n : Fin d → ℤ) :
    torusLift L (torusChar L n) = UnitAddTorus.mFourier n := by
  funext y
  have hf : ∀ i, fourier (n i) (y i) = exp (2 * Real.pi * I * (n i) * (torusRep y i) / (1 : ℝ)) := by
    intro i
    conv_lhs => rw [← coe_torusRep y i]
    exact fourier_coe_apply
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hf, ← Complex.exp_sum, torusLift,
    torusChar]
  congr 1
  push_cast
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  have hL' : (L : ℂ) ≠ 0 := ofReal_ne_zero.2 hL
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  field_simp

end Lift

/-! ### Integrals over `[0, L]^d` as integrals over the unit torus -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ}

theorem smul_univ_pi_Ioc_one (hL : 0 < L) :
    L • (univ.pi fun _ : Fin d => Ioc (0 : ℝ) 1) = univ.pi fun _ => Ioc 0 L := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hL.ne']
  simp only [mem_univ_pi, Pi.smul_apply, smul_eq_mul, mem_Ioc]
  refine forall_congr' fun j => ?_
  rw [inv_mul_le_iff₀ hL, mul_one, mul_pos_iff_of_pos_left (inv_pos.2 hL)]

theorem univ_pi_Ioc_ae_eq_Icc (L : ℝ) :
    (univ.pi fun _ : Fin d => Ioc (0 : ℝ) L) =ᵐ[volume] Icc (0 : Fin d → ℝ) (fun _ => L) := by
  rw [volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

/-- `∫_{[0,L]^d} F = L^d ∫_{𝕋^d} torusLift L F` (no periodicity or integrability needed). -/
theorem setIntegral_Icc_eq_smul_integral_torusLift (hL : 0 < L) (F : (Fin d → ℝ) → E) :
    ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), F x = L ^ d • ∫ y, torusLift L F y := by
  rw [← setIntegral_congr_set (univ_pi_Ioc_ae_eq_Icc L)]
  have h2 := Measure.setIntegral_comp_smul_of_pos volume F
    (univ.pi fun _ : Fin d => Ioc (0 : ℝ) 1) hL
  rw [smul_univ_pi_Ioc_one hL, Module.finrank_fin_fun] at h2
  have h3 : ∫ y, torusLift L F y = ∫ y in univ.pi fun _ : Fin d => Ioc (0 : ℝ) 1, F (L • y) := by
    rw [UnitAddTorus.integral_preimage _ 0]
    have hs : {x : Fin d → ℝ | ∀ i, x i ∈ Ioc ((0 : Fin d → ℝ) i) ((0 : Fin d → ℝ) i + 1)} =
        univ.pi fun _ => Ioc (0 : ℝ) 1 := by
      ext x
      simp
    rw [hs]
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun x hx => ?_
    simp only [torusLift]
    rw [torusRep_coe_of_mem (by simpa using hx)]
  rw [h3, h2, smul_inv_smul₀ (pow_ne_zero _ hL.ne')]

/-- The bridge to Mathlib's Fourier coefficients on the unit torus:
`f̂(n) = L^{d/2} · mFourierCoeff (torusLift L f) n` (no periodicity or integrability needed). -/
theorem torusFourierCoeff_eq_mFourierCoeff (hL : 0 < L) (f : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ) :
    torusFourierCoeff L f n =
      ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ) * UnitAddTorus.mFourierCoeff (torusLift L f) n := by
  rw [torusFourierCoeff_eq_integral, setIntegral_Icc_eq_smul_integral_torusLift hL,
    UnitAddTorus.mFourierCoeff]
  have hlift : torusLift L (fun x => f x * torusChar L (-n) x) =
      fun y => UnitAddTorus.mFourier (-n) y • torusLift L f y := by
    funext y
    rw [smul_eq_mul, mul_comm, ← torusLift_torusChar hL.ne']
    rfl
  rw [hlift, Complex.real_smul, ← mul_assoc]
  congr 1
  have hne : (L ^ ((d : ℝ) / 2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  have h : (L ^ d : ℝ) = L ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_add hL, add_halves, Real.rpow_natCast]
  rw [h]
  push_cast
  field_simp

/-- Integrals of periodic functions over `[0, L]^d` are translation invariant. -/
theorem setIntegral_Icc_comp_add (hL : 0 < L) {F : (Fin d → ℝ) → E} (hF : IsTorusPeriodic L F)
    (h : Fin d → ℝ) :
    ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), F (x + h) =
      ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), F x := by
  rw [setIntegral_Icc_eq_smul_integral_torusLift hL, setIntegral_Icc_eq_smul_integral_torusLift hL,
    torusLift_comp_add hL.ne' hF, integral_add_right_eq_self]

/-- Translating a periodic function multiplies its coefficients by a character. -/
theorem torusFourierCoeff_comp_add (hL : 0 < L) {f : (Fin d → ℝ) → ℂ} (hf : IsTorusPeriodic L f)
    (h : Fin d → ℝ) (n : Fin d → ℤ) :
    torusFourierCoeff L (fun x => f (x + h)) n = torusChar L n h * torusFourierCoeff L f n := by
  rw [torusFourierCoeff_eq_integral, torusFourierCoeff_eq_integral]
  have hG : IsTorusPeriodic L (fun x => f x * torusChar L (-n) x) :=
    hf.mul (isTorusPeriodic_torusChar hL.ne' (-n))
  have hpt : ∀ x, f (x + h) * torusChar L (-n) x =
      torusChar L n h * (f (x + h) * torusChar L (-n) (x + h)) := by
    intro x
    rw [torusChar_add L (-n) x h]
    linear_combination (f (x + h) * torusChar L (-n) x) * (torusChar_mul_torusChar_neg L n h).symm
  simp_rw [hpt]
  rw [integral_const_mul, setIntegral_Icc_comp_add hL hG h]
  ring

end Integral

/-! ### Bounds -/

section Bounds

variable {L : ℝ}

/-- A continuous periodic function is bounded. -/
theorem IsTorusPeriodic.exists_bound {E : Type*} [SeminormedAddCommGroup E] (hL : L ≠ 0)
    {f : (Fin d → ℝ) → E} (hf : Continuous f) (hp : IsTorusPeriodic L f) :
    ∃ C, ∀ x, ‖f x‖ ≤ C := by
  let g : C(UnitAddTorus (Fin d), E) := ⟨torusLift L f, continuous_torusLift hL hf hp⟩
  exact ⟨‖g‖, fun x => by rw [← torusLift_torusProj hL hp x]; exact g.norm_coe_le_norm _⟩

theorem volume_real_Icc_torus (hL : 0 ≤ L) :
    volume.real (Icc (0 : Fin d → ℝ) (fun _ => L)) = L ^ d := by
  simp [Measure.real, Real.volume_Icc_pi, hL]

/-- `‖f̂(n)‖ ≤ L^{d/2} sup_{[0,L]^d} ‖f‖`. -/
theorem norm_torusFourierCoeff_le (hL : 0 < L) {f : (Fin d → ℝ) → ℂ} {C : ℝ}
    (hC : ∀ x ∈ Icc (0 : Fin d → ℝ) (fun _ => L), ‖f x‖ ≤ C) (n : Fin d → ℤ) :
    ‖torusFourierCoeff L f n‖ ≤ L ^ ((d : ℝ) / 2) * C := by
  have hpos : 0 < L ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hL _
  rw [torusFourierCoeff_eq_integral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hpos.le]
  have hint := norm_setIntegral_le_of_norm_le_const (measure_Icc_lt_top (μ := volume))
    (fun x hx => by rw [norm_mul, norm_torusChar, mul_one]; exact hC x hx)
    (f := fun x => f x * torusChar L (-n) x)
  rw [volume_real_Icc_torus hL.le] at hint
  have h : (L ^ d : ℝ) = L ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_add hL, add_halves, Real.rpow_natCast]
  calc (L ^ ((d : ℝ) / 2))⁻¹ * ‖∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), f x * torusChar L (-n) x‖
      ≤ (L ^ ((d : ℝ) / 2))⁻¹ * (C * L ^ d) := by gcongr
    _ = L ^ ((d : ℝ) / 2) * C := by rw [h]; field_simp

end Bounds

end WaveTurbulence
