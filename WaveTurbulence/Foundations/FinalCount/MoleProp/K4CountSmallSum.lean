/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountDyadic
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountSmallProfile
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountCutoff
import Mathlib.Tactic

/-! # Uniform actual small-sphere K4 bound after finite radius summation

All dyadic blocks are produced from source constraints. The integer
spacing supplies the least terminal scale, and the positive radius powers
sum geometrically. Constants depend only on d and gamma.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

noncomputable def k4SmallSumConstant (d : ℕ) (γ : ℝ) : ℝ :=
  60*k4BlockBoxConstant d*(3+2*(4 : ℝ)^(min γ (1-γ)/100)/(min γ (1-γ)/100))

/-- The actual profile sum is uniform in the number of radius blocks and
all source centers, with a stronger 1.04 gamma-zero saving. -/
theorem k4_small_profile_sum_le (d : ℕ) (hd : 3 ≤ d) {L R δ γ : ℝ}
    (hL : 1 ≤ L) (hR : 0 < R) (hcut : R ≤ k4CoefficientCut L γ)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ < 1) (J : ℕ)
    (hscales : ∀ j < J, 1 ≤ L*(R/(2 : ℝ)^j)) :
    (∑ j ∈ range J, k4BaseLocalProfile d L (δ⁻¹*L^(-2*γ)) (R/(2 : ℝ)^j)*
      k4SmallFiberProfile d L (δ⁻¹*L^(-2*γ)) ((R/(2 : ℝ)^j)/2) (L^(1-min γ (1-γ)/10))) ≤
      k4SmallSumConstant d γ*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(104 : ℝ)/100*min γ (1-γ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hD0 : 0 < δ⁻¹ := inv_pos.mpr hδ.1
  let g := min γ (1-γ)
  let ε := g/100
  let E := 3*((d : ℝ)-γ)-(21 : ℝ)/20*g
  let F := 3*((d : ℝ)-γ)-(104 : ℝ)/100*g
  let H := 3+2*(4 : ℝ)^ε/ε
  let K := 10*k4BlockBoxConstant d*H*(δ⁻¹)^3*L^F
  have hg : 0 < g := lt_min hγ (by linarith only [hγ1])
  have hε : 0 < ε := div_pos hg (by norm_num)
  have hK0 : 0 ≤ k4BlockBoxConstant d := by unfold k4BlockBoxConstant; positivity
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have he : E+ε=F := by dsimp only [E,ε,F]; ring
  have hR1 : R ≤ 1 := hcut.trans (k4_coefficient_cut_le_one hL)
  have hblock : ∀ j ∈ range J,
      k4BaseLocalProfile d L (δ⁻¹*L^(-2*γ)) (R/(2 : ℝ)^j)*
      k4SmallFiberProfile d L (δ⁻¹*L^(-2*γ)) ((R/(2 : ℝ)^j)/2) (L^(1-g/10)) ≤
      K*((R/(2 : ℝ)^j)^(d-2)+2*(R/(2 : ℝ)^j)^(d-1)) := by
    intro j hj
    let r := R/(2 : ℝ)^j
    have hr : 0 < r := div_pos hR (pow_pos (by norm_num : (0 : ℝ)<2) j)
    have hpow : 1 ≤ (2 : ℝ)^j := by
      simpa only [pow_zero] using pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (Nat.zero_le j)
    have hrR : r ≤ R := div_le_self hR.le hpow
    have hr1 : r ≤ 1 := hrR.trans hR1
    have hrcut : r ≤ k4CoefficientCut L γ := hrR.trans hcut
    have hH1 : 1 ≤ 3+2*Real.log (⌈2*(L*r)+1⌉₊ : ℝ) := k4_harmonic_factor_one_le hLp.le hr.le
    have hP := k4_small_block_power_le d hd hL hr (hscales j (mem_range.mp hj)) hδ hγ hγ1
    have hC := k4_cutoff_three_term_le d (by omega : 1 ≤ d) hL hr.le hrcut
    have hLog := k4_harmonic_factor_le_rpow hL hr.le hr1 hε
    have hHi0 : 0 ≤ 3+2*Real.log (⌈2*(L*r)+1⌉₊ : ℝ) := zero_le_one.trans hH1
    have hc0 : 0 ≤ 10*k4BlockBoxConstant d*(3+2*Real.log (⌈2*(L*r)+1⌉₊ : ℝ))*(δ⁻¹)^3 := by positivity
    have hrad0 : 0 ≤ r^(d-2)+2*r^(d-1) := by positivity
    calc
      _ ≤ (10*k4BlockBoxConstant d)*(3+2*Real.log (⌈2*(L*r)+1⌉₊ : ℝ))*(δ⁻¹)^3*
          (L^E*(r^(d-2)+2*r^(d-1))) :=
        hP.trans (mul_le_mul_of_nonneg_left hC hc0)
      _ = (10*k4BlockBoxConstant d*(δ⁻¹)^3*L^E*(r^(d-2)+2*r^(d-1)))*
          (3+2*Real.log (⌈2*(L*r)+1⌉₊ : ℝ)) := by ring
      _ ≤ (10*k4BlockBoxConstant d*(δ⁻¹)^3*L^E*(r^(d-2)+2*r^(d-1)))*(H*L^ε) :=
        mul_le_mul_of_nonneg_left hLog (by positivity)
      _ = (10*k4BlockBoxConstant d*H*(δ⁻¹)^3)*(L^E*L^ε)*(r^(d-2)+2*r^(d-1)) := by ring
      _ = _ := by rw [← Real.rpow_add hLp,he]
  have hsum : (∑ j ∈ range J, k4BaseLocalProfile d L (δ⁻¹*L^(-2*γ)) (R/(2 : ℝ)^j)*
      k4SmallFiberProfile d L (δ⁻¹*L^(-2*γ)) ((R/(2 : ℝ)^j)/2) (L^(1-g/10))) ≤
      K*(∑ j ∈ range J, ((R/(2 : ℝ)^j)^(d-2)+2*(R/(2 : ℝ)^j)^(d-1))) := by
    rw [mul_sum]
    exact sum_le_sum hblock
  have hp := CountLemmas.sum_dyadic_radius_pow_le hR.le (d-2) J (by omega)
  have hq := CountLemmas.sum_dyadic_radius_pow_le hR.le (d-1) J (by omega)
  have hRp : R^(d-2) ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hR.le hR1 (d-2)
  have hRq : R^(d-1) ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hR.le hR1 (d-1)
  have hgeom : (∑ j ∈ range J, ((R/(2 : ℝ)^j)^(d-2)+2*(R/(2 : ℝ)^j)^(d-1))) ≤ 6 := by
    rw [sum_add_distrib,← mul_sum]
    linarith only [hp,hq,hRp,hRq]
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_left hgeom hK).trans_eq
  dsimp only [K,H,F,ε,g,k4SmallSumConstant]
  ring

/-- Actual canonical source points below the coefficient cutoff obey a
uniform small-sphere bound. No shell-count premise survives this export. -/
theorem k4_small_nonexception_source_le (d : ℕ) (hd : 3 ≤ d)
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    {L δ γ : ℝ} (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ)
    (hS : ∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β (δ⁻¹*L^(-2*γ)))
    (hneq : ∀ p ∈ S, p.2.1 ≠ a) (hcoeff : ∀ p ∈ S, p.2.1 ≠ -c)
    (hr : ∀ p ∈ S, ‖latticePoint L c+latticePoint L p.2.1‖ ≤ k4CoefficientCut L γ)
    (hsmall : ∀ p ∈ S, ‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖ ≤ L^(1-min γ (1-γ)/10)) :
    (S.card : ℝ) ≤ k4SmallSumConstant d γ*(δ⁻¹)^3*
      L^(3*((d : ℝ)-γ)-(104 : ℝ)/100*min γ (1-γ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hLp.le _)
  obtain ⟨J,hscales,hcount⟩ := k4_small_sphere_dyadic_le (by omega : 2 ≤ d) S hLp
    (k4_coefficient_cut_pos hLp) (Real.rpow_nonneg hLp.le _) hτ A a b c β hS hneq hcoeff hr hsmall
  exact hcount.trans (k4_small_profile_sum_le d hd hL (k4_coefficient_cut_pos hLp) le_rfl hδ hγ hγ1 J hscales)

end WaveTurbulence.MoleProp
