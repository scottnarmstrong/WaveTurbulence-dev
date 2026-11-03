/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.WeylDifferencing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Quantitative A-process under fractional shift bounds

The exact proved Weyl–van der Corput inequality is reduced to its usable
cutoff form. Shift estimates remain explicit local hypotheses of these
conditional numerical helpers; the shared exponent-pair predicate belongs
to NT-BPROC and is not redefined here.
-/

public section

namespace WaveTurbulence.NumberTheory

open Finset

/-- The A-process with a local `A*abs(h)^kappa` bound on its actual differenced
sums. Both signs of the shift and all finite-window overlaps are included. -/
theorem weyl_vdC_sq_le_of_shift_rpow_bound (f : ℤ → ℝ) (a : ℤ) (N H : ℕ)
    {A kappa : ℝ} (hA : 0 ≤ A) (hk : 0 ≤ kappa)
    (hshift : ∀ h : ℤ, h ≠ 0 → |h| ≤ (H:ℤ) →
      ‖∑ n ∈ (Ioc a (a+N)).filter (fun n => n+h ∈ Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤ A*|(h:ℝ)|^kappa) :
    ‖∑ n ∈ Ioc a (a+N), expPhase (f n)‖^2 ≤
      ((N+H:ℝ)/(H+1))*((N:ℝ)+2*H*A*(H:ℝ)^kappa) := by
  classical
  let G : ℤ → ℂ := fun h => ∑ n ∈ (Ioc a (a+N)).filter (fun n => n+h ∈ Ioc a (a+N)),
    expPhase (f (n+h)-f n)
  let S := Icc (-(H:ℤ)) H
  have hcard : (Ioc a (a+N)).card = N := by rw [Int.card_Ioc]; omega
  have hfilter : (Ioc a (a+N)).filter (fun n : ℤ => n+0 ∈ Ioc a (a+N)) = Ioc a (a+N) := by
    ext n
    simp only [Finset.mem_filter,add_zero,and_self]
  have hzero : ‖G 0‖ = (N:ℝ) := by
    dsimp only [G]
    rw [hfilter]
    simp only [add_zero,sub_self,expPhase_zero,Finset.sum_const,nsmul_eq_mul,mul_one,
      Complex.norm_natCast,hcard]
  have hmem0 : (0:ℤ) ∈ S := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hcardS : S.card = 2*H+1 := by dsimp only [S]; rw [Int.card_Icc]; omega
  have hcardErase : (S.erase 0).card = 2*H := by
    rw [Finset.card_erase_of_mem hmem0,hcardS]
    omega
  have hpoint (h : ℤ) (hh : h ∈ S.erase 0) : ‖G h‖ ≤ A*(H:ℝ)^kappa := by
    have hm := Finset.mem_erase.mp hh
    have habs : |h| ≤ (H:ℤ) := abs_le.mpr (Finset.mem_Icc.mp hm.2)
    have habsR : |(h:ℝ)| ≤ (H:ℝ) := by rw [← Int.cast_abs]; exact_mod_cast habs
    exact (hshift h hm.1 habs).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) habsR hk) hA)
  have hsum : (∑ h ∈ S, ‖G h‖) ≤ (N:ℝ)+2*H*A*(H:ℝ)^kappa := by
    rw [← Finset.sum_erase_add S (fun h => ‖G h‖) hmem0,hzero]
    calc
      _ ≤ (∑ _h ∈ S.erase 0, A*(H:ℝ)^kappa)+(N:ℝ) :=
        add_le_add (Finset.sum_le_sum hpoint) le_rfl
      _ = _ := by rw [Finset.sum_const,hcardErase,nsmul_eq_mul]; push_cast; ring
  exact (weyl_vdC_expSum f a N H).trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- Standard cutoff form of the A-process when `1 ≤ H ≤ N`. This version
keeps the two competing terms separate for exponent-pair optimization. -/
theorem weyl_vdC_sq_le_cutoff (f : ℤ → ℝ) (a : ℤ) {N H : ℕ}
    (hH : 0 < H) (hHN : H ≤ N) {A kappa : ℝ} (hA : 0 ≤ A) (hk : 0 ≤ kappa)
    (hshift : ∀ h : ℤ, h ≠ 0 → |h| ≤ (H:ℤ) →
      ‖∑ n ∈ (Ioc a (a+N)).filter (fun n => n+h ∈ Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤ A*|(h:ℝ)|^kappa) :
    ‖∑ n ∈ Ioc a (a+N), expPhase (f n)‖^2 ≤
      2*(N:ℝ)^2/H+4*(N:ℝ)*A*(H:ℝ)^kappa := by
  have hHR : 0 < (H:ℝ) := by exact_mod_cast hH
  have hHNR : (H:ℝ) ≤ N := by exact_mod_cast hHN
  have hfront : (N+H:ℝ)/(H+1) ≤ (2*(N:ℝ))/H := by
    calc
      _ ≤ (2*(N:ℝ))/(H+1) := div_le_div_of_nonneg_right
        (by linarith only [hHNR]) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hHR (by linarith)
  have hc := weyl_vdC_sq_le_of_shift_rpow_bound f a N H hA hk hshift
  calc
    _ ≤ ((N+H:ℝ)/(H+1))*((N:ℝ)+2*H*A*(H:ℝ)^kappa) := hc
    _ ≤ ((2*(N:ℝ))/H)*((N:ℝ)+2*H*A*(H:ℝ)^kappa) :=
      mul_le_mul_of_nonneg_right hfront (by positivity)
    _ = _ := by field_simp; ring

/-- Choose the actual integer cutoff as `floor X`. The resulting A-process
bound loses only a fixed factor and remains valid for every `1 ≤ X ≤ N`. -/
theorem weyl_vdC_sq_le_real_cutoff (f : ℤ → ℝ) (a : ℤ) (N : ℕ)
    {A kappa X : ℝ} (hA : 0 ≤ A) (hk : 0 ≤ kappa) (hX1 : 1 ≤ X) (hXN : X ≤ (N:ℝ))
    (hshift : ∀ h : ℤ, h ≠ 0 → |h| ≤ (N:ℤ) →
      ‖∑ n ∈ (Ioc a (a+N)).filter (fun n => n+h ∈ Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤ A*|(h:ℝ)|^kappa) :
    ‖∑ n ∈ Ioc a (a+N), expPhase (f n)‖^2 ≤
      4*(N:ℝ)^2/X+4*(N:ℝ)*A*X^kappa := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  let H : ℕ := ⌊X⌋₊
  have hH : 0 < H := Nat.floor_pos.mpr hX1
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hHX : (H:ℝ) ≤ X := Nat.floor_le hXp.le
  have hXH : X/2 ≤ (H:ℝ) := by
    have hh := Nat.lt_floor_add_one X
    change X < (H:ℝ)+1 at hh
    linarith only [hh,hHR]
  have hHN : H ≤ N := by exact_mod_cast hHX.trans hXN
  have hb := weyl_vdC_sq_le_cutoff f a hH hHN hA hk
    (fun h hn hh => hshift h hn (hh.trans (by exact_mod_cast hHN)))
  have hhead : 2*(N:ℝ)^2/H ≤ 4*(N:ℝ)^2/X := by
    calc
      _ ≤ (2*(N:ℝ)^2)/(X/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hXH
      _ = _ := by ring
  have htail : 4*(N:ℝ)*A*(H:ℝ)^kappa ≤ 4*(N:ℝ)*A*X^kappa :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg H) hHX hk) (by positivity)
  exact hb.trans (add_le_add hhead htail)

/-- Balanced A-process estimate. The displayed scalar balance condition is
an optimization parameter for this distinct helper; all differenced sums are
the actual finite overlaps in the proved Weyl inequality. -/
theorem weyl_vdC_norm_le_balanced (f : ℤ → ℝ) (a : ℤ) (N : ℕ)
    {A kappa X : ℝ} (hA : 0 ≤ A) (hk : 0 ≤ kappa) (hX1 : 1 ≤ X) (hXN : X ≤ (N:ℝ))
    (hbalance : A*X^(kappa+1) ≤ (N:ℝ))
    (hshift : ∀ h : ℤ, h ≠ 0 → |h| ≤ (N:ℤ) →
      ‖∑ n ∈ (Ioc a (a+N)).filter (fun n => n+h ∈ Ioc a (a+N)),
        expPhase (f (n+h)-f n)‖ ≤ A*|(h:ℝ)|^kappa) :
    ‖∑ n ∈ Ioc a (a+N), expPhase (f n)‖ ≤ 3*(N:ℝ)/Real.sqrt X := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hbal : A*X^kappa ≤ (N:ℝ)/X := by
    apply (le_div_iff₀ hXp).mpr
    have he : (A*X^kappa)*X = A*X^(kappa+1) := by
      rw [Real.rpow_add hXp,Real.rpow_one]
      ring
    rw [he]
    exact hbalance
  have hb := weyl_vdC_sq_le_real_cutoff f a N hA hk hX1 hXN hshift
  have hterm := mul_le_mul_of_nonneg_left hbal (by positivity : 0 ≤ 4*(N:ℝ))
  have hs : ‖∑ n ∈ Ioc a (a+N), expPhase (f n)‖^2 ≤ 8*(N:ℝ)^2/X := by
    calc
      _ ≤ 4*(N:ℝ)^2/X+4*(N:ℝ)*(A*X^kappa) := by simpa only [mul_assoc] using hb
      _ ≤ 4*(N:ℝ)^2/X+4*(N:ℝ)*((N:ℝ)/X) := add_le_add le_rfl hterm
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3*(N:ℝ)/Real.sqrt X)).mp
  have he : (3*(N:ℝ)/Real.sqrt X)^2 = 9*(N:ℝ)^2/X := by
    rw [div_pow,mul_pow,Real.sq_sqrt hXp.le]
    norm_num
  rw [he]
  exact hs.trans (div_le_div_of_nonneg_right
    (by nlinarith only [sq_nonneg (N:ℝ)]) hXp.le)

end WaveTurbulence.NumberTheory
