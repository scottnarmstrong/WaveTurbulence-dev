/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountBlocks
public import WaveTurbulence.Foundations.CountLemmas.DyadicPacking
import Mathlib.Tactic

/-! # Actual finite dyadic aggregation of canonical K4 source blocks

The terminal coefficient block is empty by the spacing of the original
integer lattice. Every nonterminal block consumes the actual proved base
and physical fiber estimates. The number of blocks is not a theorem premise.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- Every nonzero actual strip coefficient has at least one lattice spacing. -/
theorem k4_strip_coefficient_spacing {d : ℕ} {L : ℝ} (hL : 0 < L)
    (c y : Fin d → ℤ) (hy : y ≠ -c) :
    L⁻¹ ≤ ‖latticePoint L c+latticePoint L y‖ := by
  have hn : y+c ≠ 0 := by
    intro he
    apply hy
    funext i
    have hh := congrFun he i
    change y i+c i=0 at hh
    change y i= -(c i)
    omega
  obtain ⟨i,hi⟩ := CountLemmas.exists_lattice_coordinate_gap hL (y+c) hn
  have hc : |(latticePoint L (y+c)) i| ≤ ‖latticePoint L (y+c)‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L (y+c)) i
  have hh := hi.trans hc
  rw [WeylSums.latticePoint_add_eq,add_comm] at hh
  exact hh

/-- Source-constrained small-sphere points admit a finite sum of their
proved actual coefficient blocks; zero coefficients are excluded here
and counted separately by the fixed-middle exception theorem. -/
theorem k4_small_sphere_dyadic_le {d : ℕ} (hd : 2 ≤ d)
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    {L R M τ : ℝ} (hL : 0 < L) (hR : 0 < R) (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ)
    (hS : ∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β τ)
    (hneq : ∀ p ∈ S, p.2.1 ≠ a) (hcoeff : ∀ p ∈ S, p.2.1 ≠ -c)
    (hr : ∀ p ∈ S, ‖latticePoint L c+latticePoint L p.2.1‖ ≤ R)
    (hsmall : ∀ p ∈ S, ‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖ ≤ M) :
    ∃ J : ℕ, (∀ j < J, 1 ≤ L*(R/(2 : ℝ)^j)) ∧ (S.card : ℝ) ≤ ∑ j ∈ range J,
      k4BaseLocalProfile d L τ (R/(2 : ℝ)^j)*
        k4SmallFiberProfile d L τ ((R/(2 : ℝ)^j)/2) M := by
  classical
  have hex : ∃ J : ℕ, R/(2 : ℝ)^J < L⁻¹ := by
    obtain ⟨J,hJ⟩ := exists_pow_lt_of_lt_one (div_pos (inv_pos.mpr hL) hR)
      (by norm_num : (1/2 : ℝ)<1)
    refine ⟨J,?_⟩
    have hh := (lt_div_iff₀ hR).mp hJ
    simpa only [one_div,inv_pow,div_eq_mul_inv,one_mul,mul_comm] using hh
  let J := Nat.find hex
  have hterminal : R/(2 : ℝ)^J < L⁻¹ := Nat.find_spec hex
  have hscales : ∀ j < J, 1 ≤ L*(R/(2 : ℝ)^j) := by
    intro j hj
    have hn := Nat.find_min hex hj
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hL.le
    rw [mul_inv_cancel₀ hL.ne'] at hm
    exact hm
  let height := fun p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
    ‖latticePoint L c+latticePoint L p.2.1‖
  have hempty : S.filter (fun p => height p ≤ R/(2 : ℝ)^J) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hs := (mem_filter.mp hp).1
    have hlo := k4_strip_coefficient_spacing hL c p.2.1 (hcoeff p hs)
    exact (not_le_of_gt hterminal) (hlo.trans (mem_filter.mp hp).2)
  have he := Counting.sum_eq_low_add_dyadic_blocks S height (fun _ => (1 : ℝ)) hR.le hr J
  simp only [sum_const,nsmul_eq_mul,mul_one,hempty,card_empty,Nat.cast_zero,zero_add] at he
  refine ⟨J,hscales,he.trans_le ?_⟩
  apply sum_le_sum
  intro j _hj
  let r := R/(2 : ℝ)^j
  let T := S.filter (fun p => R/(2 : ℝ)^(j+1) < height p ∧ height p ≤ r)
  have hrp : 0 < r := div_pos hR (pow_pos (by norm_num : (0 : ℝ)<2) j)
  have hsplit : r/2=R/(2 : ℝ)^(j+1) := by dsimp only [r]; rw [pow_succ,div_mul_eq_div_div]
  apply k4_small_sphere_block_le hd T hL hrp hM hτ A a b c β
    (fun p hp => hS p (mem_filter.mp hp).1) (fun p hp => hneq p (mem_filter.mp hp).1)
  · intro p hp
    have hh := (mem_filter.mp hp).2
    exact ⟨by rw [hsplit]; exact hh.1.le,hh.2⟩
  · intro p hp
    exact hsmall p (mem_filter.mp hp).1

end WaveTurbulence.MoleProp
