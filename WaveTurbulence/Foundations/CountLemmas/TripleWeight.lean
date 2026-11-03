/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearBandWeight
public import WaveTurbulence.Foundations.CountLemmas.BroadBand
public import WaveTurbulence.Foundations.CountLemmas.DoubleBandCount
public import WaveTurbulence.Foundations.WeylSums.CubicChainPointwise

/-! # A plateau cutoff majorizing the source triple count -/

public section
open Set Finset
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

/-- Width four is fixed, with value one throughout the source unit balls. -/
@[expose] noncomputable def tripleBandWeight {d : ℕ} (L : ℝ) (a b c : Mom d)
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  latticeCutoff ((4 : ℝ)⁻¹ • (latticePoint L q.1-a))*
    latticeCutoff ((4 : ℝ)⁻¹ • (latticePoint L q.2.1-b))*
    latticeCutoff ((4 : ℝ)⁻¹ • (latticePoint L q.2.2-c))

theorem tripleBandWeight_nonneg {d : ℕ} (L : ℝ) (a b c : Mom d)
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
    0 ≤ tripleBandWeight L a b c q :=
  mul_nonneg (mul_nonneg (latticeCutoff_nonneg _) (latticeCutoff_nonneg _)) (latticeCutoff_nonneg _)

theorem tripleBandWeight_eq_one {d : ℕ} (L : ℝ) (a b c : Mom d)
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))
    (ha : ‖latticePoint L q.1-a‖ ≤ 1) (hb : ‖latticePoint L q.2.1-b‖ ≤ 1)
    (hc : ‖latticePoint L q.2.2-c‖ ≤ 1) : tripleBandWeight L a b c q = 1 := by
  rw [tripleBandWeight,latticeCutoff_quarter_eq_one _ (ha.trans (by norm_num)),
    latticeCutoff_quarter_eq_one _ (hb.trans (by norm_num)),
    latticeCutoff_quarter_eq_one _ (hc.trans (by norm_num))]
  norm_num

theorem finite_tripleBandWeight {d : ℕ} {L : ℝ} (hL : 0 < L) (a b c : Mom d) :
    (Function.support (tripleBandWeight L a b c)).Finite := by
  apply ((finite_latticeCutoff (mul_pos (by norm_num : (0 : ℝ) < 4) hL) ((4 : ℝ)⁻¹ • a)).prod
    ((finite_latticeCutoff (mul_pos (by norm_num : (0 : ℝ) < 4) hL) ((4 : ℝ)⁻¹ • b)).prod
      (finite_latticeCutoff (mul_pos (by norm_num : (0 : ℝ) < 4) hL) ((4 : ℝ)⁻¹ • c)))).subset
  intro q hq
  have heq (n : Fin d → ℤ) (v : Mom d) :
      (4 : ℝ)⁻¹ • (latticePoint L n-v) = latticePoint (4*L) n-(4 : ℝ)⁻¹ • v := by
    rw [latticePoint_four_mul,smul_sub]
  change latticeCutoff (latticePoint (4*L) q.1-(4 : ℝ)⁻¹ • a) ≠ 0 ∧
    latticeCutoff (latticePoint (4*L) q.2.1-(4 : ℝ)⁻¹ • b) ≠ 0 ∧
    latticeCutoff (latticePoint (4*L) q.2.2-(4 : ℝ)⁻¹ • c) ≠ 0
  simpa only [Function.mem_support,tripleBandWeight,heq,mul_ne_zero_iff,and_assoc] using hq

/-- Exact rescaling identifies the two-band star Fourier sum with the
proved cubic sum. The second linear frequency varies with the second time. -/
theorem tripleWeight_star_norm {d : ℕ} {L : ℝ} (hL : 0 < L)
    (a b c v : Mom d) (α β : ℝ) (ts : ℝ × ℝ) :
    ‖doubleEnergySum (finite_tripleBandWeight hL a b c).toFinset (tripleBandWeight L a b c)
      (fun q => inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α)
      (fun q => inner ℝ (latticePoint L q.1-v) (latticePoint L q.2.2)-β) ts‖ =
    ‖cubicLatticeSum (4*L) (16*ts.1) (16*ts.2) true
      ((4 : ℝ)⁻¹ • a) ((4 : ℝ)⁻¹ • b) ((4 : ℝ)⁻¹ • c)
      0 0 ((-4*ts.2) • v)‖ := by
  let w := tripleBandWeight L a b c
  let I := (finite_tripleBandWeight hL a b c).toFinset
  have heq : doubleEnergySum I w
      (fun q => inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α)
      (fun q => inner ℝ (latticePoint L q.1-v) (latticePoint L q.2.2)-β) ts =
      e (-ts.1*α-ts.2*β)*cubicLatticeSum (4*L) (16*ts.1) (16*ts.2) true
        ((4 : ℝ)⁻¹ • a) ((4 : ℝ)⁻¹ • b) ((4 : ℝ)⁻¹ • c) 0 0 ((-4*ts.2) • v) := by
    have hsum : doubleEnergySum I w
        (fun q => inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α)
        (fun q => inner ℝ (latticePoint L q.1-v) (latticePoint L q.2.2)-β) ts =
        ∑' q, (w q : ℂ)*e (ts.1*(inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α)+
          ts.2*(inner ℝ (latticePoint L q.1-v) (latticePoint L q.2.2)-β)) := by
      symm
      apply tsum_eq_sum
      intro q hq
      have hz : w q = 0 := by
        by_contra hz
        exact hq ((finite_tripleBandWeight hL a b c).mem_toFinset.mpr hz)
      simp only [hz,Complex.ofReal_zero,zero_mul]
    rw [hsum,cubicLatticeSum,← tsum_mul_left]
    apply tsum_congr
    intro q
    have hw : latticeCutoff (latticePoint (4*L) q.1-(4 : ℝ)⁻¹ • a)*
        latticeCutoff (latticePoint (4*L) q.2.1-(4 : ℝ)⁻¹ • b)*
        latticeCutoff (latticePoint (4*L) q.2.2-(4 : ℝ)⁻¹ • c) = w q := by
      dsimp only [w,tripleBandWeight]
      simp only [latticePoint_four_mul,smul_sub]
    rw [hw,mul_left_comm,mul_assoc,← e_add]
    congr 2
    simp only [cubicQuadraticForm,ite_true,latticePoint_four_mul,real_inner_smul_left,
      real_inner_smul_right,inner_zero_left,inner_sub_left]
    ring
  rw [heq,norm_mul,norm_e,one_mul]

end WaveTurbulence.CountLemmas
