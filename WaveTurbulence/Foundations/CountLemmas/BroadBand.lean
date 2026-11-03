/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearBandCount
public import WaveTurbulence.Foundations.CountLemmas.LatticeSets

/-! # Bilinear band counting with a fixed enlarged spatial radius -/

public section
open Set Finset
namespace WaveTurbulence.CountLemmas

/-- Exact lattice rescaling; the integer label is unchanged. -/
theorem latticePoint_four_mul {d : ℕ} (L : ℝ) (n : Fin d → ℤ) :
    latticePoint (4*L) n = (4 : ℝ)⁻¹ • latticePoint L n := by
  ext i
  simp only [latticePoint,PiLp.smul_apply,smul_eq_mul]
  ring

/-- A radius-four version of the proved bilinear band count. This finite
family form is convenient for projections of coupled counting problems. -/
theorem exists_broad_bilinear_band_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ : ℝ, 2 ≤ L → 0 < τ → 1/τ ≤ L^2 →
    ∀ a b : Mom d, ∀ β : ℝ, ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖latticePoint L q.1-a‖ ≤ 4 ∧ ‖latticePoint L q.2-b‖ ≤ 4 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-β| ≤ τ) →
      (s.card : ℝ) ≤ C*τ*L^(2*(d : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := WeylSums.exists_bilinear_band_count_bound d hd
  refine ⟨C*(4 : ℝ)^(2*(d : ℝ)),by positivity,?_⟩
  intro L τ hL hτ hwindow a b β s hs
  have hLp : 0 < L := by linarith only [hL]
  have hLp' : 0 < 4*L := by positivity
  have hsub : (s : Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
      WeylSums.bilinearBandSet (4*L) ((4 : ℝ)⁻¹ • a) ((4 : ℝ)⁻¹ • b) (β/16) (τ/16) := by
    intro q hq
    obtain ⟨ha,hb,he⟩ := hs q hq
    change ‖latticePoint (4*L) q.1-(4 : ℝ)⁻¹ • a‖ ≤ 2 ∧
      ‖latticePoint (4*L) q.2-(4 : ℝ)⁻¹ • b‖ ≤ 2 ∧ _
    rw [latticePoint_four_mul,latticePoint_four_mul,← smul_sub,← smul_sub,
      norm_smul,norm_smul,Real.norm_eq_abs]
    norm_num only [abs_inv,abs_of_pos (by norm_num : (0 : ℝ) < 4),inv_pos] at *
    refine ⟨by linarith only [ha],by linarith only [hb],?_⟩
    rw [real_inner_smul_left,real_inner_smul_right]
    have hid : (1/4 : ℝ)*((1/4 : ℝ)*inner ℝ (latticePoint L q.1) (latticePoint L q.2))-β/16 =
        (inner ℝ (latticePoint L q.1) (latticePoint L q.2)-β)/16 := by ring
    rw [hid,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 16)]
    exact div_le_div_of_nonneg_right he (by norm_num)
  have hwin : 1/(τ/16) ≤ (4*L)^2 := by
    have hh := mul_le_mul_of_nonneg_left hwindow (by norm_num : (0 : ℝ) ≤ 16)
    convert hh using 1 <;> ring
  have hc := Set.ncard_le_ncard hsub (WeylSums.finite_bilinearBandSet hLp' _ _ _ _)
  have hcR : (s.card : ℝ) ≤
      (WeylSums.bilinearBandSet (4*L) ((4 : ℝ)⁻¹ • a) ((4 : ℝ)⁻¹ • b) (β/16) (τ/16)).ncard := by
    exact_mod_cast (by simpa only [Set.ncard_coe_finset] using hc)
  have hh := hcR.trans (hb (4*L) (τ/16) (by linarith only [hL]) (by positivity) hwin _ _ _)
  calc
    _ ≤ C*(τ/16)*(4*L)^(2*(d : ℝ)) := hh
    _ ≤ C*τ*(4*L)^(2*(d : ℝ)) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [hτ] : τ/16 ≤ τ) hC.le) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hLp.le]; ring

end WaveTurbulence.CountLemmas
