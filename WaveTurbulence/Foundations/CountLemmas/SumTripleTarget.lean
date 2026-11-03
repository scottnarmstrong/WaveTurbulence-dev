/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.SumTripleBound
public import WaveTurbulence.Foundations.CountLemmas.SumPowers
public import WaveTurbulence.Foundations.WeylSums.CubicChainTarget

/-! # The exact triple power for the two sum selectors -/

public section
open Set Finset
namespace WaveTurbulence.CountLemmas

theorem latticePoint_sumTripleProjection {d : ℕ} (L : ℝ) (nv : Fin d → ℤ)
    (sel : Bool) (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
    latticePoint L (sumTripleProjection nv sel q).1 =
      latticePoint L q.1+latticePoint L q.2.1-latticePoint L nv-
        (if sel then latticePoint L q.2.2 else 0) := by
  dsimp only [sumTripleProjection]
  rw [WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_add_eq]
  cases sel <;> ext i <;> simp [latticePoint]

/-- TARGET Lemma A.8, the selectors `x+y-v` and `x+y-v-z`, with its exact
power and uniform tolerance constant. -/
theorem coupledTriple_sum_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ a b c : Mom d, ∀ nv : Fin d → ℤ, ∀ sel : Bool, ∀ α β : ℝ,
      ((coupledTripleSet L a b c (latticePoint L nv) α β (δ⁻¹*L^(-2*γ))
        (if sel then 2 else 1)).ncard : ℝ) ≤
      C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  obtain ⟨n,hn⟩ : ∃ n, d = n+2 := ⟨d-2,by omega⟩
  subst d
  obtain ⟨C,hC,hbound⟩ := exists_sum_triple_bound n (by omega)
  obtain ⟨R,hR,hupper⟩ := WeylSums.exists_upper_time_le_square
    (by norm_num : (0 : ℝ) < 1) hγ.2
  refine ⟨3*C*3^n,R,by positivity,?_⟩
  intro L hL δ hδ a b c nv sel α β
  have hL2 : 2 ≤ L := hR.trans hL
  have hLp : 0 < L := by linarith only [hL2]
  let τ := δ⁻¹*L^(-2*γ)
  have hτ : 0 < τ := mul_pos (inv_pos.mpr hδ.1) (Real.rpow_pos_of_pos hLp _)
  have hinv : 1/τ = δ*L^(2*γ) := by
    dsimp only [τ]
    rw [show -2*γ = -(2*γ) by ring,Real.rpow_neg hLp.le]
    field_simp [hδ.1.ne',(Real.rpow_pos_of_pos hLp (2*γ)).ne']
  have hwin : 1/τ ≤ L^2 := by
    rw [hinv]
    exact (mul_le_mul_of_nonneg_right hδ.2 (by positivity : 0 ≤ L^(2*γ))).trans
      (by simpa only [one_mul] using hupper L hL)
  have hW : 1 ≤ τ*L^2 := by
    simpa only [mul_comm] using (div_le_iff₀ hτ).mp hwin
  let S := (finite_coupledTripleSet hLp a b c (latticePoint L nv) α β τ
    (if sel then 2 else 1)).toFinset
  have hb := hbound L τ hL2 hτ hW hwin a b c nv sel α β S (by
    intro q hq
    have hh := (finite_coupledTripleSet hLp a b c (latticePoint L nv) α β τ
      (if sel then 2 else 1)).mem_toFinset.mp hq
    refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,?_⟩
    rw [latticePoint_sumTripleProjection]
    cases sel <;> simpa using hh.2.2.2.2)
  have hp := sum_triple_power_bound n hC.le (by linarith only [hL2] : 1 ≤ L) hδ.1 hδ.2 (γ := γ)
  rw [Set.ncard_eq_toFinset_card _ (finite_coupledTripleSet hLp a b c (latticePoint L nv) α β τ
    (if sel then 2 else 1))]
  rw [show 3*((((n+2 : ℕ) : ℝ))-γ)-min γ (1-γ) =
    3*(((n+2 : ℕ) : ℝ))-3*γ-min γ (1-γ) by ring]
  exact hb.trans hp

end WaveTurbulence.CountLemmas
