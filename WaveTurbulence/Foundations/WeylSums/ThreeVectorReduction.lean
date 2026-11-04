/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearBandCount

/-! # Conservation and energy reduction for the three-vector lattice count -/

public section
open Set Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- The three-vector set with one conserved momentum and an energy band. -/
@[expose] def threeVectorBandSet {d : ℕ} (L : ℝ) (nk : Fin d → ℤ)
    (a b c : Mom d) (β τ : ℝ) : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | q.1-q.2.1+q.2.2 = nk ∧ ‖latticePoint L q.1-a‖ ≤ 1 ∧
    ‖latticePoint L q.2.1-b‖ ≤ 1 ∧ ‖latticePoint L q.2.2-c‖ ≤ 1 ∧
    |‖latticePoint L q.1‖^2-‖latticePoint L q.2.1‖^2+‖latticePoint L q.2.2‖^2-β| ≤ τ}

/-- The two free differences after imposing momentum conservation. -/
@[expose] def threeVectorDifferences {d : ℕ}
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) : (Fin d → ℤ) × (Fin d → ℤ) :=
  (q.1-q.2.1,q.2.2-q.2.1)

theorem latticePoint_sub_eq {d : ℕ} (L : ℝ) (m n : Fin d → ℤ) :
    latticePoint L (m-n) = latticePoint L m-latticePoint L n := by
  ext i
  simp only [latticePoint,PiLp.sub_apply,Pi.sub_apply,Int.cast_sub]
  ring

theorem latticePoint_add_eq {d : ℕ} (L : ℝ) (m n : Fin d → ℤ) :
    latticePoint L (m+n) = latticePoint L m+latticePoint L n := by
  ext i
  simp only [latticePoint,PiLp.add_apply,Pi.add_apply,Int.cast_add]
  ring

/-- The sign of the bilinear energy term is negative for the free
variables `(k₁-k₂,k₃-k₂)`. -/
theorem three_vector_energy_identity {d : ℕ} (x y z : Mom d) :
    ‖x‖^2-‖y‖^2+‖z‖^2 = ‖x-y+z‖^2-2*inner ℝ (x-y) (z-y) := by
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.inner_apply,Real.inner_apply,PiLp.sub_apply,PiLp.add_apply]
  rw [← sum_sub_distrib,← sum_add_distrib,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  ring

/-- Difference coordinates inject the three-vector set into a bilinear
band count on radius-two balls. -/
theorem threeVectorDifferences_mapsTo {d : ℕ} (L : ℝ) (nk : Fin d → ℤ)
    (a b c : Mom d) (β τ : ℝ) :
    MapsTo threeVectorDifferences (threeVectorBandSet L nk a b c β τ)
      (bilinearBandSet L (a-b) (c-b) ((‖latticePoint L nk‖^2-β)/2) (τ/2)) := by
  intro q hq
  obtain ⟨hcon,ha,hb,hc,henergy⟩ := hq
  change ‖latticePoint L (q.1-q.2.1)-(a-b)‖ ≤ 2 ∧
    ‖latticePoint L (q.2.2-q.2.1)-(c-b)‖ ≤ 2 ∧ _
  have hnorm (x y a b : Mom d) (hx : ‖x-a‖ ≤ 1) (hy : ‖y-b‖ ≤ 1) :
      ‖(x-y)-(a-b)‖ ≤ 2 := by
    have heq : (x-y)-(a-b) = (x-a)-(y-b) := by abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith)
  refine ⟨?_,?_,?_⟩
  · rw [latticePoint_sub_eq]
    exact hnorm _ _ _ _ ha hb
  · rw [latticePoint_sub_eq]
    exact hnorm _ _ _ _ hc hb
  · have hmomentum : latticePoint L q.1-latticePoint L q.2.1+latticePoint L q.2.2 = latticePoint L nk := by
      rw [← latticePoint_sub_eq,← latticePoint_add_eq,hcon]
    have he := three_vector_energy_identity (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2)
    rw [hmomentum] at he
    dsimp only [threeVectorDifferences]
    rw [latticePoint_sub_eq,latticePoint_sub_eq]
    have harg : inner ℝ (latticePoint L q.1-latticePoint L q.2.1) (latticePoint L q.2.2-latticePoint L q.2.1)-
        (‖latticePoint L nk‖^2-β)/2 =
        -(‖latticePoint L q.1‖^2-‖latticePoint L q.2.1‖^2+‖latticePoint L q.2.2‖^2-β)/2 := by
      rw [he]
      ring
    rw [harg,abs_div,abs_neg]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right henergy (by norm_num)

/-- Momentum conservation reconstructs the middle vector from the two differences. -/
theorem threeVectorDifferences_injOn {d : ℕ} (L : ℝ) (nk : Fin d → ℤ)
    (a b c : Mom d) (β τ : ℝ) :
    InjOn threeVectorDifferences (threeVectorBandSet L nk a b c β τ) := by
  intro q hq r hr heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  have hqc := hq.1
  have hrc := hr.1
  apply Prod.ext
  · funext i
    have h₁ := congrFun hx i
    have h₂ := congrFun hy i
    have h₃ := congrFun hqc i
    have h₄ := congrFun hrc i
    simp only [threeVectorDifferences,Pi.sub_apply,Pi.add_apply] at h₁ h₂ h₃ h₄
    omega
  · apply Prod.ext <;> funext i
    all_goals
      have h₁ := congrFun hx i
      have h₂ := congrFun hy i
      have h₃ := congrFun hqc i
      have h₄ := congrFun hrc i
      simp only [threeVectorDifferences,Pi.sub_apply,Pi.add_apply] at h₁ h₂ h₃ h₄
      omega

theorem finite_threeVectorBandSet {d : ℕ} {L : ℝ} (hL : 0 < L) (nk : Fin d → ℤ)
    (a b c : Mom d) (β τ : ℝ) : (threeVectorBandSet L nk a b c β τ).Finite :=
  Set.Finite.of_injOn (threeVectorDifferences_mapsTo L nk a b c β τ)
    (threeVectorDifferences_injOn L nk a b c β τ) (finite_bilinearBandSet hL _ _ _ _)

/-- The cardinality reduction retains all source spatial centers and the
arbitrary conserved lattice momentum. -/
theorem threeVectorBandSet_ncard_le {d : ℕ} {L : ℝ} (hL : 0 < L) (nk : Fin d → ℤ)
    (a b c : Mom d) (β τ : ℝ) :
    (threeVectorBandSet L nk a b c β τ).ncard ≤
      (bilinearBandSet L (a-b) (c-b) ((‖latticePoint L nk‖^2-β)/2) (τ/2)).ncard :=
  ncard_le_ncard_of_injOn threeVectorDifferences (threeVectorDifferences_mapsTo L nk a b c β τ)
    (threeVectorDifferences_injOn L nk a b c β τ) (finite_bilinearBandSet hL _ _ _ _)

end WaveTurbulence.WeylSums
