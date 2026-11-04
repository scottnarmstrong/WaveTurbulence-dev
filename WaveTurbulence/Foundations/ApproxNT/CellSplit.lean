/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Decompose

/-!
# Splitting `I` and the main integral over the cells meeting `E` (packet NT6)

With `Q` the finite set of cell configurations meeting the support set `E` (`Cells.lean`),
`W = ∑_{pq ∈ Q} W · cellWeight pq` pointwise; hence `I` and `∫ W Ψ` split into finitely many cell
contributions. We also record the regularity used for Fubini: the profile `Ψ` of
(propertypsi1) is continuous, and the cell weights are continuous with compact support.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped FourierTransform ContDiff

namespace WaveTurbulence.ApproxNT

variable {d n : ℕ}

theorem continuous_chiInf_div : Continuous (fun u : ℝ => Fourier.chiInfinity u / u) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  by_cases h0 : u₀ = 0
  · subst h0
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hu
    rw [Fourier.chiInfinity, Fourier.chi0_eq_one hu.le, sub_self, zero_div]
  · exact ((continuous_const.sub (Fourier.chi0_contDiff (n := 0)).continuous).continuousAt).div
      continuousAt_id h0

theorem continuous_resProfile (J : Finset (Fin n)) {Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ}
    (hΨ : Continuous Ψ₁) : Continuous (resProfile J Ψ₁) := by
  refine (continuous_finsetProd _ fun j _ => ?_).mul (hΨ.comp ?_)
  · exact Complex.continuous_ofReal.comp (continuous_chiInf_div.comp (continuous_apply j))
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply (i : Fin n))

theorem continuous_cellWeight (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) => cellWeight pq z.1 z.2) := by
  refine continuous_finsetProd _ fun j _ => ?_
  exact ((continuous_thetaC (d := d)).comp (((continuous_apply j).comp continuous_fst).sub
    continuous_const)).mul ((continuous_thetaC (d := d)).comp
      (((continuous_apply j).comp continuous_snd).sub continuous_const))

theorem hasCompactSupport_cellWeight (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    HasCompactSupport (fun z : (Fin n → Mom d) × (Fin n → Mom d) => cellWeight pq z.1 z.2) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_univ_pi fun j => isCompact_closedBall (NTSP.intVec (pq j).1) (Real.sqrt d)).prod
      (isCompact_univ_pi fun j => isCompact_closedBall (NTSP.intVec (pq j).2) (Real.sqrt d))) ?_
  intro z hz
  have hj : ∀ j, cellAmp (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (z.1 j) (z.2 j) ≠ 0 :=
    fun j h => hz (prod_eq_zero (mem_univ j) h)
  refine ⟨Set.mem_univ_pi.2 fun j => ?_, Set.mem_univ_pi.2 fun j => ?_⟩
  · have h1 : thetaMom d (z.1 j - NTSP.intVec (pq j).1) ≠ 0 := by
      intro h; apply hj j; simp [cellAmp, thetaC, h]
    have := thetaMom_support_subset (d := d) h1
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_eq_norm]; exact this
  · have h1 : thetaMom d (z.2 j - NTSP.intVec (pq j).2) ≠ 0 := by
      intro h; apply hj j; simp [cellAmp, thetaC, h]
    have := thetaMom_support_subset (d := d) h1
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_eq_norm]; exact this

/-- The partition of `W` over the cells meeting `E`. -/
theorem W_eq_sum_cells {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    {a b : Fin n → Mom d} {lam : Fin n → ℝ} {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hWs : ∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) (x y : Fin n → Mom d) :
    W x y = ∑ pq ∈ (cellBox_finite hxs hys a b lam).toFinset, W x y * cellWeight pq x y := by
  by_cases hW : W x y = 0
  · simp [hW]
  have hE := hWs x y hW
  rw [← mul_sum]
  set Q := (cellBox_finite hxs hys a b lam).toFinset
  have h1 : ∑ pq ∈ Q, cellWeight pq x y = ∑ pq ∈ Q ∩ localCells x y, cellWeight pq x y := by
    refine (sum_subset inter_subset_left fun pq hpq hn => ?_).symm
    exact cellWeight_eq_zero (fun hl => hn (mem_inter.2 ⟨hpq, hl⟩))
  have h2 : ∑ pq ∈ localCells x y, cellWeight pq x y =
      ∑ pq ∈ Q ∩ localCells x y, cellWeight pq x y := by
    refine (sum_subset inter_subset_right fun pq hpq hn => ?_).symm
    by_contra hw
    exact hn (mem_inter.2 ⟨(Set.Finite.mem_toFinset _).2 (mem_cellBox hE hw), hpq⟩)
  rw [h1, ← h2, sum_cellWeight, mul_one]

theorem summable_cell {L : ℝ} (hL : 0 < L) (μ : ℝ) (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ)
    (Ψ : (Fin n → ℝ) → ℂ) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    Summable (fun g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ) =>
      W (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) *
        cellWeight pq (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) *
        Ψ (fun j => μ * inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))) := by
  set G1 := Fintype.piFinset fun j => (finite_thetaLattice hL (NTSP.intVec (pq j).1)).toFinset
  set G2 := Fintype.piFinset fun j => (finite_thetaLattice hL (NTSP.intVec (pq j).2)).toFinset
  refine summable_of_ne_finset_zero (s := G1 ×ˢ G2) fun g hg => ?_
  have hw : cellWeight pq (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) = 0 := by
    rw [mem_product, not_and_or] at hg
    rcases hg with hg | hg
    · rw [Fintype.mem_piFinset] at hg
      simp only [not_forall] at hg
      obtain ⟨j, hj⟩ := hg
      refine prod_eq_zero (mem_univ j) ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hj
      simp [cellAmp, thetaC, hj]
    · rw [Fintype.mem_piFinset] at hg
      simp only [not_forall] at hg
      obtain ⟨j, hj⟩ := hg
      refine prod_eq_zero (mem_univ j) ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hj
      simp [cellAmp, thetaC, hj]
  rw [hw, mul_zero, zero_mul]

theorem approxSum_eq_sum_cells {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    {a b : Fin n → Mom d} {lam : Fin n → ℝ} {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hWs : ∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) {L : ℝ} (hL : 0 < L) (μ : ℝ)
    (Ψ : (Fin n → ℝ) → ℂ) :
    approxSum L μ W Ψ = ∑ pq ∈ (cellBox_finite hxs hys a b lam).toFinset,
      approxSum L μ (fun x y => W x y * cellWeight pq x y) Ψ := by
  simp only [approxSum]
  rw [← Summable.tsum_finsetSum fun pq _ => summable_cell hL μ W Ψ pq]
  refine tsum_congr fun g => ?_
  conv_lhs => rw [W_eq_sum_cells hxs hys hWs]
  rw [sum_mul]

theorem approxInt_eq_sum_cells {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    {a b : Fin n → Mom d} {lam : Fin n → ℝ} {W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hWs : ∀ x y, W x y ≠ 0 → (x, y) ∈ supportSet xs ys a b lam) (μ : ℝ)
    (Ψ : (Fin n → ℝ) → ℂ)
    (hint : ∀ pq, Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      W z.1 z.2 * cellWeight pq z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j)))) :
    approxInt μ W Ψ = ∑ pq ∈ (cellBox_finite hxs hys a b lam).toFinset,
      approxInt μ (fun x y => W x y * cellWeight pq x y) Ψ := by
  simp only [approxInt]
  rw [← integral_finsetSum _ fun pq _ => hint pq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  conv_lhs => rw [W_eq_sum_cells hxs hys hWs]
  rw [sum_mul]

end WaveTurbulence.ApproxNT
