/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Basic

/-!
# A smooth partition of unity subordinate to unit cubes (packet NT6)

The proof of DH23 Prop 6.4 given here localizes every momentum variable to a unit cube.
We use the explicit one-dimensional profile `θ₁(t) = S(t+1) - S(t)`, where `S` is
`Real.smoothTransition`; it is smooth, supported in `[-1,1]`, takes values in `[0,1]`, and its
integer translates sum to one (the sum telescopes). The `d`-dimensional profile is the tensor
product `θ(x) = ∏ᵢ θ₁(xᵢ)`.
-/

public section

noncomputable section

open MeasureTheory Metric WithLp Finset
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.ApproxNT

/-- The one-dimensional profile `θ₁(t) = S(t+1) - S(t)`. -/
@[expose] def theta1 (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t

theorem theta1_nonneg (t : ℝ) : 0 ≤ theta1 t :=
  sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

theorem theta1_le_one (t : ℝ) : theta1 t ≤ 1 := by
  have h1 := Real.smoothTransition.le_one (t + 1)
  have h2 := Real.smoothTransition.nonneg t
  rw [theta1]; linarith

theorem theta1_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : theta1 t = 0 := by
  rcases le_abs.mp ht with h | h
  · rw [theta1, Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le h, sub_self]
  · rw [theta1, Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem contDiff_theta1 : ContDiff ℝ ∞ theta1 :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

/-- Integer translates of `θ₁` sum to one (a telescoping sum). -/
theorem sum_theta1 (t : ℝ) :
    ∑ i ∈ range 4, theta1 (t - ((⌊t⌋ - 1 + i : ℤ) : ℝ)) = 1 := by
  set f : ℕ → ℝ := fun i => Real.smoothTransition (t - ((⌊t⌋ - 2 + i : ℤ) : ℝ))
  have hterm : ∀ i ∈ range 4, theta1 (t - ((⌊t⌋ - 1 + i : ℤ) : ℝ)) = f i - f (i + 1) := by
    intro i _
    simp only [theta1, f]
    congr 2 <;> push_cast <;> ring
  rw [sum_congr rfl hterm, sum_range_sub']
  have hf0 : f 0 = 1 := by
    simp only [f]
    apply Real.smoothTransition.one_of_one_le
    have := Int.floor_le t
    push_cast; linarith
  have hf4 : f 4 = 0 := by
    simp only [f]
    apply Real.smoothTransition.zero_of_nonpos
    have := Int.lt_floor_add_one t
    push_cast; linarith
  rw [hf0, hf4, sub_zero]

/-- `θ₁(t - k)` vanishes unless `k` is one of the four integers `⌊t⌋ - 1 + i`, `i < 4`. -/
theorem theta1_sub_eq_zero {t : ℝ} {k : ℤ}
    (hk : k ∉ (range 4).image (fun i : ℕ => ⌊t⌋ - 1 + (i : ℤ))) : theta1 (t - k) = 0 := by
  apply theta1_eq_zero
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨h1, h2⟩ := abs_lt.mp hlt
  have hf1 := Int.floor_le t
  have hf2 := Int.lt_floor_add_one t
  have hk1 : ⌊t⌋ - 1 ≤ k := by
    have : (⌊t⌋ : ℝ) - 2 < k := by linarith
    have : ⌊t⌋ - 2 < k := by exact_mod_cast this
    omega
  have hk2 : k ≤ ⌊t⌋ + 2 := by
    have : (k : ℝ) < ⌊t⌋ + 2 := by linarith
    have : k < ⌊t⌋ + 2 := by exact_mod_cast this
    omega
  apply hk
  refine mem_image.2 ⟨(k - (⌊t⌋ - 1)).toNat, mem_range.2 ?_, ?_⟩
  · omega
  · omega

/-- The finite set of integers `k` with `θ₁(t - k) ≠ 0` possible. -/
@[expose] def theta1Support (t : ℝ) : Finset ℤ := (range 4).image (fun i : ℕ => ⌊t⌋ - 1 + (i : ℤ))

theorem sum_theta1Support (t : ℝ) : ∑ k ∈ theta1Support t, theta1 (t - k) = 1 := by
  rw [theta1Support, sum_image (fun i _ j _ h => by simpa using h)]
  exact sum_theta1 t

/-- The tensor-product cutoff `θ(x) = ∏ᵢ θ₁(xᵢ)` on `ℝ^d`. -/
@[expose] def thetaMom (d : ℕ) (x : Mom d) : ℝ := ∏ i, theta1 (x i)

variable {d : ℕ}

theorem thetaMom_nonneg (x : Mom d) : 0 ≤ thetaMom d x :=
  prod_nonneg fun _ _ => theta1_nonneg _

theorem thetaMom_le_one (x : Mom d) : thetaMom d x ≤ 1 :=
  prod_le_one₀ (fun _ _ => theta1_nonneg _) fun _ _ => theta1_le_one _

theorem thetaMom_eq_zero {x : Mom d} {i : Fin d} (hi : 1 ≤ |x i|) : thetaMom d x = 0 :=
  prod_eq_zero (mem_univ i) (theta1_eq_zero hi)

theorem abs_lt_one_of_thetaMom_ne_zero {x : Mom d} (hx : thetaMom d x ≠ 0) (i : Fin d) :
    |x i| < 1 := by
  by_contra h
  exact hx (thetaMom_eq_zero (not_lt.mp h))

theorem contDiff_thetaMom : ContDiff ℝ ∞ (thetaMom d) := by
  unfold thetaMom
  refine contDiff_prod fun i _ => contDiff_theta1.comp ?_
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).contDiff

theorem thetaMom_support_subset :
    Function.support (thetaMom d) ⊆ Metric.closedBall 0 (Real.sqrt d) := by
  intro x hx
  rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
        have := abs_lt_one_of_thetaMom_ne_zero hx i
        nlinarith [abs_nonneg (x i), sq_abs (x i)]
    _ = d := by simp

theorem hasCompactSupport_thetaMom : HasCompactSupport (thetaMom d) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) thetaMom_support_subset

/-- The integer translates of `θ` that can be nonzero at `x`. -/
@[expose] def thetaSupport (x : Mom d) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => theta1Support (x i)

theorem thetaMom_sub_intVec (x : Mom d) (g : Fin d → ℤ) :
    thetaMom d (x - NTSP.intVec g) = ∏ i, theta1 (x i - g i) := by
  simp [thetaMom, NTSP.intVec_apply]

theorem thetaMom_sub_eq_zero {x : Mom d} {g : Fin d → ℤ} (hg : g ∉ thetaSupport x) :
    thetaMom d (x - NTSP.intVec g) = 0 := by
  rw [thetaSupport, Fintype.mem_piFinset] at hg
  simp only [not_forall] at hg
  obtain ⟨i, hi⟩ := hg
  rw [thetaMom_sub_intVec]
  exact prod_eq_zero (mem_univ i) (theta1_sub_eq_zero (by simpa [theta1Support] using hi))

/-- The partition of unity: `∑_{g ∈ ℤ^d} θ(x - g) = 1`. -/
theorem sum_thetaMom (x : Mom d) : ∑ g ∈ thetaSupport x, thetaMom d (x - NTSP.intVec g) = 1 := by
  simp_rw [thetaMom_sub_intVec]
  rw [thetaSupport, ← prod_univ_sum (fun i => theta1Support (x i)) (fun i k => theta1 (x i - k))]
  exact prod_eq_one fun i _ => sum_theta1Support (x i)

/-- The cutoff as a Schwartz function (it is smooth with compact support). -/
@[expose] def thetaSchwartz (d : ℕ) : 𝓢(Mom d, ℝ) :=
  hasCompactSupport_thetaMom.toSchwartzMap contDiff_thetaMom

theorem thetaSchwartz_apply (x : Mom d) : thetaSchwartz d x = thetaMom d x := rfl

/-- Derivative bounds of the cutoff. -/
@[expose] def thetaDerivConst (d k : ℕ) : ℝ := SchwartzMap.seminorm ℝ 0 k (thetaSchwartz d)

theorem thetaDerivConst_nonneg (d k : ℕ) : 0 ≤ thetaDerivConst d k := apply_nonneg _ _

theorem norm_iteratedFDeriv_thetaMom_le (k : ℕ) (x : Mom d) :
    ‖iteratedFDeriv ℝ k (thetaMom d) x‖ ≤ thetaDerivConst d k := by
  have h := (thetaSchwartz d).norm_iteratedFDeriv_le_seminorm ℝ k x
  exact h

theorem norm_iteratedFDeriv_thetaMom_sub_le (k : ℕ) (p x : Mom d) :
    ‖iteratedFDeriv ℝ k (fun x => thetaMom d (x - p)) x‖ ≤ thetaDerivConst d k := by
  rw [iteratedFDeriv_comp_sub]
  exact norm_iteratedFDeriv_thetaMom_le k _

end WaveTurbulence.ApproxNT
