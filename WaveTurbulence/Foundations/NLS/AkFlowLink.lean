/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkTruncFlow
public import WaveTurbulence.Foundations.NLS.AkPersistence
public import WaveTurbulence.Foundations.NLS.UniformDecay

/-!
# Classed solutions of the `a`-system and the truncated flow

* `isAkSolution_unweight_truncFlow`: while the truncated flow stays in the ball of radius `R`, its
  unweighted coefficients form a classed solution of (akeqn) (class from the `ℓ¹` bound).
* `IsAkSolution.hasDerivWithinAt_ofFun`: conversely, a classed solution with rapidly decreasing
  data is, in the weighted coordinates, a differentiable `ℓ¹`-valued solution of the flow
  (dominated convergence for the difference quotients, with the uniform decay of persistence),
  hence equals the truncated flow for every radius above its `ℓ¹` bound
  (`IsAkSolution.truncFlow_eq`).
* `exists_isAkSolution_iff`: for rapidly decreasing data, a classed solution on `[0, 𝔇]` exists
  iff the truncated flow of some integer radius `R` stays in the ball of radius `R` on `[0, 𝔇]`
  (the continuation criterion behind the measurability of the solvable set).
-/

public section

noncomputable section

open Complex Set Filter Topology Metric
open scoped ENNReal NNReal

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-! ### From functions to `ℓ¹` -/

open Classical in
/-- An absolutely summable family as an element of `ℓ¹` (`0` if it is not summable). -/
@[expose] def L1.ofFun (f : (Fin d → ℤ) → ℂ) : L1 d :=
  if h : Summable fun n => ‖f n‖ then L1.mk f h else 0

theorem L1.ofFun_apply {f : (Fin d → ℤ) → ℂ} (hf : Summable fun n => ‖f n‖) (n : Fin d → ℤ) :
    L1.ofFun f n = f n := by
  simp only [L1.ofFun, hf, ↓reduceDIte, L1.mk_apply]

theorem L1.coe_ofFun {f : (Fin d → ℤ) → ℂ} (hf : Summable fun n => ‖f n‖) :
    ((L1.ofFun f : L1 d) : (Fin d → ℤ) → ℂ) = f :=
  funext (L1.ofFun_apply hf)

/-- The weighted coefficients `(1 + ‖n‖)^{d+1} aₙ`. -/
@[expose] def weightUp (a : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ := (flowWeight n : ℂ) * a n

theorem unweight_weightUp (a : (Fin d → ℤ) → ℂ) : unweight (weightUp a) = a := by
  funext n
  rw [unweight, weightUp, mul_div_cancel_left₀ _ (ofReal_ne_zero.2 (flowWeight_pos n).ne')]

theorem norm_weightUp (a : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    ‖weightUp a n‖ = flowWeight n * ‖a n‖ := by
  rw [weightUp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (flowWeight_pos n).le]

theorem flowWeight_mul_norm_unweight (y : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    flowWeight n * ‖unweight y n‖ = ‖y n‖ := by
  rw [unweight, norm_div, Complex.norm_real, Real.norm_of_nonneg (flowWeight_pos n).le,
    mul_div_cancel₀ _ (flowWeight_pos n).ne']

theorem _root_.WaveTurbulence.IsRapidDecay.summable_norm_weightUp {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) :
    Summable fun n => ‖weightUp c n‖ := by
  simp_rw [norm_weightUp, flowWeight]
  exact (hc.summable_norm_mul_pow (d + 1)).congr fun n => mul_comm _ _

theorem unweight_ofFun_weightUp {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖weightUp c n‖) :
    unweight (L1.ofFun (weightUp c) : (Fin d → ℤ) → ℂ) = c := by
  rw [L1.coe_ofFun hc, unweight_weightUp]

/-! ### The class from an `ℓ¹` bound -/

theorem IsAkBounded.of_flowWeight_mul_le {L 𝔇 C : ℝ} (hL : 0 < L) {a : ℝ → (Fin d → ℤ) → ℂ}
    (h : ∀ t ∈ Icc 0 𝔇, ∀ n, flowWeight n * ‖a t n‖ ≤ C) : IsAkBounded L 𝔇 a := by
  set A := (1 + d / L ^ 2) ^ (((d : ℝ) + 1) / 2)
  refine ⟨A * C, fun t ht n => ?_⟩
  calc (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖a t n‖
      ≤ A * (1 + ‖n‖) ^ (d + 1) * ‖a t n‖ := by gcongr; exact japanese_le hL n
    _ = A * (flowWeight n * ‖a t n‖) := by rw [flowWeight]; ring
    _ ≤ A * C := by gcongr; exact h t ht n

/-! ### The truncated flow inside the ball gives a classed solution -/

variable {L γ δ R 𝔇 : ℝ}

/-- A solution `z` on `[0, 𝔇]` of the truncated system that stays in the ball of radius `R`
gives, unweighted, a classed solution of (akeqn). -/
theorem isAkSolution_unweight_of_hasDerivWithinAt (hL : 0 < L) {z : ℝ → L1 d} {x : L1 d}
    (hz0 : z 0 = x)
    (hz : ∀ t ∈ Icc 0 𝔇, HasDerivWithinAt z (truncField L γ δ R t (z t)) (Icc 0 𝔇) t)
    (hball : ∀ t ∈ Icc 0 𝔇, ‖z t‖ ≤ R) :
    IsAkSolution L γ δ 𝔇 (unweight x) fun t => unweight (z t) := by
  refine ⟨by subst hz0; rfl, IsAkBounded.of_flowWeight_mul_le hL (C := R) fun t ht n => ?_,
    fun t ht n => ?_⟩
  · rw [flowWeight_mul_norm_unweight]
    exact (lp.norm_apply_le_norm (by norm_num) _ n).trans (hball t ht)
  · have h := (((lp.evalCLM ℝ (fun _ : Fin d → ℤ => ℂ) 1 n).hasFDerivAt).comp_hasDerivWithinAt
      t (hz t ht)).div_const (flowWeight n : ℂ)
    rw [truncField_of_norm_le L γ δ t (hball t ht)] at h
    convert h using 1
    · funext s
      rfl
    · change aNonlin L γ δ 1 t _ _ _ n = flowTerm L γ δ t _ n / _
      rw [flowTerm, mul_div_cancel_left₀ _ (ofReal_ne_zero.2 (flowWeight_pos n).ne')]

theorem isAkSolution_unweight_truncFlow (hL : 0 < L) (hR : 0 ≤ R) (x : L1 d)
    (hball : ∀ t ∈ Icc 0 𝔇, ‖truncFlow L γ δ R 𝔇 x t‖ ≤ R) :
    IsAkSolution L γ δ 𝔇 (unweight x) fun t => unweight (truncFlow L γ δ R 𝔇 x t) :=
  isAkSolution_unweight_of_hasDerivWithinAt hL (truncFlow_zero L γ δ R 𝔇 x)
    (fun _ ht => hasDerivWithinAt_truncFlow hR x ht) hball

/-! ### A classed solution is a differentiable `ℓ¹`-valued solution -/

section Classed

variable {c : (Fin d → ℤ) → ℂ} {a : ℝ → (Fin d → ℤ) → ℂ}

/-- Along a classed solution with rapidly decreasing data, the weighted coefficients are
dominated, uniformly on `[0, 𝔇]`, by `C (1 + ‖n‖)^{-(d+1)}`, and the weighted right side of
(akeqn) by a summable family. -/
theorem IsAkSolution.exists_flow_majorants (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (hc : IsRapidDecay c) :
    ∃ C, 0 ≤ C ∧ ∃ Q : (Fin d → ℤ) → ℝ, Summable (fun n => flowWeight n * Q n) ∧
      ∀ t ∈ Icc 0 𝔇, ∀ n, flowWeight n * ‖a t n‖ ≤ C * ((1 + ‖n‖) ^ (d + 1))⁻¹ ∧
        ‖aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n‖ ≤ Q n := by
  obtain ⟨C₀, hC₀⟩ := ha.exists_uniform_decay hL hc (2 * (d + 1))
  set C := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hdec : ∀ t ∈ Icc 0 𝔇, ∀ n, ‖a t n‖ ≤ C * ((1 + ‖n‖) ^ (2 * (d + 1)))⁻¹ := fun t ht n => by
    have h := hC₀ t ht n
    rw [zpow_neg, zpow_natCast] at h
    exact h.trans (by gcongr; exact le_max_left _ _)
  set M : (Fin d → ℤ) → ℂ := fun n => ((C * ((1 + ‖n‖) ^ (2 * (d + 1)))⁻¹ : ℝ) : ℂ)
  have hM : ∀ n, ‖M n‖ = C * ((1 + ‖n‖) ^ (2 * (d + 1)))⁻¹ := fun n => by
    simp only [M, Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hwM : ∀ n, flowWeight n * (C * ((1 + ‖n‖) ^ (2 * (d + 1)))⁻¹) =
      C * ((1 + ‖n‖) ^ (d + 1))⁻¹ := fun n => by
    have hpos : 0 < 1 + ‖n‖ := by positivity
    rw [flowWeight, show 2 * (d + 1) = (d + 1) + (d + 1) by ring, pow_add]
    field_simp
    ring
  set κ := ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))|
  have hWM : wnorm (d + 1) M ≠ ∞ := by
    have hs : Summable fun n => flowWeight n * ‖M n‖ := by
      simp_rw [hM, hwM]
      exact summable_inv_one_add_norm_pow.mul_left C
    have : wnorm (d + 1) M = ∑' n, ENNReal.ofReal (flowWeight n * ‖M n‖) := by
      refine tsum_congr fun n => ?_
      rw [wt_eq_ofReal_flowWeight, ← ofReal_norm, ← ENNReal.ofReal_mul (flowWeight_pos n).le]
    rw [this, ← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (flowWeight_pos n).le (norm_nonneg _)) hs]
    exact ENNReal.ofReal_ne_top
  have hfin : ∑' n, wt (d + 1) n * (κ * tripleAbs M M M n) ≠ ∞ := by
    have : ∑' n, wt (d + 1) n * (κ * tripleAbs M M M n) =
        κ * ∑' n, wt (d + 1) n * tripleAbs M M M n := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun n => by ring
    rw [this]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hWM hWM) hWM) (tsum_wt_mul_tripleAbs_le _ _ _ _))
  set Q : (Fin d → ℤ) → ℝ := fun n => (κ * tripleAbs M M M n).toReal
  have hQfin : ∀ n, κ * tripleAbs M M M n ≠ ∞ := fun n => by
    have h1 := ne_top_of_le_ne_top hfin
      (ENNReal.le_tsum (f := fun n => wt (d + 1) n * (κ * tripleAbs M M M n)) n)
    have hw : 1 ≤ wt (d + 1) n :=
      one_le_pow₀ (ENNReal.one_le_ofReal.2 (by linarith [norm_nonneg n]))
    exact ne_top_of_le_ne_top h1 (le_mul_of_one_le_left' hw)
  refine ⟨C, hC0, Q, ?_, fun t ht n => ⟨?_, ?_⟩⟩
  · have hs := ENNReal.summable_toReal hfin
    refine hs.congr fun n => ?_
    rw [ENNReal.toReal_mul, wt_eq_ofReal_flowWeight, ENNReal.toReal_ofReal (flowWeight_pos n).le]
  · rw [← hwM]
    exact mul_le_mul_of_nonneg_left (hdec t ht n) (flowWeight_pos n).le
  · rw [← toReal_enorm]
    refine ENNReal.toReal_mono (hQfin n) ((enorm_aNonlin_le L γ δ t _ _ _ n).trans ?_)
    gcongr
    refine tripleAbs_mono (fun m => ?_) (fun m => ?_) (fun m => ?_) n <;>
      simp only [hM, Complex.norm_conj] <;> exact hdec t ht m

theorem IsAkSolution.summable_norm_weightUp (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (hc : IsRapidDecay c) {t : ℝ} (ht : t ∈ Icc 0 𝔇) : Summable fun n => ‖weightUp (a t) n‖ := by
  obtain ⟨C, hC0, Q, -, hQ⟩ := ha.exists_flow_majorants hL hc
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_inv_one_add_norm_pow.mul_left C)
  rw [norm_weightUp]
  exact (hQ t ht n).1

/-- The `ℓ¹` norm of the weighted coefficients of a classed solution with rapidly decreasing data
is bounded on `[0, 𝔇]`. -/
theorem IsAkSolution.exists_norm_ofFun_le (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (hc : IsRapidDecay c) : ∃ Y, ∀ t ∈ Icc 0 𝔇, ‖(L1.ofFun (weightUp (a t)) : L1 d)‖ ≤ Y := by
  obtain ⟨C, hC0, Q, -, hQ⟩ := ha.exists_flow_majorants hL hc
  refine ⟨C * ∑' n : Fin d → ℤ, ((1 + ‖n‖) ^ (d + 1))⁻¹, fun t ht => ?_⟩
  have hs := ha.summable_norm_weightUp hL hc ht
  rw [L1.norm_eq, L1.coe_ofFun hs, ← tsum_mul_left]
  refine hs.tsum_le_tsum (fun n => ?_) (summable_inv_one_add_norm_pow.mul_left C)
  rw [norm_weightUp]
  exact (hQ t ht n).1

/-- A classed solution with rapidly decreasing data is, in the weighted coordinates, a
differentiable `ℓ¹`-valued solution of `y' = flowField t y` on `[0, 𝔇]`. -/
theorem IsAkSolution.hasDerivWithinAt_ofFun (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (hc : IsRapidDecay c) {t : ℝ} (ht : t ∈ Icc 0 𝔇) :
    HasDerivWithinAt (fun s => (L1.ofFun (weightUp (a s)) : L1 d))
      (flowField L γ δ t (L1.ofFun (weightUp (a t)))) (Icc 0 𝔇) t := by
  obtain ⟨C, hC0, Q, hQs, hQ⟩ := ha.exists_flow_majorants hL hc
  set y : ℝ → L1 d := fun s => L1.ofFun (weightUp (a s))
  set a' : (Fin d → ℤ) → ℂ := fun n =>
    aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n
  have hy : ∀ s ∈ Icc 0 𝔇, ∀ n, y s n = flowWeight n * a s n := fun s hs n => by
    simp only [y]
    rw [L1.ofFun_apply (ha.summable_norm_weightUp hL hc hs), weightUp]
  have hF : ∀ n, flowField L γ δ t (y t) n = flowWeight n * a' n := fun n => by
    rw [flowField_apply, flowTerm]
    simp only [y]
    rw [L1.coe_ofFun (ha.summable_norm_weightUp hL hc ht), unweight_weightUp]
  set l := 𝓝[Icc 0 𝔇 \ {t}] t
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have hmem : ∀ᶠ s in l, s ∈ Icc 0 𝔇 \ {t} := self_mem_nhdsWithin
  -- coordinates of the difference quotient
  have hcoord : ∀ s ∈ Icc 0 𝔇 \ {t}, ∀ n,
      ((slope y t s - flowField L γ δ t (y t) : L1 d) : (Fin d → ℤ) → ℂ) n =
        flowWeight n * (slope (fun r => a r n) t s - a' n) := fun s hs n => by
    rw [lp.coeFn_sub, Pi.sub_apply, slope_def_module, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub,
      Pi.sub_apply, hy s hs.1, hy t ht, hF, slope_def_module]
    simp only [Complex.real_smul]
    ring
  have hlim : Tendsto (fun s => ∑' n,
      ‖((slope y t s - flowField L γ δ t (y t) : L1 d) : (Fin d → ℤ) → ℂ) n‖) l
      (𝓝 (∑' _ : Fin d → ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => 2 * (flowWeight n * Q n))
      (hQs.mul_left 2) (fun n => ?_) ?_
    · have h1 := (hasDerivWithinAt_iff_tendsto_slope.1 (ha.2.2 t ht n))
      have h2 : Tendsto (fun s => ‖(flowWeight n : ℂ) * (slope (fun r => a r n) t s - a' n)‖) l
          (𝓝 ‖(flowWeight n : ℂ) * (a' n - a' n)‖) :=
        ((tendsto_const_nhds.mul (h1.sub tendsto_const_nhds))).norm
      rw [sub_self, mul_zero, norm_zero] at h2
      refine h2.congr' (hmem.mono fun s hs => ?_)
      exact congrArg norm (hcoord s hs n).symm
    · filter_upwards [hmem] with s hs n
      rw [norm_norm, hcoord s hs n, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (flowWeight_pos n).le]
      have hst : s - t ≠ 0 := sub_ne_zero.2 hs.2
      have hmvt := (convex_Icc (0 : ℝ) 𝔇).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun r => a r n) (fun r hr => ha.2.2 r hr n) (fun r hr => (hQ r hr n).2) ht hs.1
      have hsl : ‖slope (fun r => a r n) t s‖ ≤ Q n := by
        rw [slope_def_module, norm_smul, norm_inv, ← div_eq_inv_mul,
          div_le_iff₀ (norm_pos_iff.2 hst)]
        exact hmvt
      calc flowWeight n * ‖slope (fun r => a r n) t s - a' n‖
          ≤ flowWeight n * (Q n + Q n) :=
            mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hsl ((hQ t ht n).2)))
              (flowWeight_pos n).le
        _ = 2 * (flowWeight n * Q n) := by ring
  rw [tsum_zero] at hlim
  refine hlim.congr fun s => ?_
  rw [L1.norm_eq]

/-- A classed solution with rapidly decreasing data, whose weighted `ℓ¹` norm stays below `R`,
is the truncated flow of radius `R` (in the weighted coordinates). -/
theorem IsAkSolution.truncFlow_eq (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (hc : IsRapidDecay c) (hR : ∀ t ∈ Icc 0 𝔇, ‖(L1.ofFun (weightUp (a t)) : L1 d)‖ ≤ R) :
    ∀ t ∈ Icc 0 𝔇, truncFlow L γ δ R 𝔇 (L1.ofFun (weightUp c)) t =
      L1.ofFun (weightUp (a t)) := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 𝔇 := ⟨le_rfl, ht.1.trans ht.2⟩
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 h0)
  refine (eqOn_truncFlow hR0 (z := fun s => (L1.ofFun (weightUp (a s)) : L1 d))
    (by simp only [ha.1]) (fun s hs => ?_) ht).symm
  rw [truncField_of_norm_le L γ δ s (hR s hs)]
  exact ha.hasDerivWithinAt_ofFun hL hc hs

end Classed

/-! ### The continuation criterion -/

/-- For rapidly decreasing data `c`, a classed solution of (akeqn) on `[0, 𝔇]` exists iff the
truncated flow of some integer radius `R` stays in the ball of radius `R` on `[0, 𝔇]`. -/
theorem exists_isAkSolution_iff (hL : 0 < L) {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) :
    (∃ a, IsAkSolution L γ δ 𝔇 c a) ↔
      ∃ R : ℕ, ∀ t ∈ Icc 0 𝔇, ‖truncFlow L γ δ R 𝔇 (L1.ofFun (weightUp c)) t‖ ≤ R := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨Y, hY⟩ := ha.exists_norm_ofFun_le hL hc
    refine ⟨⌈Y⌉₊, fun t ht => ?_⟩
    have hR : ∀ s ∈ Icc 0 𝔇, ‖(L1.ofFun (weightUp (a s)) : L1 d)‖ ≤ (⌈Y⌉₊ : ℝ) :=
      fun s hs => (hY s hs).trans (Nat.le_ceil Y)
    rw [ha.truncFlow_eq hL hc hR t ht]
    exact hR t ht
  · rintro ⟨R, hR⟩
    have h := isAkSolution_unweight_truncFlow hL (Nat.cast_nonneg R) _ hR
    rw [unweight_ofFun_weightUp (IsRapidDecay.summable_norm_weightUp hc)] at h
    exact ⟨_, h⟩

end WaveTurbulence.NLS
