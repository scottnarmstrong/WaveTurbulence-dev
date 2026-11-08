/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSKernelBound
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS

/-! # B3s MK-SLOTS (cap slots): centring a superposition at one momentum

A cap slot is evaluated at ONE momentum `k₀` only. A time superposition `Σ_l w_l u_l e(m_l · ts)` of complex numbers
`|u_l| ≤ 1` becomes a superposition with `SlotFam`-compatible amplitudes (`‖amp‖ ≤ 1`, `SNorm (30 d) 0 amp ≤ 1`,
supported within distance `1` of a lattice point `latPt d c`) by multiplying with one fixed bump `ψ` around the rounded
lattice point of `k₀`, normalized so that `ψ k₀ = K⁻¹`; the weights are multiplied by `K = K(d) ≥ 1`.

* `capThetaMin`, `le_theta1_of_mem`: `theta1 ≥ capThetaMin > 0` on `[1/2, 3/2]`;
* `capRound`, `pow_le_chi_capRound`: `χ_{round k}(k) ≥ capThetaMin ^ d`;
* `exists_capBump`: the normalized bump;
* **`cap_centre`**: centring of a superposition at one momentum (weights `K · w`, the same modes). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3.FS Finset

namespace WaveTurbulence.Flower.MkSlots

/-- The minimum of the one-dimensional bump `theta1` on `[1/2, 3/2]`. -/
def capThetaMin : ℝ := min (Real.smoothTransition (1 / 2)) (1 - Real.smoothTransition (1 / 2))

theorem capThetaMin_pos : 0 < capThetaMin :=
  lt_min (Real.smoothTransition.pos_of_pos (by norm_num))
    (sub_pos.2 (Real.smoothTransition.lt_one_of_lt_one (by norm_num)))

theorem capThetaMin_le_one : capThetaMin ≤ 1 :=
  (min_le_left _ _).trans (Real.smoothTransition.le_one _)

theorem le_theta1_of_mem {y : ℝ} (h1 : 1 / 2 ≤ y) (h2 : y ≤ 3 / 2) : capThetaMin ≤ RepAnalytic.theta1 y := by
  unfold RepAnalytic.theta1
  rcases le_total y 1 with hy | hy
  · have h0 : Real.smoothTransition (y - 1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [h0, sub_zero]
    exact (min_le_left _ _).trans (Real.smoothTransition.monotone h1)
  · rw [Real.smoothTransition.one_of_one_le hy]
    have := Real.smoothTransition.monotone (show y - 1 ≤ 1 / 2 by linarith)
    exact (min_le_right _ _).trans (by linarith)

/-- The rounded lattice index of a momentum. -/
def capRound (d : ℕ) (k : Mom d) : Fin d → ℤ := fun i => round (k i / RepAnalytic.lsp d)

theorem chi_eq_prod (d : ℕ) (n : Fin d → ℤ) (k : Mom d) :
    RepAnalytic.chi d n k = ∏ i, RepAnalytic.theta1 (k i / RepAnalytic.lsp d - (n i : ℝ) + 1) := by
  unfold RepAnalytic.chi RepAnalytic.chi0 RepAnalytic.latPt
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha := (RepAnalytic.lsp_pos d).ne'
  congr 1
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  field_simp

theorem pow_le_chi_capRound (d : ℕ) (k : Mom d) :
    capThetaMin ^ d ≤ RepAnalytic.chi d (capRound d k) k := by
  rw [chi_eq_prod]
  have h : ∏ _i : Fin d, capThetaMin = capThetaMin ^ d := by simp
  rw [← h]
  refine Finset.prod_le_prod₀ (fun _ _ => capThetaMin_pos.le) fun i _ => le_theta1_of_mem ?_ ?_
  · have := abs_sub_round (k i / RepAnalytic.lsp d)
    rw [abs_le] at this
    unfold capRound
    linarith [this.2]
  · have := abs_sub_round (k i / RepAnalytic.lsp d)
    rw [abs_le] at this
    unfold capRound
    linarith [this.1]

theorem chi_le_one (d : ℕ) (n : Fin d → ℤ) (k : Mom d) : RepAnalytic.chi d n k ≤ 1 := by
  rw [chi_eq_prod]
  exact Finset.prod_le_one₀ (fun _ _ => RepAnalytic.theta1_nonneg _) fun _ _ => RepAnalytic.theta1_le_one _

/-- **The normalized bump**: for every momentum `k₀` a function `ψ` bounded by `1`, of `SNorm (30 d) 0` at most `1`,
supported within distance `1` of a lattice point, with `ψ k₀ = K⁻¹` (`K ≥ 1` depending on `d` only). -/
theorem exists_capBump (d : ℕ) : ∃ K : ℝ, 1 ≤ K ∧ ∀ k₀ : Mom d, ∃ (c : Fin d → ℤ) (ψ : Mom d → ℂ),
    (∀ k, ‖ψ k‖ ≤ 1) ∧ SNorm (30 * d) 0 ψ ≤ 1 ∧ (∀ k, ψ k ≠ 0 → ‖k - RepAnalytic.latPt d c‖ ≤ 1) ∧
    ψ k₀ = ((K⁻¹ : ℝ) : ℂ) := by
  obtain ⟨C, hC, hCb⟩ := RepAnalytic.snorm_chiC_le d (30 * d)
  have hmm : 0 < capThetaMin ^ d := pow_pos capThetaMin_pos d
  have hmm1 : capThetaMin ^ d ≤ 1 := pow_le_one₀ capThetaMin_pos.le capThetaMin_le_one
  set K := max 1 C / capThetaMin ^ d with hK
  have hK1 : 1 ≤ K := by
    rw [hK, le_div_iff₀ hmm, one_mul]
    exact hmm1.trans (le_max_left _ _)
  refine ⟨K, hK1, fun k₀ => ?_⟩
  set c := capRound d k₀
  set v := RepAnalytic.chi d c k₀ with hv
  have hv0 : capThetaMin ^ d ≤ v := pow_le_chi_capRound d k₀
  have hvpos : 0 < v := hmm.trans_le hv0
  have hKv : max 1 C ≤ K * v := by
    rw [hK, div_mul_eq_mul_div, le_div_iff₀ hmm]
    exact mul_le_mul_of_nonneg_left hv0 (le_trans zero_le_one (le_max_left _ _))
  have hKvpos : 0 < K * v := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hKv)
  refine ⟨c, fun k => (((K * v)⁻¹ : ℝ) : ℂ) * RepAnalytic.chiC d c k, fun k => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, RepAnalytic.chiC, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hKvpos), abs_of_nonneg (RepAnalytic.chi_nonneg d c k)]
    calc (K * v)⁻¹ * RepAnalytic.chi d c k ≤ (K * v)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (chi_le_one d c k) (inv_pos.2 hKvpos).le
      _ = (K * v)⁻¹ := mul_one _
      _ ≤ 1 := inv_le_one_of_one_le₀ ((le_max_left _ _).trans hKv)
  · refine (VineEstS3.Eng.SNorm_smul_le (30 * d) 0 _ _).trans ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hKvpos)]
    refine (mul_le_mul' le_rfl (hCb c)).trans ?_
    rw [← ENNReal.ofReal_mul (inv_pos.2 hKvpos).le, ENNReal.ofReal_le_one, inv_mul_le_iff₀ hKvpos, mul_one]
    exact (le_max_right _ _).trans hKv
  · have hne : RepAnalytic.chi d c k ≠ 0 := by
      intro h0
      apply hk
      simp [RepAnalytic.chiC, h0]
    exact RepAnalytic.norm_sub_le_one_of_chi_ne_zero hne
  · show (((K * v)⁻¹ : ℝ) : ℂ) * ((v : ℝ) : ℂ) = ((K⁻¹ : ℝ) : ℂ)
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp

/-- **Centring at one momentum.** A superposition `Σ_l w_l u_l e(m_l · ts)` (`w ≥ 0` summable, `|u_l| ≤ 1`) of a
function `F` on a set `B` is, at the momentum `k₀`, a superposition with the weights `K · w` and amplitudes bounded by
`1`, of `SNorm (30 d) 0` at most `1`, centred within distance `1` of a lattice point; the moment mass is multiplied by
`K = K(d) ≥ 1`. -/
theorem cap_centre (d : ℕ) : ∃ K : ℝ, 1 ≤ K ∧ ∀ (θ : ℝ) {Λ : Type} (B : Set (Fin 2 → ℝ)) (F : (Fin 2 → ℝ) → ℂ)
    (k₀ : Mom d) (w : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (u : Λ → ℂ), (∀ l, 0 ≤ w l) → Summable w → (∀ l, ‖u l‖ ≤ 1) →
    (∀ ts ∈ B, HasSum (fun l => (w l : ℂ) * u l * fsPhase (m l) ts) (F ts)) →
    ∃ (c : Λ → Fin d → ℤ) (amp : Λ → Mom d → ℂ),
      (∀ l, 0 ≤ K * w l) ∧ Summable (fun l => K * w l) ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧
      (∀ l, SNorm (30 * d) 0 (amp l) ≤ 1) ∧ (∀ l k, amp l k ≠ 0 → ‖k - RepAnalytic.latPt d (c l)‖ ≤ 1) ∧
      (∀ ts ∈ B, HasSum (fun l => ((K * w l : ℝ) : ℂ) * amp l k₀ * fsPhase (m l) ts) (F ts)) ∧
      ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (K * w l) =
        ENNReal.ofReal K * ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (w l) := by
  obtain ⟨K, hK1, hb⟩ := exists_capBump d
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  refine ⟨K, hK1, fun θ Λ B F k₀ w m u hw hws hu hF => ?_⟩
  obtain ⟨c, ψ, hψ1, hψS, hψc, hψk⟩ := hb k₀
  refine ⟨fun _ => c, fun l k => u l * ψ k, fun l => mul_nonneg hK0.le (hw l), hws.mul_left K,
    fun l k => ?_, fun l => ?_, fun l k hk => hψc k (right_ne_zero_of_mul hk), fun ts hts => ?_, ?_⟩
  · rw [norm_mul]
    calc ‖u l‖ * ‖ψ k‖ ≤ 1 * 1 := mul_le_mul (hu l) (hψ1 k) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · refine (VineEstS3.Eng.SNorm_smul_le (30 * d) 0 _ _).trans ?_
    calc ‖u l‖ₑ * SNorm (30 * d) 0 ψ ≤ 1 * 1 := mul_le_mul' (by
          rw [← ofReal_norm, ENNReal.ofReal_le_one]; exact hu l) hψS
      _ = 1 := one_mul 1
  · refine (hF ts hts).congr_fun fun l => ?_
    show ((K * w l : ℝ) : ℂ) * (u l * ψ k₀) * fsPhase (m l) ts = _
    rw [hψk, Complex.ofReal_mul]
    have : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hK0.ne'
    simp only [Complex.ofReal_inv]
    field_simp
  · rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun l => ?_
    rw [ENNReal.ofReal_mul hK0.le]
    ring

end WaveTurbulence.Flower.MkSlots
