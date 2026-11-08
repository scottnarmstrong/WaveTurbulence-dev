/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Step
/-! # CAPS-FUBINI: summability of the kernel summand for `leafProd`-dominated weights, for every `L > 0`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsFub
open Finset MeasureTheory Set GraftGen LGSpine

theorem latticePoint_eq_smul {d : ℕ} (L : ℝ) (m : Fin d → ℤ) :
    latticePoint L m = L⁻¹ • latticePoint 1 m := by
  ext j; simp [latticePoint, div_eq_inv_mul]

theorem summable_jbr_lattice {d : ℕ} {L : ℝ} (hL : 0 < L) :
    Summable fun m : Fin d → ℤ => jbr (latticePoint L m) ^ (-((d : ℝ) + 1)) := by
  by_cases h1 : 1 ≤ L
  · exact Induct.summable_jbr_rpow_neg h1
  · rw [not_le] at h1
    refine Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (Polar.jbr_pos_p _).le _) (fun m => ?_)
      (Induct.summable_jbr_rpow_neg (d := d) (L := 1) le_rfl)
    apply Real.rpow_le_rpow_of_nonpos (Polar.jbr_pos_p _)
    · unfold jbr
      apply Real.sqrt_le_sqrt
      have : ‖latticePoint 1 m‖ ≤ ‖latticePoint L m‖ := by
        rw [latticePoint_eq_smul L m, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL]
        have : 1 ≤ L⁻¹ := (one_le_inv₀ hL).2 h1.le
        nlinarith [norm_nonneg (latticePoint 1 m : Mom d)]
      nlinarith [norm_nonneg (latticePoint 1 m : Mom d)]
    · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith

/-- Pointwise decay of a pair function of finite `S^{40d,40d}` norm. -/
theorem abs_le_of_SNormR {d : ℕ} (F : Mom d → ℝ) (b : ℝ) (hb : 1 ≤ b)
    (h : SNormR (40 * d) (40 * d) F ≤ ENNReal.ofReal b) (x : Mom d) :
    |F x| ≤ b * jbr x ^ (-((d + 1 : ℕ) : ℝ)) := by
  have h0 := Induct.SNormR_pointwise F b (by linarith) h x
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : jbr x = 1 := by
      have : x = 0 := Subsingleton.elim _ _
      simp [jbr, this]
    simpa [this] using h0
  · refine h0.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    apply Real.rpow_le_rpow_of_exponent_le (Induct.one_le_jbr _)
    have : ((d + 1 : ℕ) : ℝ) ≤ ((40 * d : ℕ) : ℝ) := by exact_mod_cast (by omega)
    linarith

/-- `summable_kernelGenFactor_dom` with only `0 < L`. -/
theorem summable_kernelGenFactor_dom' {w d : ℕ} (L γ δ : ℝ) (hL : 0 < L) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (up : GBranch LG.garden.tree → ℝ) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hn : ∀ ℓ, LG.garden.mark ℓ ≠ some MarkTag.lower)
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hwt : ∀ k, |wt k| ≤ ∏ ℓ ∈ inputLeaves LG.garden, (C * jbr (k ℓ.toNode) ^ (-((d + 1 : ℕ) : ℝ)))) :
    Summable (kernelGenFactor L γ δ (fun _ _ => 1) LG fix off wt up 0 (n := n) (nfl := nfl)) := by
  set F : ℕ → Mom d → ℝ := fun _ x => C * jbr x ^ (-((d + 1 : ℕ) : ℝ)) with hFdef
  have hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (0 + latticePoint L m)| := by
    intro q
    refine ((summable_jbr_lattice (d := d) hL).mul_left C).congr fun m => ?_
    simp only [hFdef]
    rw [abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (Polar.jbr_pos_p _).le _))]
    push_cast; rw [zero_add]
  have hsum := summable_kernelGenFactor L γ δ F LG fix off (fun _ => 1) (fun _ => by simp) up 0 n nfl hn hF
  have hnorm : Summable fun κ => ‖kernelGenFactor L γ δ F LG fix off (fun _ => 1) up 0
      (n := n) (nfl := nfl) κ‖ := hsum.norm
  refine Summable.of_norm_bounded hnorm fun κ => ?_
  have e1 : ‖kernelGenFactor L γ δ (fun _ _ => 1) LG fix off wt up 0 κ‖ =
      ‖(epsDec LG.garden κ.1 : ℂ)‖ * ‖genIntegral L γ δ LG fix off up (cosetDecoration LG.garden L 0 κ.1)‖ *
        |wt (cosetDecoration LG.garden L 0 κ.1)| := by
    unfold kernelGenFactor
    simp only [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs, norm_one, Finset.prod_const_one,
      mul_one]
    ring
  have e2 : ‖kernelGenFactor L γ δ F LG fix off (fun _ => 1) up 0 κ‖ =
      ‖(epsDec LG.garden κ.1 : ℂ)‖ * ‖genIntegral L γ δ LG fix off up (cosetDecoration LG.garden L 0 κ.1)‖ *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (C * jbr (cosetDecoration LG.garden L 0 κ.1 ℓ.toNode) ^ (-((d + 1 : ℕ) : ℝ))) := by
    unfold kernelGenFactor
    simp only [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_one, one_mul, mul_one]
    congr 1
    refine prod_congr rfl fun ℓ _ => ?_
    simp only [hFdef]
    exact abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (Polar.jbr_pos_p _).le _))
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (hwt _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end WaveTurbulence.Flower.CapsFub
