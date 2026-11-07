/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.GlueMain
public import WaveTurbulence.Foundations.VineEst.K2.CrossRow
public import WaveTurbulence.Foundations.VineEst.K2.CrossDisp

/-! # W2-KIND2 EXPORT: the cross-window bound of the two-sided clamp in its consumer form

`crossBound_C_final`, `crossBound_T_final` (`0 < η < 1/4`): there is one constant `Kx ≥ 1` (depending on `η` only) such that for every gate level `q`, every pair of windows
`w + 1 ≤ w'` and every continuous gate time factor `Jc` with `‖Jc‖_{𝔛^{1-η}(box_q)} < CJ`, the two-sided clamp satisfies
`‖clamp2J q Jc‖_{𝔛^{1-2η}(box_{w'} ∪ box_w)} < Kx · CJ`.  This is exactly the field `XCross.xq_norm` / `xt_norm` (with `CJxq = Kx · CJq`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

theorem exists_Kx {η : ℝ} (CA : ℝ≥0∞) (hCA : CA ≠ ⊤) :
    ∃ Kx : ℝ, 1 ≤ Kx ∧ ∀ {CJ : ℝ}, 0 < CJ → glueConst η CA * ENNReal.ofReal CJ < ENNReal.ofReal (Kx * CJ) := by
  have hne := glueConst_ne_top η hCA
  obtain ⟨k, hk⟩ : ∃ k : ℝ, glueConst η CA = ENNReal.ofReal k ∧ 0 ≤ k :=
    ⟨(glueConst η CA).toReal, (ENNReal.ofReal_toReal hne).symm, ENNReal.toReal_nonneg⟩
  refine ⟨2 * max 1 k, ?_, fun {CJ} hCJ => ?_⟩
  · have := le_max_left 1 k; linarith
  · rw [hk.1, ← ENNReal.ofReal_mul hk.2]
    rw [ENNReal.ofReal_lt_ofReal_iff (by have := le_max_left 1 k; positivity)]
    have h2 := le_max_right 1 k
    have h3 := le_max_left 1 k
    nlinarith [mul_pos hCJ (by linarith : (0 : ℝ) < max 1 k)]

theorem crossBound_C_final {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) :
    ∃ Kx : ℝ, 1 ≤ Kx ∧ ∀ {q w w' L2 : ℕ}, L2 ≤ q → L2 ≤ w → w + 1 ≤ w' → ∀ {Jc : (Fin 2 → ℝ) → ℂ}, Continuous Jc →
      ∀ {CJ : ℝ}, XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) < ENNReal.ofReal CJ →
      XNorm00Restr (V := Unit) (1 - 2 * η) (timeBox (w' : ℝ) L2 ∪ timeBox (w : ℝ) L2) Set.univ
        (fun ts _ => clamp2J q Jc ts) < ENNReal.ofReal (Kx * CJ) := by
  obtain ⟨CA, hCA, hG⟩ := clampGlueC hη0 hη4
  obtain ⟨Kx, hKx, hK⟩ := exists_Kx (η := η) CA hCA
  refine ⟨Kx, hKx, fun {q w w' L2} hL2q hL2w hw {Jc} hJc {CJ} hJ => ?_⟩
  have hCJ : 0 < CJ := by
    by_contra h
    have : ENNReal.ofReal CJ = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 h)
    rw [this] at hJ
    exact absurd hJ (not_lt.2 zero_le)
  exact lt_of_le_of_lt (crossBound_C (by linarith) (by linarith) hη0.le hG hL2q hL2w hw hJc hCJ.le hJ.le) (hK hCJ)

theorem crossBound_T_final {η : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) :
    ∃ Kx : ℝ, 1 ≤ Kx ∧ ∀ {q w w' L2 : ℕ}, L2 ≤ q → L2 ≤ w → w + 1 ≤ w' → ∀ {Jc : (Fin 2 → ℝ) → ℂ}, Continuous Jc →
      ∀ {CJ : ℝ}, XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) < ENNReal.ofReal CJ →
      XNorm00Restr (V := Unit) (1 - 2 * η) (timeBoxGt (w' : ℝ) L2 ∪ timeBoxGt (w : ℝ) L2) Set.univ
        (fun ts _ => clamp2J q Jc ts) < ENNReal.ofReal (Kx * CJ) := by
  obtain ⟨CA, hCA, hG⟩ := clampGlueT hη0 hη4
  obtain ⟨Kx, hKx, hK⟩ := exists_Kx (η := η) CA hCA
  refine ⟨Kx, hKx, fun {q w w' L2} hL2q hL2w hw {Jc} hJc {CJ} hJ => ?_⟩
  have hCJ : 0 < CJ := by
    by_contra h
    have : ENNReal.ofReal CJ = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 h)
    rw [this] at hJ
    exact absurd hJ (not_lt.2 zero_le)
  exact lt_of_le_of_lt (crossBound_T (by linarith) (by linarith) hη0.le hG hL2q hL2w hw hJc hCJ.le hJ.le) (hK hCJ)

end WaveTurbulence.VineEstS5C.P4.W2.K2
