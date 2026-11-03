/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.NearModes

/-!
# DH23 Lemma 6.5 (2): bounds for fixed `s`

For fixed `s` let `T(s) = ∑_{(g,h) ≠ 0} termBound(Lg + ξ + s b, Lh + ζ + s a)` (in `ℝ≥0∞`).

* `enorm_tsum_nonzero_le`: `|∑_{(g,h) ≠ 0} J_{g,h}(s)| ≤ C D λ^{2d} T(s)`, and `= 0` when
  `Φ(s, ·, ·) = 0` (in particular for `|s| > κL`);
* `nonzeroModes_le_full`: `T(s) ≤ C λ^{2d+2} ⟨s⟩^{-d}` for `|s| ≤ κL`;
* `nonzeroModes_le_split`: for `λ√d|s| ≤ L/8`, `T(s)` is at most the two far sums plus the two
  near sums.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- The majorant sum over the nonzero Poisson modes, for fixed `s`. -/
@[expose] def modeSum (d N : ℕ) (L lam s : ℝ) (a b ξ ζ : Mom d) : ℝ≥0∞ :=
  ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), {gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0}.indicator
    (fun gh => ENNReal.ofReal
      (termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a))) gh

theorem ntIntegral_eq_zero {lam : ℝ} {Φ : Mom d → Mom d → ℂ} (hΦ : ∀ x y, Φ x y = 0)
    (a b ξ ζ : Mom d) (s : ℝ) : ntIntegral lam Φ a b ξ ζ s = 0 := by
  simp [ntIntegral, hΦ]

theorem enorm_tsum_nonzero_le {N : ℕ} (hN : d + 1 ≤ N) {D L lam s : ℝ} {Φ : Mom d → Mom d → ℂ}
    (hΦ : NTBounds N D Φ) (hlam : 1 ≤ lam) (a b ξ ζ : Mom d) :
    ‖∑' gh : {gh : (Fin d → ℤ) × (Fin d → ℤ) // gh ≠ 0},
        ntIntegral lam Φ a b (L • intVec gh.1.1 + ξ) (L • intVec gh.1.2 + ζ) s‖ₑ ≤
      ENNReal.ofReal (termConst d N * D * lam ^ (2 * d)) * modeSum d N L lam s a b ξ ζ := by
  have hK : 0 ≤ termConst d N * D * lam ^ (2 * d) := by
    have := termConst_nonneg d N; have := hΦ.nonneg; have : 0 ≤ lam := by linarith
    positivity
  refine enorm_tsum_le_tsum_enorm.trans ?_
  rw [modeSum, ← tsum_subtype ({gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0}), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun gh => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (norm_ntIntegral_le hN hΦ hlam a b _ _ s)

theorem modeSum_le_full {N : ℕ} (hN : 2 * (d + 1) ≤ N) {L κ lam s : ℝ} (hL : 1 ≤ L)
    (hκ : 0 ≤ κ) (hs : |s| ≤ κ * L) (hlam : 1 ≤ lam) (a b ξ ζ : Mom d) :
    modeSum d N L lam s a b ξ ζ ≤
      ENNReal.ofReal (fullConst d κ * lam ^ (2 * (d + 1)) * ((1 + |s|) ^ d)⁻¹) := by
  obtain ⟨hsum, hle⟩ := summable_tsum_termBound_le hN hL hκ hs hlam a b ξ ζ
  calc modeSum d N L lam s a b ξ ζ
      ≤ ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), ENNReal.ofReal
          (termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a)) :=
        ENNReal.tsum_le_tsum fun gh => Set.indicator_le_self _ _ _
    _ = ENNReal.ofReal (∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
          termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => termBound_nonneg _ _ _ _ _ _) hsum).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

theorem termBound_comm (d N : ℕ) (lam s : ℝ) (P Q : Mom d) :
    termBound d N lam s P Q = termBound d N lam s Q P := by
  unfold termBound; rw [min_comm (decayW N _)]

/-- The near-mode sum of `P_g(s) = Lg + c + s v`. -/
@[expose] def nearSum (d N : ℕ) (L lam s : ℝ) (c v : Mom d) : ℝ≥0∞ :=
  ∑' g : Fin d → ℤ, {g : Fin d → ℤ | g ≠ 0 ∧ ‖(L • intVec g + c) + s • v‖ < L / 4}.indicator
    (fun g => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
      (decayW N (‖(L • intVec g + c) + s • v‖ - |s| * (lam * Real.sqrt d))))) g

/-- For `λ√d|s| ≤ L/8`, the mode sum is at most two far sums plus two near sums. -/
theorem modeSum_le_split {N : ℕ} (hN : 4 * (d + 1) ≤ N) {L κ lam s : ℝ} (hL : 1 ≤ L)
    (hκ : 0 ≤ κ) (hs : |s| ≤ κ * L) (hlam : 1 ≤ lam) (hρ : |s| * (lam * Real.sqrt d) ≤ L / 8)
    (a b ξ ζ : Mom d) :
    modeSum d N L lam s a b ξ ζ ≤
      2 * ENNReal.ofReal (farConst d κ * lam ^ (2 * (d + 1)) * (1 + |s|) / L ^ (d + 1)) +
        (nearSum d N L lam s ξ b + nearSum d N L lam s ζ a) := by
  have hL0 : 0 < L := by linarith
  set f : (Fin d → ℤ) × (Fin d → ℤ) → ℝ≥0∞ := fun gh => ENNReal.ofReal
    (termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a))
  set SP := {gh : (Fin d → ℤ) × (Fin d → ℤ) | L / 4 ≤ ‖(L • intVec gh.1 + ξ) + s • b‖}
  set SQ := {gh : (Fin d → ℤ) × (Fin d → ℤ) | L / 4 ≤ ‖(L • intVec gh.2 + ζ) + s • a‖}
  set SN := {gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0 ∧ ‖(L • intVec gh.1 + ξ) + s • b‖ < L / 4 ∧
    ‖(L • intVec gh.2 + ζ) + s • a‖ < L / 4}
  have hcover : ∀ gh, {gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0}.indicator f gh ≤
      SP.indicator f gh + SQ.indicator f gh + SN.indicator f gh := fun gh => by
    by_cases h0 : gh ∈ {gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0}
    · rw [Set.indicator_of_mem h0]
      by_cases hP : gh ∈ SP
      · rw [Set.indicator_of_mem hP]; exact le_self_add.trans le_self_add
      by_cases hQ : gh ∈ SQ
      · rw [Set.indicator_of_mem hQ]; exact le_add_self.trans le_self_add
      have hN' : gh ∈ SN := ⟨h0, not_le.1 hP, not_le.1 hQ⟩
      rw [Set.indicator_of_mem hN']; exact le_add_self
    · rw [Set.indicator_of_notMem h0]; exact bot_le
  have hfarP := tsum_far_le hN hL hκ hs hlam hρ a b ξ ζ
  have hfarQ : ∑' gh, SQ.indicator f gh ≤
      ENNReal.ofReal (farConst d κ * lam ^ (2 * (d + 1)) * (1 + |s|) / L ^ (d + 1)) := by
    have h := tsum_far_le hN hL hκ hs hlam hρ b a ζ ξ
    refine le_trans (le_of_eq ?_) h
    rw [← (Equiv.prodComm (Fin d → ℤ) (Fin d → ℤ)).tsum_eq]
    refine tsum_congr fun gh => ?_
    simp only [SQ, f, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Set.indicator_apply,
      Set.mem_ofPred_eq]
    rw [termBound_comm]
  have hnear := tsum_nearPair_le (N := N) (lam := lam) (s := s) hL0 a b ξ ζ
  calc modeSum d N L lam s a b ξ ζ
      = ∑' gh, {gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0}.indicator f gh := rfl
    _ ≤ ∑' gh, (SP.indicator f gh + SQ.indicator f gh + SN.indicator f gh) :=
        ENNReal.tsum_le_tsum hcover
    _ = (∑' gh, SP.indicator f gh) + (∑' gh, SQ.indicator f gh) + ∑' gh, SN.indicator f gh := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal (farConst d κ * lam ^ (2 * (d + 1)) * (1 + |s|) / L ^ (d + 1)) +
          ENNReal.ofReal (farConst d κ * lam ^ (2 * (d + 1)) * (1 + |s|) / L ^ (d + 1)) +
          (nearSum d N L lam s ξ b + nearSum d N L lam s ζ a) :=
        add_le_add (add_le_add hfarP hfarQ) hnear
    _ = _ := by ring

end WaveTurbulence.NTSP
