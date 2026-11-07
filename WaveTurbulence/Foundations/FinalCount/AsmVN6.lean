/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN5
public import WaveTurbulence.Foundations.FinalCount.AsmPhase3
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 6): the two `ι`-tests of a vine agree.**  For twin gaps (`pgap py = ± pgap px`) with
`‖pgap px‖ ≥ R/2`, a hit of `py` against the alive list extended by `px` gives a hit of `px` against the alive list
(`iotaHit_first_of_second`): the new element `px` itself gives `‖py ± px‖ ∈ {0, 2 ‖px‖}`, never in `(0, L^{-50η} R]`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {D₀ : Type u} {d : ℕ}

theorem iotaHit_first_of_second {L η : ℝ} (hL : 1 < L) (hη : 0 < η) {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    {alive : List (D₀ × D₀)} {px py : D₀ × D₀} {R : ℝ} (hR : 0 < R)
    (htwin : pgap L w κ py = pgap L w κ px ∨ pgap L w κ py = -pgap L w κ px) (hsim : R / 2 ≤ ‖pgap L w κ px‖)
    (h : IotaHit L η w κ (px :: alive) py R) : IotaHit L η w κ alive px R := by
  obtain ⟨q, hq, sg, hsg, h1, h2⟩ := h
  have hε : L ^ (-50 * η) * R < R := by
    have : L ^ (-50 * η) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)
    nlinarith
  rcases List.mem_cons.mp hq with rfl | hq'
  · exfalso
    set a := pgap L w κ q
    have hn : ‖pgap L w κ py + sg • a‖ = 0 ∨ ‖pgap L w κ py + sg • a‖ = 2 * ‖a‖ := by
      have h2a : ‖a + a‖ = 2 * ‖a‖ := by
        rw [← two_smul ℝ a, norm_smul]; norm_num
      have h2b : ‖-a + -a‖ = 2 * ‖a‖ := by
        rw [← neg_add, norm_neg, h2a]
      rcases htwin with e | e <;> rcases hsg with e2 | e2 <;> rw [e, e2]
      · right; simpa using h2a
      · left; simp
      · left; simp
      · right; simpa [sub_eq_add_neg] using h2b
    rcases hn with hn | hn
    · linarith
    · linarith
  · rcases htwin with e | e
    · refine ⟨q, hq', sg, hsg, ?_, ?_⟩
      · rw [e] at h1; exact h1
      · rw [e] at h2; exact h2
    · have key : ‖pgap L w κ py + sg • pgap L w κ q‖ = ‖pgap L w κ px + (-sg) • pgap L w κ q‖ := by
        rw [e, ← norm_neg]; congr 1; simp [neg_smul, add_comm]
      exact ⟨q, hq', -sg, by rcases hsg with rfl | rfl <;> simp, key ▸ h1, key ▸ h2⟩

end WaveTurbulence.FinalCountAsm
