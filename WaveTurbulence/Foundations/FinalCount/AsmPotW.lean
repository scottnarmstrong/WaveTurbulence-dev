/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2d
/-! **FINALCOUNT-ASSEMBLY: the potential and the per-step inequality.**
`potR y h = y · L^{-aF(h)+bVβ(h)} / Ap(h)` (`a = 2γ₀+5η²`, `b = γ₀+2η²`; `y` is the `ρ`/critical/`p⁺` factor, supplied by the caller).
`pot_step`: `N · (C · stepRHS h h') · potR y' h' ≤ potR y h` as soon as `N · C · L^{-η³} · y' ≤ y`.  This is the arithmetic of `hW` of the
phase cover theorems. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The potential of a state with the extra factor `y`. -/
noncomputable def potR (L γ η : ℝ) (y : ℝ) (h : HSt V D₀) : ℝ :=
  y * L ^ (-(2 * min γ (1 - γ) + 5 * η ^ 2) * (h.s.M.numComponents : ℝ) + (min γ (1 - γ) + 2 * η ^ 2) * (vBeta h.s : ℝ)) /
    apProd L γ η h.s

theorem stepRHS_mul_potR {L γ η : ℝ} (hL : 0 < L) {h h' : HSt V D₀} (hAp : 0 < apProd L γ η h.s) (hAp' : 0 < apProd L γ η h'.s)
    (y' : ℝ) :
    stepRHS L γ η h h' * potR L γ η y' h' = L ^ (-η ^ 3) * y' * (potR L γ η 1 h) := by
  unfold stepRHS potR
  have e : ∀ x y : ℝ, L ^ x * L ^ y = L ^ (x + y) := fun x y => (Real.rpow_add hL x y).symm
  set a := 2 * min γ (1 - γ) + 5 * η ^ 2
  set b := min γ (1 - γ) + 2 * η ^ 2
  have h1 : L ^ (a * ((h'.s.M.numComponents : ℝ) - h.s.M.numComponents) - b * ((vBeta h'.s : ℝ) - vBeta h.s)) *
      L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ)) =
      L ^ (-a * (h.s.M.numComponents : ℝ) + b * (vBeta h.s : ℝ)) := by
    rw [e]; congr 1; ring
  have hAp0 := hAp.ne'
  have hAp0' := hAp'.ne'
  calc _ = L ^ (-η ^ 3) * L ^ (a * ((h'.s.M.numComponents : ℝ) - h.s.M.numComponents) - b * ((vBeta h'.s : ℝ) - vBeta h.s)) *
        (L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ))) * y' * (apProd L γ η h'.s / (apProd L γ η h.s * apProd L γ η h'.s)) := by
        field_simp
    _ = L ^ (-η ^ 3) * y' * ((L ^ (a * ((h'.s.M.numComponents : ℝ) - h.s.M.numComponents) - b * ((vBeta h'.s : ℝ) - vBeta h.s)) *
        L ^ (-a * (h'.s.M.numComponents : ℝ) + b * (vBeta h'.s : ℝ))) / apProd L γ η h.s) := by
        field_simp
    _ = _ := by rw [h1]; ring

/-- **The per-step inequality of the cover theorems**, in `ℝ≥0∞`. -/
theorem pot_step {L γ η : ℝ} (hL : 0 < L) {h h' : HSt V D₀} (hAp : 0 < apProd L γ η h.s) (hAp' : 0 < apProd L γ η h'.s)
    (y y' C : ℝ) (N : ℕ) (hC : 0 ≤ C) (hy' : 0 ≤ y') (hyy : (N : ℝ) * C * L ^ (-η ^ 3) * y' ≤ y) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (C * stepRHS L γ η h h') * ENNReal.ofReal (potR L γ η y' h')) ≤
      ENNReal.ofReal (potR L γ η y h) := by
  have hpos : 0 ≤ potR L γ η 1 h := by
    unfold potR
    exact div_nonneg (by positivity) hAp.le
  have hX : 0 ≤ stepRHS L γ η h h' := by
    unfold stepRHS; positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have key := stepRHS_mul_potR hL hAp hAp' y'
  have hpy : potR L γ η y h = y * potR L γ η 1 h := by unfold potR; ring
  rw [hpy]
  calc (N : ℝ) * (C * stepRHS L γ η h h' * potR L γ η y' h') = N * C * (stepRHS L γ η h h' * potR L γ η y' h') := by ring
    _ = N * C * (L ^ (-η ^ 3) * y' * potR L γ η 1 h) := by rw [key]
    _ = (N * C * L ^ (-η ^ 3) * y') * potR L γ η 1 h := by ring
    _ ≤ y * potR L γ η 1 h := mul_le_mul_of_nonneg_right hyy hpos


/-- **The `y`-factor of the per-step inequality**: if a step lowers the exponent `g` by at most `δg` and `N · C ≤ L^{η³ - δg}`,
then `N · C · L^{-η³} · (Y₀ L^{-g'}) ≤ Y₀ L^{-g}`. -/
theorem yy_of {L η : ℝ} (hL : 1 ≤ L) {Y0 : ℝ} (hY0 : 0 ≤ Y0) {g g' δg : ℝ} (hg : g - δg ≤ g') {N C : ℝ} (hN : 0 ≤ N)
    (hC : 0 ≤ C) (hNC : N * C ≤ L ^ (η ^ 3 - δg)) :
    N * C * L ^ (-η ^ 3) * (Y0 * L ^ (-g')) ≤ Y0 * L ^ (-g) := by
  have hL0 : 0 < L := by linarith
  have h1 : L ^ (-g') ≤ L ^ (-g + δg) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h2 : L ^ (-η ^ 3) * L ^ (-g + δg) * L ^ (η ^ 3 - δg) = L ^ (-g) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
  have hpos : 0 ≤ L ^ (-η ^ 3) := by positivity
  calc N * C * L ^ (-η ^ 3) * (Y0 * L ^ (-g')) = (N * C) * (L ^ (-η ^ 3) * Y0 * L ^ (-g')) := by ring
    _ ≤ (L ^ (η ^ 3 - δg)) * (L ^ (-η ^ 3) * Y0 * L ^ (-g + δg)) := by
        gcongr
    _ = Y0 * (L ^ (-η ^ 3) * L ^ (-g + δg) * L ^ (η ^ 3 - δg)) := by ring
    _ = Y0 * L ^ (-g) := by rw [h2]


/-- The potential used by the cover theorems: `Y₀ L^{-g(h)}` times `potR`'s state part. -/
noncomputable def WPot (L γ η Y0 : ℝ) (g : HSt V D₀ → ℝ) (h : HSt V D₀) : ℝ≥0∞ :=
  ENNReal.ofReal (potR L γ η (Y0 * L ^ (-g h)) h)

/-- **Generic `hW`**: a step whose exponent `g` drops by at most `δg`, with `N · C ≤ L^{η³ - δg}`. -/
theorem hW_generic {L γ η : ℝ} (hL1 : 1 ≤ L) {h h' : HSt V D₀} (hAp : 0 < apProd L γ η h.s) (hAp' : 0 < apProd L γ η h'.s)
    {Y0 : ℝ} (hY0 : 0 ≤ Y0) (g : HSt V D₀ → ℝ) {δg : ℝ} (hg : g h - δg ≤ g h') (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hNC : (N : ℝ) * C ≤ L ^ (η ^ 3 - δg)) :
    (N : ℝ≥0∞) * (ENNReal.ofReal (C * stepRHS L γ η h h') * WPot L γ η Y0 g h') ≤ WPot L γ η Y0 g h := by
  have hL : 0 < L := by linarith
  unfold WPot
  refine pot_step hL hAp hAp' _ _ C N hC (by positivity) ?_
  exact yy_of hL1 hY0 hg (by positivity) hC hNC

end WaveTurbulence.FinalCountAsm
