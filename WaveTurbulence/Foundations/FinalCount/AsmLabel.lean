/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3State
/-! **FINALCOUNT-ASSEMBLY, M7: dyadic labels exist.**  A nonzero lattice gap `r` with `‖r‖ ≤ L^{-γ+η}` has a label `R = 2^z`
(`IsLabel`) with `GapSim`: `R/2 ≤ ‖r‖ ≤ 2R`, provided `2/L ≤ L^{-γ+η}` (i.e. `L^{1-γ+η} ≥ 2`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

theorem exists_label {L γ η r : ℝ} (hr0 : 1 / L ≤ r) (hrU : r ≤ L ^ (-γ + η)) (hL : 0 < L)
    (h2 : 2 / L ≤ L ^ (-γ + η)) :
    ∃ R, IsLabel L γ η R ∧ R / 2 ≤ r ∧ r ≤ 2 * R := by
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr0
  obtain ⟨z, hz1, hz2⟩ := exists_mem_Ico_zpow hrpos (by norm_num : (1 : ℝ) < 2)
  have hR1 : (0 : ℝ) < 2 ^ z := zpow_pos (by norm_num) z
  have hz2' : r < 2 * 2 ^ z := by rw [zpow_add_one₀ (by norm_num)] at hz2; linarith
  by_cases hc : 1 / L ≤ 2 ^ z
  · refine ⟨2 ^ z, ⟨⟨z, rfl⟩, by simpa [one_div] using hc, hz1.trans hrU⟩, by linarith, by linarith⟩
  · push Not at hc
    have hR : (2 : ℝ) * 2 ^ z = 2 ^ (z + 1) := by rw [zpow_add_one₀ (by norm_num)]; ring
    refine ⟨2 * 2 ^ z, ⟨⟨z + 1, hR⟩, ?_, ?_⟩, by linarith, by linarith⟩
    · rw [inv_eq_one_div]; linarith
    · have : 2 * (2 : ℝ) ^ z ≤ 2 / L := by
        have := mul_le_mul_of_nonneg_left hc.le (by norm_num : (0 : ℝ) ≤ 2)
        simpa [div_eq_mul_inv] using this
      linarith

theorem gapAt_lattice {d : ℕ} (L : ℝ) (w : Mom d) {D : Type*} (κ : D → (Fin d → ℤ)) (x y : D) :
    Molecule.gapAt L w κ x y = latticePoint L (κ x - κ y) := by
  unfold Molecule.gapAt Molecule.kvec latticePoint
  ext j
  simp [sub_div]

theorem lattice_norm_ge {d : ℕ} {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) (hn : n ≠ 0) :
    1 / L ≤ ‖latticePoint L n‖ := by
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h; push Not at h; exact hn (funext h)
  have h1 : |(latticePoint L n) j| ≤ ‖latticePoint L n‖ := by
    have := PiLp.norm_apply_le (latticePoint L n) j
    simpa using this
  have h2 : (latticePoint L n) j = (n j : ℝ) / L := rfl
  have h3 : (1 : ℝ) ≤ |(n j : ℝ)| := by
    have : (1 : ℤ) ≤ |n j| := Int.one_le_abs hj
    exact_mod_cast this
  calc 1 / L ≤ |(n j : ℝ)| / L := by gcongr
    _ = |(latticePoint L n) j| := by rw [h2, abs_div, abs_of_pos hL]
    _ ≤ _ := h1

/-- For an SG gap in a lattice decoration. -/
theorem exists_label_of_SG {d : ℕ} {L γ η : ℝ} (w : Mom d) {D : Type*} (κ : D → (Fin d → ℤ)) (x y : D)
    (hL : 0 < L) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG) :
    ∃ R, IsLabel L γ η R ∧ GapSim L w κ x y R := by
  have hne : Molecule.gapAt L w κ x y ≠ 0 := by
    intro h; unfold Molecule.gapKind at hsg; simp [h] at hsg
  have hU : ‖Molecule.gapAt L w κ x y‖ ≤ L ^ (-γ + η) := by
    unfold Molecule.gapKind at hsg
    by_contra hc
    simp [hne, hc] at hsg
  have hlow : 1 / L ≤ ‖Molecule.gapAt L w κ x y‖ := by
    rw [gapAt_lattice] at hne ⊢
    refine lattice_norm_ge hL _ ?_
    intro h; apply hne; rw [h]; simp [latticePoint]; rfl
  obtain ⟨R, hR, h1, h2'⟩ := exists_label hlow hU hL h2
  exact ⟨R, hR, h1, h2'⟩

end WaveTurbulence.FinalCountAsm
