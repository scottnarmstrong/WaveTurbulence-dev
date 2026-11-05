/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
/-! Compact unit-ball momentum restrictions give genuinely finite lattice-label carriers. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem finite_coset_unit_ball {d : ℕ} {L : ℝ} (hL : 0 < L) (base center : Mom d) :
    {n : Fin d → ℤ | ‖base + latticePoint L n - center‖ ≤ 1}.Finite := by
  refine (Set.finite_Icc (fun j => ⌊L * (center j - base j - 1)⌋)
    (fun j => ⌈L * (center j - base j + 1)⌉)).subset ?_
  intro n hn
  have hj (j : Fin d) : |base j + (n j : ℝ) / L - center j| ≤ 1 := by
    have hh := (PiLp.norm_apply_le (base + latticePoint L n - center) j).trans hn
    simpa only [PiLp.sub_apply, PiLp.add_apply, latticePoint, Real.norm_eq_abs] using hh
  constructor
  · intro j
    have hh := (abs_le.mp (hj j)).1
    apply Int.floor_le_iff.mpr
    have hg : L * (center j - base j - 1) ≤ (n j : ℝ) := by
      rw [mul_comm L]
      apply (le_div_iff₀ hL).mp
      linarith
    exact_mod_cast (by linarith : L * (center j - base j - 1) < (n j : ℝ) + 1)
  · intro j
    have hh := (abs_le.mp (hj j)).2
    apply Int.le_ceil_iff.mpr
    have hg : (n j : ℝ) ≤ L * (center j - base j + 1) := by
      rw [mul_comm L]
      apply (div_le_iff₀ hL).mp
      linarith
    exact_mod_cast (by linarith : (n j : ℝ) - 1 < L * (center j - base j + 1))

end WaveTurbulence.LGSpine
