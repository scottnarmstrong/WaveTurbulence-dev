/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.TranslatedLatticeBound
public import Mathlib.Data.Int.Interval

/-! # Finite lattice support from a geometric coordinate box -/

public section
namespace WaveTurbulence.WeylSums

/-- Sampling a bounded joint cutoff gives finite lattice support, uniformly
in its real center. No smoothness is needed for this elementary fact. -/
theorem finite_lattice_sample_of_box {m : ℕ}
    (χ : EuclideanSpace ℝ (Fin m) → ℂ) (R : ℝ)
    (hbox : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ R)
    {L : ℝ} (hL : 0 < L) (c : EuclideanSpace ℝ (Fin m)) :
    {n : Fin m → ℤ | χ (WithLp.toLp 2 (fun i => (n i : ℝ)/L)-c) ≠ 0}.Finite := by
  classical
  refine (Fintype.piFinset (fun i : Fin m => Finset.Icc ⌊L*(c i-R)⌋ ⌈L*(c i+R)⌉)).finite_toSet.subset ?_
  intro n hn
  have hx (i : Fin m) : |(n i : ℝ)/L-c i| ≤ R := hbox _ hn i
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  constructor
  ·
    have hh := (abs_le.mp (hx i)).1
    have hlo : L*(c i-R) ≤ (n i : ℝ) := by
      have := (le_div_iff₀ hL).mp (show c i-R ≤ (n i : ℝ)/L by linarith only [hh])
      linarith only [this]
    exact Int.cast_le.mp ((Int.floor_le _).trans hlo)
  ·
    have hh := (abs_le.mp (hx i)).2
    have hsum : (n i : ℝ)/L ≤ c i+R := by linarith only [hh]
    have hhi : (n i : ℝ) ≤ L*(c i+R) := by
      simpa only [mul_comm] using (div_le_iff₀ hL).mp hsum
    exact (Int.cast_le.mp (hhi.trans (Int.le_ceil _)))

end WaveTurbulence.WeylSums
