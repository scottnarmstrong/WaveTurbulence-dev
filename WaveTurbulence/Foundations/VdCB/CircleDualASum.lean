/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleDualTower
public import WaveTurbulence.Foundations.NumberTheory.CircleDualAScale

/-!
# The actual circle dual A-process estimate

The literal calculus tower discharges every derivative premise of the
landed A-process theorem. The conclusion concerns the actual corrected
lattice dual, uniformly in arbitrary additional real linear phases.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The pure `(1/30,26/30)` derivative estimate for the actual corrected
circle dual, with no assumed derivative formulas or sum bounds. -/
theorem norm_sum_circleLatticeDualPhase_add_linear_le (a : ℤ) (N : ℕ) (p q : ℝ)
    {R h Y : ℝ} (hR : 0 < R) (hh : 0 < h) (hY : 1 ≤ Y) (hhY : h ≤ Y)
    (hRY : Y ^ 2 ≤ R * h ^ 2) (ha : Y ≤ (a : ℝ) + 1)
    (hb : (a : ℝ) + N + 2 ≤ 4 * Y) (hNY : (N : ℝ) ≤ 2 * Y) :
    ‖∑ n ∈ Finset.Ioc a (a + N), expPhase (circleLatticeDualPhase R h n + p * (n : ℝ) + q)‖ ≤
      17179869184 * ((R * h ^ 2 / Y ^ 2) ^ ((1 : ℝ) / 30) * Y ^ ((26 : ℝ) / 30)) := by
  have he := circle_dual_exp_sum_le_of_derivative_formulas (circleDualTower R h) a N (R + p) q
    hR hh hY hhY hRY ha hb hNY
    (fun r _ x _ => hasDerivAt_circleDualTower R hh r x)
    (fun x _ => circleDualTower_three_quotient R hh x)
    (fun x _ => circleDualTower_four_quotient R hh x)
    (fun x _ => circleDualTower_five_quotient R hh x)
  convert he using 1
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  simp only [circleDualTower, iteratedDeriv_zero, circleLatticeDualPhase]
  ring

end WaveTurbulence.VdCB
