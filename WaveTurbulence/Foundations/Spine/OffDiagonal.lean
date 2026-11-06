/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.KernelMomentumSupport
/-! TARGET L769–770: the off-diagonal clause is a literal momentum-support consequence. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem truncSum_pair_off_diagonal (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (q N : ℕ) (t : ℝ) (n : Fin 2 → (Fin P.d → ℤ)) (hn : n 0 ≠ n 1) :
    truncSum P F q N t ![1, -1] n = 0 := by
  apply truncSum_eq_zero_of_momentum
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Units.val_one, Units.val_neg, one_smul, neg_smul,
    ← sub_eq_add_neg, sub_ne_zero] using hn

end WaveTurbulence.LGSpine
