/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PairCoordinates
public import WaveTurbulence.Foundations.NTSP.FullSum
import Mathlib.Tactic

/-!
# Integer dual coordinates for the bilinear Poisson sum

The exact two-block lattice bijection aligns the absolutely convergent
Fourier samples with the arbitrary frequency shifts in `lemlayer1`.
-/

public section

namespace WaveTurbulence.Sumint

/-- Pack two integer vectors into the flattened integer lattice. -/
@[expose] noncomputable def pairIntegerEquiv (d : ℕ) :
    ((Fin d → ℤ) × (Fin d → ℤ)) ≃ (Fin (2*d) → ℤ) :=
  (finTwoArrowEquiv (Fin d → ℤ)).symm.trans (Fourier.flattenIntegerBlocks 2 d)

/-- The first flattened dual block has exactly the frequency scale `L`. -/
theorem flatMomentum_integer_zero {d : ℕ} (L : ℝ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    flatMomentum 0 (fun k => L * (pairIntegerEquiv d p k : ℝ)) = L • NTSP.intVec p.1 := by
  ext j
  simp [flatMomentum, pairIntegerEquiv, Fourier.flattenIntegerBlocks_apply, NTSP.intVec]

/-- The second flattened dual block has exactly the same frequency scale. -/
theorem flatMomentum_integer_one {d : ℕ} (L : ℝ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    flatMomentum 1 (fun k => L * (pairIntegerEquiv d p k : ℝ)) = L • NTSP.intVec p.2 := by
  ext j
  simp [flatMomentum, pairIntegerEquiv, Fourier.flattenIntegerBlocks_apply, NTSP.intVec]

/-- Reflection of integer indices reflects the literal dual vector. -/
theorem ntsp_intVec_neg {d : ℕ} (n : Fin d → ℤ) : NTSP.intVec (-n) = -NTSP.intVec n := by
  ext j
  simp [NTSP.intVec]

end WaveTurbulence.Sumint
