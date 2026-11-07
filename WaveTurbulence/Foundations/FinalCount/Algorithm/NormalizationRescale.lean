/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentNormalization
import Mathlib.Tactic

/-! # Exact C-plus rescaling for the source circuit-rank normalization

Binary choices are exponential in the number of atoms. The source uses
C-plus to the circuit rank, so absorbing these choices requires this
actual rescaling identity and a separate rank/size comparison.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem linkNormalization_rescale (M : Molecule V D) (d : ℕ) (L γ δ Ca Cb : ℝ)
    (ha : Ca ≠ 0) (hb : Cb ≠ 0) (P : Finset V → ℝ) :
    linkNormalization M d L γ δ Cb P = (Ca/Cb)^M.circuitRank*linkNormalization M d L γ δ Ca P := by
  have he : Cb⁻¹*δ^(1/2 : ℝ) = (Ca/Cb)*(Ca⁻¹*δ^(1/2 : ℝ)) := by
    field_simp
  unfold linkNormalization
  rw [he,mul_zpow]
  ring

/-- The actual normalized count scales by the circuit rank, including
possible infinite raw counts and arbitrary admissibility constraints. -/
theorem linkCountA_rescale (M : Molecule V D) {d : ℕ} (L γ δ Ca Cb : ℝ)
    (ha : 0 < Ca) (hb : 0 < Cb) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    appbLinkCountA M L γ δ Cb w A P =
      ENNReal.ofReal ((Ca/Cb)^M.circuitRank)*appbLinkCountA M L γ δ Ca w A P := by
  change (appbCountE M L γ δ w A : ℝ≥0∞)*ENNReal.ofReal (linkNormalization M d L γ δ Cb P) =
    ENNReal.ofReal ((Ca/Cb)^M.circuitRank)*
      ((appbCountE M L γ δ w A : ℝ≥0∞)*ENNReal.ofReal (linkNormalization M d L γ δ Ca P))
  rw [linkNormalization_rescale M d L γ δ Ca Cb ha.ne' hb.ne' P,
    ENNReal.ofReal_mul (zpow_nonneg (div_pos ha hb).le _)]
  ring

end WaveTurbulence.Mole.AppbAlgorithm
