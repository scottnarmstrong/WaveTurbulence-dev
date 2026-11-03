/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.SimplexVolume
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The two-chain factorial gain

Two monotone chains lose at most `2^z` compared with a single chain on `z`
coordinates. This is the harmless exponential factor absorbed at TARGET
L2032–2036.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- The two-chain factorial denominator is within `2^{m+n}` of the
one-chain denominator. -/
theorem two_chain_factorial_bound {D : ℝ} (hD : 0 ≤ D) (m n : ℕ) :
    D ^ (m + n) / ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ)) ≤
      2 ^ (m + n) * (D ^ (m + n) / (Nat.factorial (m + n) : ℝ)) := by
  have hf : ((m + n).choose m : ℝ) * (Nat.factorial m : ℝ) * (Nat.factorial n : ℝ) =
      (Nat.factorial (m + n) : ℝ) := by
    have hh := Nat.add_choose_mul_factorial_mul_factorial m n
    rw [← Nat.choose_symm_add] at hh
    exact_mod_cast hh
  have heq : D ^ (m + n) / ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ)) =
      ((m + n).choose m : ℝ) * (D ^ (m + n) / (Nat.factorial (m + n) : ℝ)) := by
    field_simp
    nlinarith only [congrArg (fun v : ℝ => D ^ (m + n) * v) hf]
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_two_pow (m + n) m

/-- Volume bound for two interleaved chains, with the exponential loss
explicit. Coordinate interleavings preserve Lebesgue measure. -/
theorem volume_two_orderedSimplex_le (m n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    volume ((orderedSimplex m D) ×ˢ (orderedSimplex n D)) ≤
      ENNReal.ofReal (2 ^ (m + n) * (D ^ (m + n) / (Nat.factorial (m + n) : ℝ))) := by
  rw [volume_two_orderedSimplex m n hD]
  exact ENNReal.ofReal_le_ofReal (two_chain_factorial_bound hD m n)

/-- Two chains in an arbitrarily interleaved labelling of `m+n` coordinates.
The equivalence `e` assigns every original label to a place in one chain. -/
@[expose] def interleavedTwoChains {m n : ℕ}
    (e : Fin (m + n) ≃ (Fin m ⊕ Fin n)) (D : ℝ) : Set (Fin (m + n) → ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin m ⊕ Fin n => ℝ) e).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ))) ⁻¹'
      ((orderedSimplex m D) ×ˢ (orderedSimplex n D))

/-- Exact volume of two interleaved monotone chains. -/
theorem volume_interleavedTwoChains {m n : ℕ}
    (e : Fin (m + n) ≃ (Fin m ⊕ Fin n)) {D : ℝ} (hD : 0 ≤ D) :
    volume (interleavedTwoChains e D) =
      ENNReal.ofReal (D ^ (m + n) / ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) := by
  have hm := (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin m ⊕ Fin n => ℝ) e)
  rw [interleavedTwoChains, MeasurableEquiv.coe_trans, hm.measure_preimage
    ((measurableSet_orderedSimplex m D).prod (measurableSet_orderedSimplex n D)).nullMeasurableSet]
  exact volume_two_orderedSimplex m n hD

end WaveTurbulence.Analysis
