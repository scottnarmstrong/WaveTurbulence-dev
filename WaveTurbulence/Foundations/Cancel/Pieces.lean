/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Reg
public import WaveTurbulence.Foundations.ClassJR.Chain2

/-!
# The regularized pair pieces and sandwiches (DH21 Lemmas 7.1, 7.3)

The variable `α_j` of a pair of a regular chain enters DH21 Lemma 5.10's operators in two shapes:

* an adjacent pair `{a, a+1}` gives `I_{εα} I_{μ-εα} = Φ(εα) 𝒥_{α[ ],μ} + (𝒥_{α,μ} + ℛ_{α,μ})` (DH21 Lemma 5.8),
  with `𝒥_{α[ ],μ} = -I_μ`. Its `α`-dependent part is `tr58K ε μ x = I_{εx}I_{μ-εx} + Φ(εx) I_μ`
  (`ClassJR.TR58`).
* a non-adjacent pair encloses an operator `T` in a sandwich `I_{εα} T I_{μ-εα}` (`ClassJR.sandw`).

Regularizing in `x = α`:

* `greg_tr58K`: `greg θ (x ↦ tr58K ε μ x t s) = e^{πiμs} GI θ (t-s)` with `GI θ u = ∫_0^u gk θ → 1`. So
  `[G]∫ (𝒥 + ℛ) dα = I_μ` (DH21 Lemma 7.3; `Φ` is odd and drops out).
* `greg_sandK`: the sandwich regularizes to `e^{πiμs} ∫_s^t gk θ(y-s) H(y,s) dy` with
  `H(y,s) = ∫_s^y T(y,z) dz`, which tends to `H(s,s) = 0` (`tendsto_greg_sandK`; DH21 Lemma 7.1).

`kcomp_assoc` (associativity of Volterra kernel composition) writes the sandwich in the right-associated form.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR WaveTurbulence.Fourier

/-! ### Associativity -/

/-! ### Elementary kernels -/

theorem norm_cexp_piI (r : ℝ) : ‖cexp (π * I * r)‖ = 1 := by
  rw [show (π : ℂ) * I * r = ((π * r : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-! ### The cumulative kernel `GI θ u = ∫_0^u gk θ` -/

/-! ### Adjacent pairs: `I_{εx} I_{μ-εx}` and Lemma 5.8's `𝒥 + ℛ` -/

/-- `Φ` is odd. -/
theorem phiR_neg (y : ℝ) : phiR (-y) = -phiR y := by
  unfold phiR chiInvR chiInfinity
  rw [chi0_even]
  push_cast
  ring

theorem norm_phiR_le (y : ℝ) : ‖phiR y‖ ≤ CPhi := by
  unfold phiR
  have hπ : ‖(π : ℂ)‖ = π := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, hπ]
  calc ‖(chiInvR y : ℂ)‖ / π ≤ ‖(chiInvR y : ℂ)‖ / 1 :=
        div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one (by linarith [Real.two_le_pi])
    _ ≤ CPhi := by rw [div_one]; exact norm_chiInvR_le y

/-! ### Non-adjacent pairs: the sandwich `I_{εx} T I_{μ-εx}` -/

end WaveTurbulence.Cancel
