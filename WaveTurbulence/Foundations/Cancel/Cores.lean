/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.L1
public import WaveTurbulence.Foundations.ClassJR.MCChainT

/-!
# Regularizing one variable through Volterra operators (DH21 §7.1)

The proofs of DH21 Lemmas 7.1 and 7.3 fix all variables but one, `x = α_j`, and compute
`[G]∫ K(x) dx = lim_{θ→0} ∫ K(x) e^{-πθ²x²} dx` (DH21 (gausspv)). Here `K(x)` is a Volterra chain in
which `x` enters a single factor. `RegTo Φ Ψ` records that the Gaussian regularization in `x` of a
family of time functions `z ↦ Φ x z` converges to `Ψ z` on `[0,1]`. It also records the bounds
that carry this through further Volterra operators.

* `RegTo.volterra_left`: a fixed Volterra operator on the left preserves `RegTo`.
* `RegTo.of_kernel`: a factor `volterra (M x) g` whose regularized kernel converges.
* `regTo_tr58`: the adjacent-pair core (DH21 Lemma 7.3). The regularized
  `𝒥_{α,μ} + ℛ_{α,μ} = I_{εα}I_{μ-εα} - Φ(εα)𝒥_{α[ ],μ}` tends to `+I_μ`. Since `𝒥_{α[ ],μ} = -I_μ`
  (F61), the integral over `α` of the `j ∉ Z` piece is minus the `j ∈ Z` piece.
* `regTo_sand`: the non-adjacent-pair core (DH21 Lemma 7.1). The regularized sandwich
  `I_{εα} T I_{μ-εα}` tends to `0`.
* `RegTo.integral_eq`: if the section is integrable, its integral is the limit.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

theorem eventually_pos_nhdsGT : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin

/-! ### The two cores -/

/-! ### Peeling one variable -/

section Peel

variable {V : Type*} [DecidableEq V]

end Peel

end WaveTurbulence.Cancel
