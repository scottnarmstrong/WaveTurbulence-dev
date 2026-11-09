/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleSum
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.FlowerKind
public import WaveTurbulence.Frozen.Defs.FlowerSumP
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.InstDecidableEqFixPat
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.TreeKind
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefixP
public import WaveTurbulence.Provider.LayergardenFlowerV4

/-!
# layergardenFlower

Wave B tier B1 (WaveB1-Flower.lean), source: T Prop `flowerest1`, L2279–L2305; T L2306–L2338; WAVE-B v2 §4.15; T L2280; T (flowerest2); T (newnormn); T L2331; T L2312; T L2290. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); full-range successor `layergardenFlower_v4` frozen by ruling D16 (`docs/DECISIONS.md#D16`); do not edit.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
open Classical in
/-- **Versioned successor (ruling D16, GAMMA-HALF extension): the full range `0 < γ < 1`.**
`layergardenFlower_v3` with the hypothesis `1 / 2 < P.γ →` removed; nothing else in the statement changes (same
binders, definitions and conclusion; `flowerSumP` as in D13; only the provider import differs). For `0 < γ ≤ 1/2`
the proof uses the enlarged vine family (T-vines, `docs/DECISIONS.md#D11`). `layergardenFlower_v1`/`_v2`
(max-form cutoffs, E34) and `_v3` stay frozen.

**Inherited from v3 (ruling D13).** The `M₁`, `M₂` cutoff weights are TARGET's smooth cutoffs in DH21's
product form (`prodDyadicCut`); `cutWeight1`/`cutWeight2` (`φ` of a maximum) are not smooth and do not factor
through the regular-object reduction. Clauses without cutoffs are unchanged (`flowerSumP` agrees with
`flowerSum` there by `rfl`). `layergardenFlower_v2` stays frozen and open.

**B1.12 `layergardenFlower`** (T Prop `flowerest1`, L2279–L2305, deterministic core; T L2306–L2338 for
its uses; review G-1, stage-3 R8, WAVE-B v2 §4.15).

Setting: `(Π_P)`, `0 ≤ p < 𝔇`, remainders as in B1.2, inputs `F_q = φ(δq) + R_q`.

**(1) Flower gardens of width `2P`.** For `p < s < t < p+1` (T's range for the flower kernels, L2263),
`n, n' ∈ ℤ^d`, `ζ`, `N ≤ N_{p+1}^4`, every kind (`𝒳`, `𝒴`, `𝒲`), every pattern vector, with or without `†`
and the cutoffs:

  `|flowerSum| ≤ ⟨k − ζk'⟩^{−4Λ_{p+1}P} L^{c(100d)³P} δ^{2νN} · M₁^{−80dP} · M₂^{−P/9}`

- `c = 1` if all patterns are plain, `c = 2` otherwise.
- The `M₁` factor is present iff the `M₁` cutoff is, also for derivative patterns.
- The `M₂` factor is present iff the `M₂` cutoff is and all patterns are plain. The `M₂` cutoff requires the
  `M₁` cutoff and `|k| ≥ M₁^{10}`.

**(2) Couples.** For `p < t < p+1`, `k ∈ ℝ^d`, `N ≤ N_{p+1}^4`, kind `ℒ₀`, or kind `a^tr` with `∂_t`:

  `|coupleSum| ≤ ⟨k⟩^{−4Λ_{p+1}} L^{100d} δ^{νN}`

**Uses.**
- The `𝒴`/`𝒲` gain `e^{−100N_{p+1}}` (T L2280) comes from summing over `N ≥ 2P(N_{p+1}+1)`, the kinds'
  lower bound.
- The bounds of (1) give T (flowerest2) with its cutoff variants, and T (newnormn) with the `∂_{t,s}` terms
  of (sobolev2), T L2331.
- Those of (2) give (trterm1) for `ℒ₀`, and for `∂_t a^tr`, `∂_t ℒ₀` with an extra `L^{100d}` (T L2312).

**Deviations** (FLOWER-DESIGN.md):
- (D1) The moment expansions `𝔼_p|𝒦|^{2P} = ∑ + errors` are left to T.flowerest1 and T.fp.part1. This gate
  is their deterministic core.
- (D2) Per-order bounds with `δ^{2νN}` (flowers) and `δ^{νN}` (couples).
- (D3) Range `N ≤ N_{p+1}^4` (T L2290).
- (D4) Prefactor `L^{d−γ}` (F25).
- (D5) Kind `𝒳` excludes the trivial flower tree (F39).
- (D6) `𝒴`/`𝒲` replace the top bound (F46).
- (D7) Explicit dyadic cutoffs, in DH21's product form (`prodDyadicCut`; D13).
- (D8) The derivative patterns and `†` as designated nodes, removed phases and weights (R8).
- (D9) `L^{2(100d)³P}` for derivative patterns.
- (D10) The couple clause covers `ℒ₀`, which B1.2 does not.
- (D11) Per-tree choices: the `†` labels `c j` and the patterns `pat j` may differ between the trees `j` of
  the garden. The consumer uses one uniform choice, so this is more general than `fixedpoint` needs (the
  proof is per tree). -/
theorem layergardenFlower_v4 : WTPrefixP fun Pm P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSumP P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.layergardenFlower_v4
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
