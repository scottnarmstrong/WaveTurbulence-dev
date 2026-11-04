/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.InitialCoeff
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.IsASolution
public import WaveTurbulence.Frozen.Defs.IsSymmetricEvent
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.JointCumulant
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.TruncSum
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTParamsR
public import WaveTurbulence.Frozen.Defs.WTParamsTheta
public import WaveTurbulence.Frozen.Defs.ZpowSign

/-!
# AnsatzAt

Wave B tier B1 (WaveB1-System.lean), source: T Prop `propansatz`; WAVE-B §2.6.7; WAVE-B §5. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **The ansatz at level `p`** (T Prop `propansatz` (1)–(4); WAVE-B §2.6.7 and §4.1), for the
probability data `(Ω, μ, g)`, the solution `a`, events `Fev`, the two-point corrections `R, E` and
the cumulant remainders `Et`. Items:
1. `Fev p` is measurable and symmetric, `Fev p ⊆ Fev (p-1)`, `P(Fev p) ≥ 1 - e^{-N_p}`; on `Fev p`
   the classed solution exists on `[0, p]` with data `û_in` and is unique in the class; every
   `a_n(t)` (`t ∈ [0,p]`) is measurable (review C1) and every product of them is integrable on `Fev p`
   (WAVE-B §5);
2. `R p` is real with `‖R p‖_{𝔖^{Λ_p,Λ_p}} ≤ L^{-θ_p}` (hence `C^{Λ_p}`, the regularity TARGET
   tracks; no separate smoothness conjunct: `ContDiff ℝ ⊤` would be real-analyticity, stage-3 R1,
   stage-2 R4), `|E p n| ≤ ⟨n/L⟩^{-Λ_p} e^{-N_p}`,
   and `𝔼_p(a_n(p) ā_{n'}(p)) = 1_{n=n'} (φ(δp, n/L) + R_p(n/L) + E_p(n))`;
2'. (time parameter, F7/F27) for `p ≥ 1`, `t ∈ [p-1, p]`: `|𝔼_p|a_n(t)|² - φ(δt, n/L)| ≤ 2L^{-θ_p}`;
3. for `2 ≤ m ≤ R_p`, balanced `ζ⃗`, `n⃗`: `𝕂_p(a_{n_j}(p)^{ζ_j}) = ∑_{N ≤ N_p} truncSum p N p ζ⃗ n⃗
   + Ẽ_p` (= `∑_{𝒢 ∈ 𝒢_p, n(𝒢) ≤ N_p} K_𝒢(p, n⃗) + Ẽ_p`: truncation void for `N ≤ N_p`), with
   `Ẽ_p = 0` unless `∑ ζ_j n_j = 0`, `|Ẽ_p| ≤ (∏⟨n_j/L⟩)^{-Λ_p} e^{-N_p}`;
4. for the same data and `N ≤ N_p`: `|𝒦_{p,N}| = |truncSum p N p| ≤ (∏⟨n_j/L⟩)^{-Λ_p}
   L^{-(m-1)/6} δ^{νN}`. -/
def AnsatzAt (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : (Fin P.d → ℤ) → Ω → ℂ) (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ) :
    Prop :=
  -- (1) event and solution
  (MeasurableSet (Fev p) ∧ IsSymmetricEvent P.L P.φin g (Fev p) ∧
    (1 ≤ p → Fev p ⊆ Fev (p - 1)) ∧
    1 - Real.exp (-(P.N p : ℝ)) ≤ μ.real (Fev p) ∧
    (∀ ω ∈ Fev p, IsASolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) (a ω) ∧
      ∀ b, IsASolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) b →
        ∀ t ∈ Icc (0 : ℝ) p, b t = a ω t) ∧
    (∀ t ∈ Icc (0 : ℝ) p, ∀ n, Measurable fun ω => a ω t n) ∧
    ∀ (r : ℕ) (t : Fin r → Icc (0 : ℝ) p) (n : Fin r → (Fin P.d → ℤ)) (ζ : Fin r → ℤˣ),
      Integrable (fun ω => ∏ j, zpowSign (ζ j) (a ω (t j) (n j))) (μ.restrict (Fev p))) ∧
  -- (2) two-point function at time p
  (SNormR (P.Lambda p) (P.Lambda p) (R p) ≤
      ENNReal.ofReal (P.L ^ (-P.theta p)) ∧
    (∀ n, |E p n| ≤ jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)) * Real.exp (-(P.N p : ℝ))) ∧
    ∀ n n', ∫ ω in Fev p, a ω p n * (starRingEnd ℂ) (a ω p n') ∂μ =
      if n = n' then ((P.φ (P.δ * p) (latticePoint P.L n) + R p (latticePoint P.L n) + E p n : ℝ)
        : ℂ) else 0) ∧
  -- (2') two-point function at intermediate times
  (1 ≤ p → ∀ t ∈ Icc ((p : ℝ) - 1) p, ∀ n,
    |(∫ ω in Fev p, ‖a ω t n‖ ^ 2 ∂μ) - P.φ (P.δ * t) (latticePoint P.L n)| ≤
      2 * P.L ^ (-P.theta p)) ∧
  -- (3) higher cumulants
  (∀ m : ℕ, 2 ≤ m → m ≤ P.R p → ∀ ζ : Fin (2 * m) → ℤˣ, ∑ j, ((ζ j : ℤˣ) : ℤ) = 0 →
    ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
      jointCumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (ζ j) (a ω p (n j))) Finset.univ =
        (∑ N ∈ Finset.range (P.N p + 1), truncSum P (inputsF P R) p N (p : ℝ) ζ n) +
          Et p m ζ n ∧
      (∑ j, ((ζ j : ℤˣ) : ℤ) • n j ≠ 0 → Et p m ζ n = 0) ∧
      ‖Et p m ζ n‖ ≤ (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) *
        Real.exp (-(P.N p : ℝ))) ∧
  -- (4) order-N bound
  (∀ m : ℕ, 2 ≤ m → m ≤ P.R p → ∀ ζ : Fin (2 * m) → ℤˣ, ∑ j, ((ζ j : ℤˣ) : ℤ) = 0 →
    ∀ n : Fin (2 * m) → (Fin P.d → ℤ), ∀ N ≤ P.N p,
      ‖truncSum P (inputsF P R) p N (p : ℝ) ζ n‖ ≤
        (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) *
          P.L ^ (-((m : ℝ) - 1) / 6) * P.δ ^ (P.ν * N))

end WaveTurbulence
