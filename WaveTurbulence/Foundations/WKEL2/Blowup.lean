/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzContinuation

/-!
# The full weighted L² blow-up conjunct of TARGET Proposition 3.2

The maximal time is exactly the landed Schwartz maximal time `WKE.tauMax`.
Uniform continuation from every bounded endpoint gives an eventual lower
bound, for every threshold and every source solution, rather than merely
an unbounded sequence of norms.
-/

public section

noncomputable section

open Set
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

/-- TARGET `wkelwp`, conjunct 3, with its exact frozen weighted norm and solution notion. -/
theorem wkelwp_blowup (d : ℕ) (hd : 3 ≤ d) (φin : 𝓢(Mom d, ℝ)) :
    WKE.tauMax φin < ⊤ → ∀ s : ℝ, (d : ℝ) / 2 - 1 < s → ∀ M : ℝ,
      ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ENNReal.ofReal τ₀ < WKE.tauMax φin ∧
        ∀ τstar > τ₀, ENNReal.ofReal τstar < WKE.tauMax φin → ∀ φ : ℝ → 𝓢(Mom d, ℝ),
          IsWKESolution φin τstar φ → M < weightedL2Norm s (φ τstar) := by
  intro hfinite s hs M
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs₀ : 0 ≤ s := by linarith only [hdR, hs]
  have hpos := tauMax_pos_of_weightedPicard hd s hs₀ hs φin
  have hne : WKE.tauMax φin ≠ ⊤ := hfinite.ne
  let T := (WKE.tauMax φin).toReal
  have hT : 0 < T := ENNReal.toReal_pos hpos.ne' hne
  let R := max 0 M
  have hR : 0 ≤ R := le_max_left _ _
  let δ := cubicUniformStep (collisionBanach hd s hs) R
  have hδ : 0 < δ := cubicUniformStep_pos _ hR
  let τ₀ := max 0 (T - δ / 2)
  have hτ₀ : 0 ≤ τ₀ := le_max_left _ _
  have hτ₀T : τ₀ < T := max_lt hT (by linarith only [hδ])
  refine ⟨τ₀, hτ₀, (ENNReal.ofReal_lt_iff_lt_toReal hτ₀ hne).2 hτ₀T, ?_⟩
  intro τstar hτstar _ φ hφ
  have hτpos : 0 < τstar := hτ₀.trans_lt hτstar
  by_contra! hend
  obtain ⟨ψ, hψ⟩ := exists_isWKESolution_extension hd s hs₀ hs hτpos.le hR hφ
    (hend.trans (le_max_right _ _))
  have hext := WKE.ofReal_le_tauMax (add_pos hτpos hδ) hψ
  have hextT : τstar + δ ≤ T := (ENNReal.ofReal_le_iff_le_toReal hne).1 hext
  have hnear : T - δ / 2 < τstar := (le_max_right _ _).trans_lt hτstar
  linarith only [hextT, hnear, hδ]

end WaveTurbulence.WKEL2
