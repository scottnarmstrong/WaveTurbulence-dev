/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOps.LocalCore
public import WaveTurbulence.Foundations.Flower.ProtOps.LocalLattice
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs

/-! # PROT-OPS: o73 (13.4), `LocalOutputExtension`

Per-lattice-output time norms give the local `X^{θ,30d,0}` norm on a unit ball at cost `L^{31d}`: extensions at the
at most `(3L)^d` lattice points of the ball (pairwise `1/L`-separated) are glued with the disjoint bumps
`psi (L (k - k₀))`; each output derivative costs `L`, at most `L^{30d}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtOps

/-- **o73 (13.4)**, in the pinned form of `ProtDefs`. -/
theorem localOutputExtension : ProtDefs.LocalOutputExtension := by
  intro d θ _
  obtain ⟨B0, hB0, hB⟩ := exists_psi_bound d (30 * d)
  set B1 : ℝ := B0 + 1 with hB1
  have hB' : ∀ n ≤ 30 * d, ∀ x, ‖iteratedFDeriv ℝ n (psi d) x‖ ≤ B1 := fun n hn x => (hB n hn x).trans (by linarith)
  refine ⟨B1 * 3 ^ d, by positivity, ?_⟩
  intro L hL r Bset b₀ c₀ F X hX
  have hCpos : 0 < B1 * 3 ^ d * L ^ (31 * d) := by
    have := zero_lt_one.trans_le hL; positivity
  by_cases hXt : X = ⊤
  · rw [hXt, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCpos).ne']
    exact le_top
  obtain ⟨S, hS, hsep, hcard⟩ := lattice_finset L hL b₀ c₀
  have hS' : ProtDefs.latticeBall L b₀ c₀ = (↑S : Set (Mom d)) := hS.symm
  rw [hS']
  refine (localExt_core hB' θ hL Bset F X (lt_top_iff_ne_top.2 hXt) S hsep ?_).trans ?_
  · intro k hk
    exact hX k (by rw [hS']; exact hk)
  · refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hL0 := zero_lt_one.trans_le hL
    calc L ^ (30 * d) * B1 * S.card ≤ L ^ (30 * d) * B1 * (3 * L) ^ d := by gcongr
      _ = B1 * 3 ^ d * L ^ (31 * d) := by
        rw [mul_pow, show 31 * d = 30 * d + d by ring, pow_add]; ring

end WaveTurbulence.Flower.ProtOps
