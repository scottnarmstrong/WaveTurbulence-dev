/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.IntegrationTree

/-!
# Binary resonance weights of the constructed tree packet

The packet index is recursively `Unit` at a leaf and
`Bool × ((left × middle) × right)` at a branch. Thus it is exactly one
binary endpoint choice per branching vertex. The output centre is zero
or the vertex resonance according to that vertex's bit. The input
resonance is the vertex frequency plus its three child output centres.
The cutoff affects only a common multiplicative cost, never these centres.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Analysis.IntegrationTree

/-- Number of branching vertices, excluding leaves. -/
@[expose] def branchCount : IntegrationTree → ℕ
  | .leaf => 0
  | .node _ _ _ _ _ l m r => l.branchCount + m.branchCount + r.branchCount + 1

/-- The common analytic cost at one branching vertex. -/
@[expose] noncomputable def branchingCost (χ : ℝ → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (cutoffKernelConstant χ) * ENNReal.ofReal (12 * Real.pi) *
    (ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (4 * Real.pi))

/-- The common analytic cost over the whole tree, with one Fourier cutoff
cost at each leaf and one integration/convolution cost at each branch. -/
@[expose] noncomputable def packetCost (χ : ℝ → ℂ) : IntegrationTree → ℝ≥0∞
  | .leaf => ENNReal.ofReal (cutoffFourierConstant χ)
  | .node _ _ _ _ _ l m r => branchingCost χ *
      ((l.packetCost χ * m.packetCost χ) * r.packetCost χ)

/-- The input resonance at a branch; the root bit affects the output
centre but not this resonance. Leaf resonance is zero. -/
@[expose] noncomputable def resonance {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) : (T : IntegrationTree) → (h : T.Admissible) →
      (T.packet hχ hs h).Index → ℝ
  | .leaf, _, _ => 0
  | .node _ α _ _ _ l m r, h, i =>
      (((l.packet hχ hs h.2.1).centre i.2.1.1 +
        (m.packet hχ hs h.2.2.1).centre i.2.1.2) +
          (r.packet hχ hs h.2.2.2).centre i.2.2) + α

/-- Product of the reciprocal brackets at all branching vertices.
`scale=1` uses the Fourier frequencies; `scale=2` uses the paper's
frequencies for the phase `πα`. -/
@[expose] noncomputable def resonanceWeight {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (scale : ℝ) : (T : IntegrationTree) → (h : T.Admissible) →
      (T.packet hχ hs h).Index → ℝ≥0∞
  | .leaf, _, _ => 1
  | .node a α σ₁ σ₂ σ₃ l m r, h, i =>
      ENNReal.ofReal (oscillatoryWeight (scale * (node a α σ₁ σ₂ σ₃ l m r).resonance hχ hs h i)) *
        ((l.resonanceWeight hχ hs scale h.2.1 i.2.1.1 *
          m.resonanceWeight hχ hs scale h.2.2.1 i.2.1.2) *
            r.resonanceWeight hχ hs scale h.2.2.2 i.2.2)

/-- The binary choice is precisely between the lower and upper endpoint
frequencies, with no new frequencies introduced by the cutoff. -/
theorem centre_node_eq {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ)
    (a α σ₁ σ₂ σ₃ : ℝ) (l m r : IntegrationTree)
    (h : (node a α σ₁ σ₂ σ₃ l m r).Admissible)
    (i : ((node a α σ₁ σ₂ σ₃ l m r).packet hχ hs h).Index) :
    ((node a α σ₁ σ₂ σ₃ l m r).packet hχ hs h).centre i =
      if i.1 then (node a α σ₁ σ₂ σ₃ l m r).resonance hχ hs h i else 0 := rfl

/-- Every packet coefficient is the product of the common analytic cost
and the source resonance denominators. -/
theorem packet_weight_eq {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (T : IntegrationTree) (h : T.Admissible)
    (i : (T.packet hχ hs h).Index) :
    (T.packet hχ hs h).weight i = T.packetCost χ * T.resonanceWeight hχ hs 1 h i := by
  induction T with
  | leaf => simp only [packet, smoothCutoffPacket, packetCost, resonanceWeight, mul_one]
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      change a ∈ Set.Icc 0 1 ∧ l.Admissible ∧ m.Admissible ∧ r.Admissible at h
      change ENNReal.ofReal (cutoffKernelConstant χ) * ENNReal.ofReal (12 * Real.pi) *
        ((ENNReal.ofReal (4 * Real.pi) *
          ((ENNReal.ofReal (4 * Real.pi) *
            ((l.packet hχ hs h.2.1).weight i.2.1.1 *
              (m.packet hχ hs h.2.2.1).weight i.2.1.2)) *
                (r.packet hχ hs h.2.2.2).weight i.2.2)) *
                  ENNReal.ofReal (oscillatoryWeight
                    (((l.packet hχ hs h.2.1).centre i.2.1.1 +
                      (m.packet hχ hs h.2.2.1).centre i.2.1.2) +
                        (r.packet hχ hs h.2.2.2).centre i.2.2 + α))) = _
      erw [hl h.2.1, hm h.2.2.1, hr h.2.2.2]
      simp only [packetCost, branchingCost, resonanceWeight, one_mul, resonance]
      ring

/-- Explicit resonance-product bound for the actual cutoff integral. -/
theorem enorm_value_le_resonance_sum {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (T : IntegrationTree) (h : T.Admissible) (t : ℝ) :
    ‖T.value χ t‖ₑ ≤ T.packetCost χ *
      (∑ i, T.resonanceWeight hχ hs 1 h i) * ENNReal.ofReal Real.pi := by
  have hh := enorm_value_le_packet_mass hχ hs T h t
  simp_rw [packet_weight_eq hχ hs T h] at hh
  rw [← Finset.mul_sum] at hh
  exact hh

end WaveTurbulence.Analysis.IntegrationTree
