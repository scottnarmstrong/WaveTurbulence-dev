/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.SmoothCutoffPacket

/-!
# Recursive cutoff integrals on a ternary tree

Each branching vertex has a frequency, a lower integration endpoint and
three time shifts. This auxiliary analytic tree represents oriented
cutoff integrals. It is separate from the heap-domain model: the latter
requires feasible endpoints before this representation can be applied.
Frequencies here use the Fourier normalization `2π`; the paper's `πα`
therefore corresponds to the input frequency `α/2`.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Analysis

/-- A local ternary analytic tree. The five real labels at a branch are
its lower endpoint, frequency and three child time shifts. -/
inductive IntegrationTree where
  | leaf
  | node (a α σ₁ σ₂ σ₃ : ℝ) (left middle right : IntegrationTree)

namespace IntegrationTree

/-- All lower endpoints lie in the range of the uniform kernel estimate. -/
@[expose] def Admissible : IntegrationTree → Prop
  | .leaf => True
  | .node a _ _ _ _ l m r => a ∈ Set.Icc 0 1 ∧ l.Admissible ∧ m.Admissible ∧ r.Admissible

/-- Actual recursively defined cutoff time integrals. -/
@[expose] noncomputable def value (χ : ℝ → ℂ) : IntegrationTree → ℝ → ℂ
  | .leaf, t => χ t
  | .node a α σ₁ σ₂ σ₃ l m r, t =>
      χ t * ∫ s in a..t, timePhase α s *
        ((l.value χ (s - σ₁) * m.value χ (s - σ₂)) * r.value χ (s - σ₃))

/-- Construct an actual spectral representation by the certified packet
operations, rather than postulating an envelope for the iterated integral. -/
@[expose] noncomputable def packet {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) : (T : IntegrationTree) → T.Admissible → SpectralPacket
  | .leaf, _ => smoothCutoffPacket hχ hs
  | .node _ α σ₁ σ₂ σ₃ l m r, h =>
      (((((l.packet hχ hs h.2.1).shift σ₁).multiply
        ((m.packet hχ hs h.2.2.1).shift σ₂)).multiply
          ((r.packet hχ hs h.2.2.2).shift σ₃)).modulate α).integrate hχ hs h.1

/-- The packet synthesis is the actual cutoff iterated integral, at every
time, including times outside the final unit interval. -/
theorem synthesis_packet {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (T : IntegrationTree) (h : T.Admissible) (t : ℝ) :
    (T.packet hχ hs h).synthesis t = T.value χ t := by
  induction T generalizing t with
  | leaf => exact synthesis_smoothCutoffPacket hχ hs t
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      rw [packet, SpectralPacket.synthesis_integrate]
      unfold value
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs'
      rw [SpectralPacket.synthesis_modulate,
        SpectralPacket.synthesis_multiply, SpectralPacket.synthesis_multiply,
        SpectralPacket.synthesis_shift, SpectralPacket.synthesis_shift, SpectralPacket.synthesis_shift,
        hl h.2.1, hm h.2.2.1, hr h.2.2.2]

/-- The resulting finite sum bound for the actual cutoff integral. Its
weights will be identified with the binary vertex choices separately. -/
theorem enorm_value_le_packet_mass {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (T : IntegrationTree) (h : T.Admissible) (t : ℝ) :
    ‖T.value χ t‖ₑ ≤ (∑ i, (T.packet hχ hs h).weight i) * ENNReal.ofReal Real.pi := by
  rw [← synthesis_packet hχ hs T h t]
  exact SpectralPacket.enorm_synthesis_le _ t

end IntegrationTree
end WaveTurbulence.Analysis
