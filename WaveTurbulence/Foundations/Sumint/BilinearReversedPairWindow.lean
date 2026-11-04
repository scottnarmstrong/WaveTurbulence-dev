/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BilinearPairWindow
public import WaveTurbulence.Foundations.Sumint.BilinearTimeSign

/-!
# Pair cancellation in the literal source time direction

Fixing the source outer time fixes both linear modulations. The inner
source time then enters with a negative coefficient. Conjugation
reduces this direction to the landed window estimate, uniformly in the
outer-time modulations.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- The ordinary pair estimate with the source ordering of the time difference. -/
theorem exists_bilinear_reversed_pair_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηγ : η ≤ 2*((d:ℝ)-1)*(1-γ)) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ 2 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ a b : Mom d,
      ∀ ξ ζ : ℝ → Mom d, ∀ c l u v w : ℝ, 0 < c → l ≤ u → v ≤ w →
      (∀ t ∈ Icc v w, -(T₀*L^(2*γ)) ≤ c*(l-t) ∧ c*(u-t) ≤ T₀*L^(2*γ)) →
      (∫ t in Icc v w, ∫ s in Icc l u,
        ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖) ≤
          (w-v) * c⁻¹ * C * L^(2*d) := by
  obtain ⟨C,L₀,hC,hL₀,hbound⟩ :=
    exists_bilinear_pair_window_bound d hd γ hγ η hη hηγ T₀ hT₀
  refine ⟨C,L₀,hC,hL₀,?_⟩
  intro L hL a b ξ ζ c l u v w hc hlu hvw hwin
  have heq (t s : ℝ) :
      ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ =
        ‖WeylSums.bilinearLatticeSum L (c*(s-t)) a b (-(ξ t)) (-(ζ t))‖ := by
    have ht : c*(t-s) = -(c*(s-t)) := by ring
    rw [ht,norm_bilinearLatticeSum_time_neg]
  simp_rw [heq]
  exact hbound L hL a b (fun t => -(ξ t)) (fun t => -(ζ t)) c l u v w hc hlu hvw hwin

end WaveTurbulence.Sumint
