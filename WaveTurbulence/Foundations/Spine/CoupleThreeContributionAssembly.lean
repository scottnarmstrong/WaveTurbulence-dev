/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RegularLegPrefix
public import WaveTurbulence.Foundations.Spine.ThreeContributionReserve
public import WaveTurbulence.Foundations.Spine.NormAssembly
public import WaveTurbulence.Foundations.Spine.ModificationOrderBudget
/-! Final norm addition on the actual carrier partition; this consumer is not a spine input. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

/-- TARGET L2253–2255: consume the three estimates on the proved carrier partition. -/
theorem coupleRemainder_bound_of_three_contributions (P : WTParams)
    (hd : 1 ≤ P.d) (hL : 0 ≤ P.L) (hδ : 0 ≤ P.δ)
    (hcoh : CoherentRemainderAt P) (hinc : IncoherentRemainderAt P)
    (hreserve : ThreeContributionReserveAt P)
    {p N : ℕ} (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4)
    (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (hnonreg : SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (nonregularCoupleSum P (inputsF P R) (p + 1) N t) ≤
      ENNReal.ofReal (P.δ ^ (2 * P.ν * N) *
        P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))) :
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
      ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) *
        P.δ ^ (2 * P.ν * N)) := by
  let E := P.δ ^ (2 * P.ν * N) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))
  have hE : 0 ≤ E := mul_nonneg (Real.rpow_nonneg hδ _) (Real.rpow_nonneg hL _)
  have hΛ := forty_dim_le_Lambda P hd (show p + 1 ≤ P.D by omega)
  have hh := coupleRemainder_norm_le_sum P R p N (4 * P.Lambda (p + 1))
    (4 * P.Lambda (p + 1)) (by omega) t E E E hE hE hE hnonreg
    (hinc p hp R hR N hN t ht) (hcoh p hp R hR N hN t ht)
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    E + E + E = P.δ ^ (2 * P.ν * N) *
        (3 * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) := by dsimp only [E]; ring
    _ ≤ P.δ ^ (2 * P.ν * N) * P.L ^ (-((4 * P.theta (p + 1) + P.theta p) / 5)) :=
      mul_le_mul_of_nonneg_left (hreserve p hp) (Real.rpow_nonneg hδ _)
    _ = _ := by
      rw [show -((4 * P.theta (p + 1) + P.theta p) / 5) =
        -(4 * P.theta (p + 1) + P.theta p) / 5 by ring]
      exact mul_comm _ _

end WaveTurbulence.LGSpine
