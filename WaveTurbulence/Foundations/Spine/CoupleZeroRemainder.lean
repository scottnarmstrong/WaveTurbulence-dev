/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoupleZeroClassification
public import WaveTurbulence.Foundations.Spine.CoherentZeroNorm
/-! Full order-zero couple remainder, including the classification of every carrier term. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset WaveTurbulence.Reg
open scoped ENNReal

theorem coherent_of_couple_order_zero (LG : LayeredGarden 2) (hc : IsCouple LG.garden)
    (ho : LG.garden.order = 0) : IsCoherentCouple LG := by
  have hQ := trivial_decodes_of_couple_zero LG.garden hc ho
  have hg := carrier_unique (uniformDecodedCouple_decodes 0 .triv) hQ
  have hreg := uniformDecodedCouple_regular 0 .triv rfl
  refine ⟨hg ▸ hreg, .triv, rfl, hQ, ?_⟩
  simp only [LayeredGarden.incoherency, RegCpl.links, RegCpl.linksAt,
    List.not_mem_nil, false_and, filter_false, card_empty]

theorem truncSumC_zero_eq_coherent (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (p : ℕ) (t : ℝ) (k : Mom P.d) :
    truncSumC P F (p + 1) 0 t k = coherentCoupleSum P F (p + 1) 0 t k := by
  classical
  have hall : ∀ LG ∈ coupleCarrier P (p + 1) 0, IsCoherentCouple LG := by
    intro LG hLG
    have hm := (Canon.finite_truncSumC_support P (p + 1) 0).mem_toFinset.mp hLG
    exact coherent_of_couple_order_zero LG hm.1.1 hm.2.2
  rw [Canon.truncSumC_eq_sum]
  unfold coherentCoupleSum
  rw [filter_eq_self.mpr hall]
  rfl

theorem coupleRemainder_zero (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p : ℕ) (t : ℝ) :
    coupleRemainder P R p 0 t = fun k => (R p k : ℂ) := by
  funext k
  unfold coupleRemainder
  rw [truncSumC_zero_eq_coherent]
  simpa only [Nat.zero_div, ite_eq_left (show Even (0 : ℕ) from ⟨0, rfl⟩)] using coherentCoupleSum_zero_sub_taylor P R p t k

theorem coupleRemainder_zero_SNorm_bound (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) (t : ℝ) :
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p 0 t) ≤
      ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5)) := by
  have he : coupleRemainder P R p 0 t =
      fun k => coherentCoupleSum P (inputsF P R) (p + 1) 0 t k -
        (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p 0 t k : ℂ) := by
    funext k
    simp only [coupleRemainder_zero, coherentCoupleSum_zero_sub_taylor]
  rw [he]
  exact coherent_zero_SNorm_bound P hd hL hp R hR t

end WaveTurbulence.LGSpine
