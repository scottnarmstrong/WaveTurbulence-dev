/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GardenPartition
public import WaveTurbulence.Foundations.XChain.SNormAddBounds
/-! TARGET L2229–2255: addition of the three genuine couple contributions in the exact spatial norm. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open scoped ENNReal

/-- Finite positive-order spatial norm supplies the regularity needed for the sum rule. -/
theorem contDiff_of_SNorm_bound {d A B : ℕ} (hA : A ≠ 0) (f : Mom d → ℂ)
    (C : ℝ) (h : SNorm A B f ≤ ENNReal.ofReal C) : ContDiff ℝ A f := by
  classical
  have ht : SNorm A B f < ⊤ := h.trans_lt ENNReal.ofReal_lt_top
  unfold SNorm at ht
  split_ifs at ht with hf
  · exact hf.resolve_left hA
  · exact False.elim (not_lt_of_ge le_rfl ht)

theorem SNorm_three_add_bound {d A B : ℕ} (hA : A ≠ 0) (f g h : Mom d → ℂ)
    (C D E : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hf : SNorm A B f ≤ ENNReal.ofReal C) (hg : SNorm A B g ≤ ENNReal.ofReal D)
    (hh : SNorm A B h ≤ ENNReal.ofReal E) :
    SNorm A B (fun k => f k + g k + h k) ≤ ENNReal.ofReal (C + D + E) := by
  have hcf := contDiff_of_SNorm_bound hA f C hf
  have hcg := contDiff_of_SNorm_bound hA g D hg
  have hch := contDiff_of_SNorm_bound hA h E hh
  exact SNorm_add_bound (f + g) h (hcf.add hcg) hch (C + D) E (add_nonneg hC hD) hE
    (SNorm_add_bound f g hcf hcg C D hC hD hf hg) hh

/-- Pure addition on the literal carrier partition; none of its three estimates is an input gate. -/
theorem coupleRemainder_norm_le_sum (P : WTParams) (R : ℕ → Mom P.d → ℝ)
    (p N A B : ℕ) (hA : A ≠ 0) (t : ℝ) (C D E : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hb : SNorm A B (nonregularCoupleSum P (inputsF P R) (p + 1) N t) ≤ ENNReal.ofReal C)
    (hc : SNorm A B (incoherentCoupleSum P (inputsF P R) (p + 1) N t) ≤ ENNReal.ofReal D)
    (hd : SNorm A B (fun k => coherentCoupleSum P (inputsF P R) (p + 1) N t k -
      if Even N then (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p (N / 2) t k : ℂ) else 0) ≤ ENNReal.ofReal E) :
    SNorm A B (coupleRemainder P R p N t) ≤ ENNReal.ofReal (C + D + E) := by
  rw [coupleRemainder_eq_three_parts]
  exact SNorm_three_add_bound hA _ _ _ C D E hC hD hE hb hc hd

end WaveTurbulence.LGSpine
