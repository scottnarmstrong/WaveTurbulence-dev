/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormGeometricTail
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.XChain.InductParameters
/-! The actual WKE Taylor tail has a source spatial-norm bound and the exact sum remainder. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset Set
open scoped ENNReal

noncomputable def wkeTaylorTail (P : WTParams) (p M : ℕ) (t : ℝ) : Mom P.d → ℝ :=
  fun k => ∑' j, wkeTaylorTerm (P.φ (P.δ * p)) P.δ p (M + j) t k

theorem wkeTaylorTail_SNormR_bound (P : WTParams) (hW : WkeTaylorBody P)
    (hd : 1 ≤ P.d) (p : ℕ) (hp : p < P.D) (hC : 0 ≤ P.C₂)
    (hr : 0 ≤ P.C₁ * P.δ) (hr1 : P.C₁ * P.δ < 1)
    (M : ℕ) (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNormR (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (wkeTaylorTail P p M t) ≤
      ENNReal.ofReal (P.C₂ * (P.C₁ * P.δ) ^ M / (1 - P.C₁ * P.δ)) := by
  have hΛ := lambda_succ_ge P hd hp
  have hA : 4 * P.Lambda (p + 1) ≠ 0 := by omega
  exact SNormR_geometric_tail_bound hA
    (fun N => wkeTaylorTerm (P.φ (P.δ * p)) P.δ p N t)
    P.C₂ (P.C₁ * P.δ) hC hr hr1 (fun N => (hW p hp).2.2 N t ht) M

theorem wkeTaylorTail_eq_remainder (P : WTParams) (hW : WkeTaylorBody P)
    (p : ℕ) (hp : p < P.D) (M : ℕ) (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (k : Mom P.d) :
    wkeTaylorTail P p M t k = P.φ (P.δ * t) k -
      ∑ N ∈ range M, wkeTaylorTerm (P.φ (P.δ * p)) P.δ p N t k := by
  have hs := ((hW p hp).2.1 t ht k).1.of_abs
  have he := hs.sum_add_tsum_nat_add M
  rw [((hW p hp).2.1 t ht k).2] at he
  have hshift : (∑' j, wkeTaylorTerm (P.φ (P.δ * p)) P.δ p (j + M) t k) = wkeTaylorTail P p M t k := by
    apply tsum_congr
    intro j
    rw [Nat.add_comm j M]
  rw [hshift] at he
  linarith

end WaveTurbulence.Induct
