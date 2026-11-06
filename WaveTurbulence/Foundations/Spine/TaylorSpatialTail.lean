/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TaylorBoundPrefix
public import WaveTurbulence.Foundations.Spine.MarkedGeometricTail
public import WaveTurbulence.Foundations.Spine.StageOrderLower
/-! The landed WKE Taylor estimate in the actual spatial norm above the full-code cutoff. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set

theorem taylor_spatial_tail (P : WTParams) (hTaylor : TaylorBoundAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ)
    (hC₂ : 0 ≤ P.C₂) (hlarge : P.C₂ ≤ P.L)
    {p n : ℕ} (hp : p < P.D) (htail : P.N (p + 1) < 2 * n)
    (B : ℝ) (hB : 0 ≤ B) (hlog : 2 * (B + 1) + 1 ≤ Real.log P.L)
    (hsmall : P.C₁ * P.δ ≤ Real.sqrt P.δ * Real.exp (-1))
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNormR (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) * P.L ^ (-B)) := by
  apply (hTaylor p hp n t ht).trans
  apply ENNReal.ofReal_le_ofReal
  exact marked_geometric_tail_le (by positivity) hδ.le (zero_lt_one.trans_le hL)
    hC₂ hlarge hsmall n
    (tail_order_ge_log P hd (B + 1) (by linarith) hlog (p + 1) n htail)

end WaveTurbulence.LGSpine
