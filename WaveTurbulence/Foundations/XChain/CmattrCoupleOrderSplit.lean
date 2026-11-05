/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CmattrCoupleIdentity
public import WaveTurbulence.Foundations.XChain.CoupleTruncatedOrderCarrier
/-! T.cmattr on the actual finite order sum plus the literal high-order tail and input-error series. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal

theorem cumulant_aTr_couple_eq_order_sum_add_tail_add_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (c : Ω → (Fin P.d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (p Ncut : ℕ) (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin 2 → (Fin P.d → ℤ))
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|) :
    cumulant μ (fun j ω => zpowSign (![1, -1] j) (aTr P.L P.γ P.δ p (P.N (p + 1)) (c ω) t (n j))) univ =
      ((∑ N ∈ range (Ncut + 1), truncSum P F (p + 1) N t ![1, -1] n) +
        ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (P.N (p + 1)) (P.N p)},
          if Ncut < LG.1.garden.order then KG P.L P.γ P.δ F LG.1 t n else 0) +
            cmattrError μ P.L P.γ P.δ F ![1, -1] c p (P.N (p + 1)) (P.N p) t n := by
  rw [cumulant_aTr_eq_canonC_sum_add_error P.L P.γ P.δ F c hc hcs hM
    p (P.N (p + 1)) (P.N p) t hpt htp n hF]
  rw [full_truncated_couple_sum_eq_sum_orders_add_tail P F p Ncut t n]

end WaveTurbulence.Induct
