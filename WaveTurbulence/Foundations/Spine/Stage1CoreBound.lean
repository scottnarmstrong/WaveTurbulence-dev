/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1SumBound
public import WaveTurbulence.Foundations.Spine.FinalNumerics
/-! TARGET (finalprooffin2), L2253-L2255, pointwise and before the weights: the sum of the Stage 1 pieces. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

/-- TARGET (finalprooffin2), L2253-L2255, for the integral conjunct of `Represents` alone (R23 (2)). The
centre loss `C_1^{n_sb}` (R24 D3) is absorbed per node: the hypothesis `hδ` is
`6 C_0 C_1^6 delta^{2 nu} <= 1`. -/
theorem stage1_core_bound_int (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (S : Stage1Data P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (Cl : Type) [Fintype Cl] (cls : S.Pc → Cl) (s : ℝ) (hs0 : 0 < s)
    (hsound : ∀ π, (S.piece π).Sound p base roots)
    (hnsb : ∀ π, (S.piece π).Gsb.order ≤ n)
    (hrep : ∀ π, (S.piece π).RepresentsInt n tt base roots s (S.val π))
    (hrb : ∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ n)
    (hgb : ∀ π, (S.piece π).gbar ≤ n)
    (hpc : ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      (3 : ℝ) ^ n * (C₀ : ℝ) ^ n * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r))
    (hδ : ((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν) ≤ 1)
    (hT2 : P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2)
    (hS2 : (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2)
    (hL : 4 * (P.C₂ * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) ≤
      P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))) :
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s *
      (P.δ ^ (8 * P.ν * n) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
  have h := stage1_sum_bound_int P hs hcoarse hfourier hcount hp hR hRmax S tt base roots C₀ Cl cls s hs0
    hsound hnsb hrep hrb hgb hpc hT2 hS2
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hs0.le)
  set Y : ℝ := 4 * (P.C₂ * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) with hY
  have hY0 : 0 ≤ Y := by
    have hC₂ : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
    have hL0 : 0 < P.L := by linarith [hs.L_ge]
    rw [hY]; positivity
  have hδ0 := hs.delta_pos
  have hpow : (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * ((6 * C₀ : ℕ) : ℝ) ^ n = (((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν)) ^ n *
      P.δ ^ (8 * P.ν * n) := by
    have h8 : P.δ ^ (8 * P.ν * (n : ℝ)) = (P.δ ^ (8 * P.ν)) ^ n := Real.rpow_mul_natCast hδ0.le _ _
    have h10 : P.δ ^ (10 * P.ν) = P.δ ^ (2 * P.ν) * P.δ ^ (8 * P.ν) := by
      rw [← Real.rpow_add hδ0]; ring_nf
    rw [h8, ← mul_pow, ← mul_pow, h10]
    congr 1; ring
  have hrearr : 4 * (P.C₂ * (P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))) =
      ((P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * ((6 * C₀ : ℕ) : ℝ) ^ n) * Y := by
    rw [hY]; ring
  rw [hrearr, hpow]
  have hn1 : (((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν)) ^ n ≤ 1 := pow_le_one₀ (by
    have := hs.c1_ge
    positivity) hδ
  have hδ8 : 0 ≤ P.δ ^ (8 * P.ν * (n : ℝ)) := Real.rpow_nonneg hδ0.le _
  calc (((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν)) ^ n * P.δ ^ (8 * P.ν * (n : ℝ)) * Y
      ≤ 1 * P.δ ^ (8 * P.ν * (n : ℝ)) * Y := by gcongr
    _ = P.δ ^ (8 * P.ν * (n : ℝ)) * Y := by ring
    _ ≤ P.δ ^ (8 * P.ν * n) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))) :=
        mul_le_mul_of_nonneg_left hL hδ8

/-- TARGET (finalprooffin2), L2253-L2255: `stage1_core_bound_int` for the full `Represents`. -/
theorem stage1_core_bound (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    {p R n : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (S : Stage1Data P R) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (tt : Fin (2 * R) → ℝ) (Cl : Type) [Fintype Cl] (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (s : ℝ) (hs0 : 0 < s)
    (hsound : ∀ π, (S.piece π).Sound p base roots)
    (hnsb : ∀ π, (S.piece π).Gsb.order ≤ n)
    (hrep : ∀ π, (S.piece π).Represents n tt base roots (members (cls π)) (sel π) F s (S.val π))
    (hrb : ∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ n)
    (hgb : ∀ π, (S.piece π).gbar ≤ n)
    (hpc : ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      (3 : ℝ) ^ n * (C₀ : ℝ) ^ n * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r))
    (hδ : ((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν) ≤ 1)
    (hT2 : P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2)
    (hS2 : (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2)
    (hL : 4 * (P.C₂ * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) ≤
      P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))) :
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s *
      (P.δ ^ (8 * P.ν * n) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) :=
  stage1_core_bound_int P hs hcoarse hfourier hcount hp hR hRmax S tt base roots C₀ Cl cls s hs0
    hsound hnsb (fun π => (hrep π).2) hrb hgb hpc hδ hT2 hS2 hL
