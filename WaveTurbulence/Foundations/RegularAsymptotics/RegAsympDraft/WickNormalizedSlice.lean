/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSliceNTIdentity
public import WaveTurbulence.Foundations.RegAsymp.WickScalarNorm

/-! # The exact source normalization on actual Wick slices -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset ApproxNT

/-- Removed and surviving source pairs partition the original order. -/
theorem card_untraced_add_trace {n : ℕ} (T : Finset (Fin n)) :
    Fintype.card {j : Fin n // j ∉ T} + T.card = n := by
  classical
  have hs := Fintype.card_subtype_compl (fun j : Fin n => j ∈ T)
  have hc : Fintype.card {j : Fin n // j ∈ T} = T.card := by simp
  rw [hc,Fintype.card_fin] at hs
  have ht : T.card ≤ n := by simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ T)
  omega

/-- The exact source Wick slice has only a geometric pattern coefficient
and the proved free-vector counting loss outside its surviving NT norm. -/
theorem norm_normalized_wickSlice_le_traced_NT {d n : ℕ} {L : ℝ} (hL : 1 ≤ L) (μ δ γexp : ℝ) (hδ : 0 ≤ δ)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (J : Finset (Fin n)) (h : Disjoint (wickTracedLinks σ) J)
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    ‖(((δ/(2*L^((d:ℝ)-γexp)))^(2*n):ℝ):ℂ)*(∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ (fun j => latticePoint L (θ j).1)
        (fun j => latticePoint L (θ j).2) *
        resProfile J (fun Ω => C (WithLp.ofLp Ω) lam) (wickLatticeEnergy L μ θ)))‖ ≤
      2^n * (2^d*L^d)^(wickTracedLinks σ).card *
      (δ/(2*L^((d:ℝ)-γexp)))^(2*(wickTracedLinks σ).card) *
      ‖(((δ/(2*L^((d:ℝ)-γexp)))^(2*Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}):ℝ):ℂ)*approxSum L μ
          (halfCellAmplitude (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
            (fun i => β ((wickSurvivorEquiv σ).symm i).val)
            (fun i => γ ((wickSurvivorEquiv σ).symm i).val))
          (resProfile (survivingSpecial (wickTracedLinks σ) J)
            (fun Ω => survivingTraceCoefficient (wickTracedLinks σ) J h C (WithLp.ofLp Ω) lam))‖ := by
  have hm := card_untraced_add_trace (wickTracedLinks σ)
  rw [tsum_wickSlice_eq_traced_NT (zero_lt_one.trans_le hL) μ σ z β γ J h C lam,
    norm_normalized_trace_product (by positivity : 0 ≤ δ/(2*L^((d:ℝ)-γexp))) _ _ hm,norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul (norm_wickPatternCoefficient_prod_le σ)
    (norm_sum_wickTracedAmplitude_le hL σ z β γ) (norm_nonneg _) (by positivity)

end WaveTurbulence.RegAsymp
