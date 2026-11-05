/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickFiniteSum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickPatternEnergy

/-! # Actual lower-dimensional NT sums on source Wick slices -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset ApproxNT

/-- The actual untouched coordinates form precisely the standard NT sum,
with the original half-cell factors and modulations relabelled. -/
theorem tsum_wickSurvivor_eq_approxSum {d n : ℕ} (L μ : ℝ) (σ : Fin n → Fin 4)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (Ψ : (Fin (Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}) → ℝ) → ℂ) :
    (∑' a : {j : Fin n // σ j = 0} → (Fin d → ℤ) × (Fin d → ℤ),
      (∏ j, wickLinkAmplitude L z β γ j.val (a j)) *
        Ψ (fun i => μ*inner ℝ (latticePoint L (a ((wickSurvivorEquiv σ).symm i)).1)
          (latticePoint L (a ((wickSurvivorEquiv σ).symm i)).2))) =
      approxSum L μ
        (halfCellAmplitude (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
          (fun i => β ((wickSurvivorEquiv σ).symm i).val)
          (fun i => γ ((wickSurvivorEquiv σ).symm i).val)) Ψ := by
  let E := (Equiv.arrowCongr (wickSurvivorEquiv σ) (Equiv.refl ((Fin d → ℤ) × (Fin d → ℤ)))).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)
  simp_rw [wickSurvivorAmplitude_eq_halfCellAmplitude]
  exact E.tsum_eq (fun g =>
    halfCellAmplitude (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
      (fun i => β ((wickSurvivorEquiv σ).symm i).val)
      (fun i => γ ((wickSurvivorEquiv σ).symm i).val)
      (fun i => latticePoint L (g.1 i)) (fun i => latticePoint L (g.2 i)) *
        Ψ (fun i => μ*inner ℝ (latticePoint L (g.1 i)) (latticePoint L (g.2 i))))

/-- Exact identity for one actual source Wick slice: its only lattice
counting loss is the finite free-vector amplitude sum. -/
theorem tsum_wickSlice_eq_traced_NT {d n : ℕ} {L : ℝ} (hL : 0 < L) (μ : ℝ)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (J : Finset (Fin n)) (h : Disjoint (wickTracedLinks σ) J)
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    (∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ (fun j => latticePoint L (θ j).1)
        (fun j => latticePoint L (θ j).2) *
        resProfile J (fun Ω => C (WithLp.ofLp Ω) lam) (wickLatticeEnergy L μ θ))) =
      (∏ j, wickPatternCoefficient (σ j)) *
        (∑ v ∈ wickFreeLatticeBox L σ z, wickTracedAmplitude L σ z β γ v) *
        approxSum L μ
          (halfCellAmplitude (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
            (fun i => β ((wickSurvivorEquiv σ).symm i).val)
            (fun i => γ ((wickSurvivorEquiv σ).symm i).val))
          (resProfile (survivingSpecial (wickTracedLinks σ) J)
            (fun Ω => survivingTraceCoefficient (wickTracedLinks σ) J h C (WithLp.ofLp Ω) lam)) := by
  classical
  rw [tsum_wickPattern_halfCell_eq_sum_free hL,mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  calc
    _ = wickTracedAmplitude L σ z β γ v *
        (∑' a : {j : Fin n // σ j = 0} → (Fin d → ℤ) × (Fin d → ℤ),
          (∏ j, wickLinkAmplitude L z β γ j.val (a j)) *
            resProfile (survivingSpecial (wickTracedLinks σ) J)
              (fun Ω => survivingTraceCoefficient (wickTracedLinks σ) J h C (WithLp.ofLp Ω) lam)
              (fun i => μ*inner ℝ (latticePoint L (a ((wickSurvivorEquiv σ).symm i)).1)
                (latticePoint L (a ((wickSurvivorEquiv σ).symm i)).2))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro a
      rw [halfCellAmplitude_wickPatternInsert,resProfile_wickPatternInsert L μ σ (a,v) J h C lam]
      ring
    _ = _ := by rw [tsum_wickSurvivor_eq_approxSum]

/-- The exact source Wick slice has only a geometric pattern coefficient
and the proved free-vector counting loss outside its surviving NT norm. -/
theorem norm_tsum_wickSlice_le_traced_NT {d n : ℕ} {L : ℝ} (hL : 1 ≤ L) (μ : ℝ)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (J : Finset (Fin n)) (h : Disjoint (wickTracedLinks σ) J)
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    ‖(∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ (fun j => latticePoint L (θ j).1)
        (fun j => latticePoint L (θ j).2) *
        resProfile J (fun Ω => C (WithLp.ofLp Ω) lam) (wickLatticeEnergy L μ θ)))‖ ≤
      2^n * (2^d*L^d)^(wickTracedLinks σ).card *
      ‖approxSum L μ
          (halfCellAmplitude (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
            (fun i => β ((wickSurvivorEquiv σ).symm i).val)
            (fun i => γ ((wickSurvivorEquiv σ).symm i).val))
          (resProfile (survivingSpecial (wickTracedLinks σ) J)
            (fun Ω => survivingTraceCoefficient (wickTracedLinks σ) J h C (WithLp.ofLp Ω) lam))‖ := by
  rw [tsum_wickSlice_eq_traced_NT (zero_lt_one.trans_le hL) μ σ z β γ J h C lam,norm_mul,norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul (norm_wickPatternCoefficient_prod_le σ)
    (norm_sum_wickTracedAmplitude_le hL σ z β γ) (norm_nonneg _) (by positivity)

end WaveTurbulence.RegAsymp
