/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ParametricHalfCell
public import WaveTurbulence.Foundations.RegAsymp.CountableCellSingularRepresentation

/-! # Exact ordinary-cell representation of the actual half-cell amplitude

The geometric cell cover is fixed before the modulation frequencies vary.
No half-width cutoff is replaced by an ordinary-width cutoff.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Incoh Finset
open scoped ENNReal

/-- The ordinary Fourier cells intersecting the literal half-cell support. -/
def halfCellOrdinaryCells {d n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ) :
    Finset (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :=
  (cellBox_finite (lt := fun i j : Fin n => i<j)
    (xs := fun _ => .zero) (ys := fun _ => .zero) (fun _ => trivial) (fun _ => trivial)
    (fun j => halfCellCenter (z (j,0))) (fun j => halfCellCenter (z (j,1)))
    (fun _ => max 1 (Real.sqrt d))).toFinset

/-- Only a dimensional geometric number of ordinary cells is needed. -/
theorem card_halfCellOrdinaryCells_le {d n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ) :
    ((halfCellOrdinaryCells z).card:ℝ) ≤ ((2*max 1 (Real.sqrt d)+5)^(2*d))^n := by
  have h := card_cellBox_le (lt := fun i j : Fin n => i<j)
    (xs := fun _ => .zero) (ys := fun _ => .zero) (fun _ => trivial) (fun _ => trivial)
    (fun j => halfCellCenter (z (j,0))) (fun j => halfCellCenter (z (j,1)))
    (lam := fun _ => max 1 (Real.sqrt d)) (fun _ => by positivity)
  simpa only [halfCellOrdinaryCells,prod_const,card_univ,Fintype.card_fin] using h

/-- Fourier inversion retains the actual half-cell amplitude under every
ordinary cell, so the representation applies to the literal source kernel. -/
theorem halfCellAmplitude_eq_sum_cellFn {d n : ℕ} (hn : 0 < n)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d) (x y : Fin n → Mom d) :
    halfCellAmplitude z β γ x y = ∑ pq ∈ halfCellOrdinaryCells z,
      ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        fourierW (halfCellAmplitude z β γ) τ.1 τ.2 *
          ∏ j, cellFn (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j) (x j) (y j) := by
  have h := W_eq_sum_appFac (lt := fun i j : Fin n => i<j)
    (xs := fun _ => .zero) (ys := fun _ => .zero) (fun _ => trivial) (fun _ => trivial)
    (halfCellAmplitude_support z β γ) (halfCellAmplitude_fourier_setup hn z β γ).2 ∅ x y
  have hj : ∀ j : Fin n, ¬(n ≤ j.val+0) := fun j => by omega
  simpa only [halfCellOrdinaryCells,appFac,hj,ite_false] using h

/-- The actual half-cell singular integral has the same literal finite
representation used by the countable mixture Fubini theorem. -/
theorem singInt_halfCellAmplitude_eq {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (J : Finset (Fin n)) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d) :
    singInt J (halfCellAmplitude z β γ) = ∑ pq ∈ halfCellOrdinaryCells z,
      ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        fourierW (halfCellAmplitude z β γ) τ.1 τ.2 *
          ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j) := by
  apply singInt_eq hd J (halfCellOrdinaryCells z) (halfCellAmplitude_fourier_setup hn z β γ).1
  intro x y
  have h := halfCellAmplitude_eq_sum_cellFn hn z β γ x y
  have hj : ∀ j : Fin n, ¬(n ≤ j.val+0) := fun j => by omega
  simpa only [appFac,hj,ite_false] using h

/-- Discarding the positive Fourier moment gives a linear, not order-powered,
modulation budget for the literal coefficient in the cell representation. -/
theorem integral_norm_fourierW_halfCellAmplitude_le {d n : ℕ} (hn : 0 < n)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d) :
    (∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW (halfCellAmplitude z β γ) τ.1 τ.2‖) ≤
      (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖)))*halfLinkFirstMomentConstant d^(2*n) := by
  have hF := (halfCellAmplitude_fourier_setup hn z β γ).1
  have hD := (halfLinkFirstMomentConstant_pos d).le
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [ofReal_integral_norm_eq_lintegral_enorm hF]
  have hb := halfCellAmplitude_fourier_budget z β γ
  have he : ENNReal.ofReal (1+2*Real.pi) *
      (ENNReal.ofReal (1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖))) *
        ENNReal.ofReal (halfLinkFirstMomentConstant d)^(2*n)) =
      ENNReal.ofReal ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖)))*
        halfLinkFirstMomentConstant d^(2*n)) := by
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hD,mul_assoc]
  apply le_trans _ (hb.trans_eq he)
  apply lintegral_mono
  intro τ
  exact le_mul_of_one_le_right bot_le (ENNReal.one_le_ofReal.mpr (by
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (freqNorm_nonneg τ.1 τ.2))))

/-- A geometric singular bound for the actual half-cell, with a single
linear modulation loss independent of the number of singular integrations. -/
theorem norm_singInt_halfCellAmplitude_le {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ (J : Finset (Fin n)) (j : Fin n) (p q ξ η : Mom d), ‖cellOp J j p q ξ η‖ ≤ M)
    (J : Finset (Fin n)) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d) :
    ‖singInt J (halfCellAmplitude z β γ)‖ ≤
      ((2*max 1 (Real.sqrt d)+5)^(2*d))^n*M^n*
        ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖)))*halfLinkFirstMomentConstant d^(2*n)) := by
  have hF := (halfCellAmplitude_fourier_setup hn z β γ).1
  rw [singInt_halfCellAmplitude_eq hd hn]
  calc
    _ ≤ ∑ pq ∈ halfCellOrdinaryCells z, ‖∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        fourierW (halfCellAmplitude z β γ) τ.1 τ.2 *
          ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)‖ := norm_sum_le _ _
    _ ≤ ∑ _pq ∈ halfCellOrdinaryCells z, M^n*∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        ‖fourierW (halfCellAmplitude z β γ) τ.1 τ.2‖ := by
      apply sum_le_sum
      intro pq _hpq
      apply (norm_integral_le_integral_norm _).trans
      rw [← integral_const_mul]
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) (hF.norm.const_mul _)
      apply ae_of_all
      intro τ
      dsimp only
      rw [norm_mul,mul_comm (M^n)]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ∏ j, ‖cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)‖ := norm_prod_le _ _
        _ ≤ ∏ _j : Fin n, M := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hb J j _ _ _ _)
        _ = _ := by simp
    _ = ((halfCellOrdinaryCells z).card:ℝ)*(M^n*∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        ‖fourierW (halfCellAmplitude z β γ) τ.1 τ.2‖) := by simp
    _ ≤ _ := by
      have hmass := integral_norm_fourierW_halfCellAmplitude_le hn z β γ
      have hcount := card_halfCellOrdinaryCells_le z
      have hh := mul_le_mul hcount (mul_le_mul_of_nonneg_left hmass (pow_nonneg hM n))
        (mul_nonneg (pow_nonneg hM n) (integral_nonneg (fun _ => norm_nonneg _))) (by positivity)
      simpa only [mul_assoc] using hh

end WaveTurbulence.RegAsymp
