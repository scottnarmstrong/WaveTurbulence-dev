/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.Spine.RestrictionNormCalculus
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! Consume the literal separated approximation statement in the order-zero mixed norm.
No continuity of arbitrary approximation representatives is assumed. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal Classical

theorem leafwiseSeparated_norm00_le (P : WTParams) (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ)
    (hη : P.η ≤ 1 / 2) (n W : ℕ) (B : Set (Fin 2 → ℝ))
    (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (cost : ℝ) (hcost : 0 < cost)
    (hsep : LeafwiseSeparated P n W B f cost) :
    mixedRestrictionNorm00 (V := Mom P.d) P.η B Set.univ (fun t k => f t k) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2 * cost) := by
  obtain ⟨m, J, M, hm, hf, hJ, hM⟩ := hsep
  let C : ℝ := P.C₁ * P.C₁ ^ n
  have hCp : 0 < C := mul_pos (lt_of_lt_of_le zero_lt_one hC₁)
    (pow_pos (lt_of_lt_of_le zero_lt_one hC₁) _)
  have hCM : 0 < C * cost := mul_pos hCp hcost
  have hδCp : 0 < P.δ ^ n * (C * cost) := mul_pos (pow_pos hδ _) hCM
  have hMbound : ∀ i k, ‖(M i k : ℂ)‖ ≤ C * cost := by
    intro i k
    have h := SNorm_pointwise (fun k => (M i k : ℂ)) (C * cost) hCM.le (hM i) k
    exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_jbr k))).trans h
  let G : Fin m → (Fin 2 → ℝ) → Mom P.d → ℂ :=
    fun i ts k => J i ts * ((P.δ ^ n : ℂ) * (M i k : ℂ))
  have hagree : ∀ ts ∈ B, ∀ k ∈ (Set.univ : Set (Mom P.d)), f ts k = ∑ i, G i ts k := by
    intro ts hts k _
    rw [hf ts hts k]
    apply sum_congr rfl
    intro i _
    dsimp only [G]
    ring
  rw [mixedRestrictionNorm00_congr_ambient P.η B Set.univ f (fun ts k => ∑ i, G i ts k) hagree]
  apply (mixedRestrictionNorm00_finsetSum_le P.η B Set.univ Finset.univ G).trans
  have hterm : ∀ i, mixedRestrictionNorm00 (V := Mom P.d) P.η B Set.univ (fun ts k => G i ts k) ≤
      ENNReal.ofReal (P.δ ^ n * (C * cost) * C) := by
    intro i
    have hscaled : ∀ k, ‖(P.δ ^ n : ℂ) * (M i k : ℂ)‖ ≤ P.δ ^ n * (C * cost) := by
      intro k
      calc
        _ = P.δ ^ n * ‖(M i k : ℂ)‖ := by simp [norm_mul, norm_pow, Complex.norm_real, abs_of_pos hδ]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hMbound i k) (pow_nonneg hδ.le _)
    have hJ' : mixedRestrictionNorm00 (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J i ts) ≤
        ENNReal.ofReal C := by
      have hJi := hJ i
      rw [NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (V := Unit)
        (1 - P.η) B Set.univ (fun ts (_ : Unit) => J i ts)] at hJi
      exact hJi
    have hJη := (mixedRestrictionNorm00_mono_time (by linarith : P.η ≤ 1 - P.η)
      B Set.univ (fun ts (_ : Unit) => J i ts)).trans hJ'
    have h := (mixedRestrictionNorm00_separated_le P.η B Set.univ (J i)
      (fun k => (P.δ ^ n : ℂ) * (M i k : ℂ)) hδCp hscaled).trans
      (mul_le_mul_right hJη (ENNReal.ofReal (P.δ ^ n * (C * cost))))
    simpa only [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hδ.le _) hCM.le)] using h
  calc
    _ ≤ ∑ _i : Fin m, ENNReal.ofReal (P.δ ^ n * (C * cost) * C) := sum_le_sum fun i _ => hterm i
    _ = ENNReal.ofReal ((m : ℝ) * (P.δ ^ n * (C * cost) * C)) := by
      rw [sum_const, card_univ, Fintype.card_fin]
      simpa only [nsmul_eq_mul] using
        (ENNReal.ofReal_nsmul (n := m) (x := P.δ ^ n * (C * cost) * C)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hm' : (m : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hm
      have h := mul_le_mul_of_nonneg_right hm' (by positivity : 0 ≤ P.δ ^ n * (C * cost) * C)
      dsimp only [C] at *
      exact h.trans_eq (by ring))

end WaveTurbulence.LGSpine
