/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.EvalGate
/-! AMEND6' (design P*): the gate bound for a recursion evaluation `evalOps (evalV ..) os h0 x`:
`‖..‖ <= T^len * B₀^(N+R) * gain` with `T = 2M/|lam|` bounding `sum_m |w_m / lam|`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset CentralDiff
open scoped Classical ENNReal

theorem sum_abs_cw_le (M : ℕ) (lam : ℝ) :
    ∑ m ∈ Finset.range (2 * M + 1), |cw M m / lam| ≤ (2 * M + 1) / |lam| := by
  have h1 : ∀ m ∈ Finset.range (2 * M + 1), |cw M m / lam| ≤ 1 / |lam| := by
    intro m _
    rw [abs_div]
    refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hm : m = M
    · simp [cw, hm]
    · refine (abs_cw_le M m hm).trans ?_
      have : (1 : ℝ) ≤ |(m : ℝ) - M| := by
        have : (m : ℤ) ≠ M := by exact_mod_cast hm
        have h2 : (1 : ℤ) ≤ |(m : ℤ) - M| := Int.one_le_abs (sub_ne_zero.mpr this)
        have h3 : (1 : ℝ) ≤ |((m : ℤ) - M : ℤ)| := by exact_mod_cast h2
        simpa using h3
      exact (div_le_one (by linarith)).mpr this
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  rw [mul_one_div]


theorem evalOps_gate_bound (C₀ : ℕ) (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L) (hd : 1 ≤ P.d)
    (hgate : Stage1ReductionAt C₀ P)
    {p R N : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) (hN1 : 1 ≤ N)
    (hN : N ≤ P.N (p + 1) ^ 4) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (hcl : TwistClosed p A) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hplain : ∀ LG ∈ A, LG.garden.IsPlain) (base : Mom P.d)
    (M : ℕ) (lam : ℝ) (T : ℝ) (hT1 : 1 ≤ T) (hT : (2 * M + 1) / |lam| ≤ T)
    (xs : ℝ) (hxs : 0 ≤ xs) (hxM : ∀ m ∈ Finset.range (2 * M + 1), |lam * ((m : ℝ) - M)| ≤ xs)
    (Dmax : ℕ) (B₀ : NNReal) (hB₀ : 0 < (B₀ : ℝ)) (Lops : ℕ)
    (os : List (TOp P.d (2 * R))) (hlen : os.length ≤ Lops) (hdc : dcnt os ≤ Dmax)
    (h0 : TProf P.d (2 * R)) (u c : ℝ) (hu : 0 ≤ u) (hc : 0 ≤ c)
    (hI : Inv p (40 * P.d) (40 * P.d) os u c h0)
    (hB : c + u * ((1 + xs * (2 * (P.d : ℝ)) ^ (40 * P.d + Dmax)) ^ Lops - 1) ≤ (B₀ : ℝ)) :
    ‖evalOps (evalV P A tt roots) M lam os h0 base‖ ≤ T ^ Lops * ((B₀ : ℝ) ^ (N + R) *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))))) := by
  rw [evalOps_apply (Y := ℂ)]
  have hd1 : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  set κ : ℝ := (2 * (P.d : ℝ)) ^ (40 * P.d + Dmax) with hκ
  have hnorm := evalOps_norm_le hd (fun g => evalV P A tt roots g base) M lam (p := p) (A := 40 * P.d)
    (B := 40 * P.d) xs κ (B₀ : ℝ) ((B₀ : ℝ) ^ (N + R) *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))))
    hxs hxM (40 * P.d + Dmax) (fun a ha => by
      have h2 : (1 : ℝ) ≤ 2 * P.d := by linarith
      constructor
      · calc (P.d : ℝ) ^ a ≤ (2 * (P.d : ℝ)) ^ a := pow_le_pow_left₀ (by positivity) (by linarith) a
          _ ≤ _ := pow_le_pow_right₀ h2 ha
      · calc (2 : ℝ) ^ a * (P.d : ℝ) ^ a = (2 * (P.d : ℝ)) ^ a := by rw [mul_pow]
          _ ≤ _ := pow_le_pow_right₀ h2 ha)
    (fun g hg => evalV_gate_bound C₀ P hs hcoarse hfourier hcount habs hlog hd hgate hp hR hRmax hN1 hN A hA hcl
      tt htt base roots hplain g B₀ hB₀ hg)
    os h0 u c hu hc (by omega) hI (by
      have h2 : (1 : ℝ) ≤ 1 + xs * κ := by
        have : 0 ≤ xs * κ := mul_nonneg hxs (by positivity)
        linarith
      have := pow_le_pow_right₀ h2 hlen
      nlinarith)
  refine hnorm.trans ?_
  have hS : ∑ m ∈ Finset.range (2 * M + 1), |cw M m / lam| ≤ T := (sum_abs_cw_le M lam).trans hT
  have hS0 : 0 ≤ ∑ m ∈ Finset.range (2 * M + 1), |cw M m / lam| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hG0 : 0 ≤ (B₀ : ℝ) ^ (N + R) *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
    have hL0 : 0 < P.L := by linarith [hs.L_ge]
    have := hs.delta_pos
    positivity
  refine mul_le_mul_of_nonneg_right ?_ hG0
  calc _ ≤ T ^ os.length := pow_le_pow_left₀ hS0 hS _
    _ ≤ T ^ Lops := pow_le_pow_right₀ hT1 hlen

end WaveTurbulence.LGSpine
