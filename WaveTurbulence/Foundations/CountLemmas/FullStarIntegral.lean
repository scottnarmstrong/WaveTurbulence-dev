/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.FullSquare
public import WaveTurbulence.Foundations.CountLemmas.FullStarMoment
public import WaveTurbulence.Foundations.WeylSums.CubicStarPointwise
public import WaveTurbulence.Foundations.CountLemmas.CubicFrequencies

/-! # Full-square cubic-star integral before substituting the bandwidth -/

public section
open MeasureTheory Set
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

/-- The full-square cubic-star estimate retains all three rational-arc
contributions. The dimension reduction uses the proved pointwise Weyl cap. -/
theorem exists_full_star_integral_bound (d : ℕ) (hd : 3 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L B : ℝ, 2 ≤ L → 0 < B → B ≤ 4*L^2 →
      ∀ a b c : Mom d, ∀ ξ ζ ω : ℝ × ℝ → Mom d,
      Continuous ξ → Continuous ζ → Continuous ω →
      IntegrableOn (fun ts : ℝ × ℝ => ‖cubicLatticeSum L ts.1 ts.2 true a b c (ξ ts) (ζ ts) (ω ts)‖)
        ({t : ℝ | |t| ≤ B} ×ˢ {t : ℝ | |t| ≤ B}) ∧
      (∫ ts : ℝ × ℝ in ({t : ℝ | |t| ≤ B} ×ˢ {t : ℝ | |t| ≤ B}),
        ‖cubicLatticeSum L ts.1 ts.2 true a b c (ξ ts) (ζ ts) (ω ts)‖) ≤
        C*L^(3*(d : ℝ)+1)*((12*L)^(2*ε)*(B/(4*L^2))^2+
          (12*L)^(-1+4*ε)*(B/(4*L^2))+(12*L)^(-1 : ℝ)) := by
  obtain ⟨C₀,hC₀,hpoint⟩ := exists_cubicStar_pointwise_bound
  obtain ⟨C₁,hC₁,hint⟩ := exists_full_star_moment_bound ε hε hε1
  let C := C₀^d*300^(d-3)*16*C₁
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro L B hL hB hBL a b c ξ ζ ω hξ hζ hω
  have hLp : 0 < L := by linarith only [hL]
  let J := 4*L^2
  let M := 12*L
  let T := B/J
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hM : 2 ≤ M := by dsimp only [M]; linarith only [hL]
  have hMp : 0 < M := by linarith only [hM]
  have hT : 0 < T := div_pos hB hJ
  have hT1 : T ≤ 1 := (div_le_one hJ).mpr hBL
  let f := fun xy : ℝ × ℝ => min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3)
  obtain ⟨hi,hb⟩ := hint M T hM hT hT1
  have his := integrableOn_fullSquare_div f B hJ hi
  let A := C₀^d*L^(2*d)*(25*M)^(d-3)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hpoint' (ts : ℝ × ℝ) :
      ‖cubicLatticeSum L ts.1 ts.2 true a b c (ξ ts) (ζ ts) (ω ts)‖ ≤ A*f (ts.1/J,ts.2/J) := by
    have hp := hpoint d L (by linarith only [hL]) ts.1 ts.2 a b c (ξ ts) (ζ ts) (ω ts)
    have hcap := min_pow_le_cap_mul_cube
      (normalizedWeyl_nonneg hMp (ts.1/J)) (normalizedWeyl_nonneg hMp (ts.2/J))
      (normalizedWeyl_le_cap (by linarith only [hM]) _) (normalizedWeyl_le_cap (by linarith only [hM]) _) hd
    exact hp.trans ((mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ C₀^d*L^(2*d))).trans_eq (by dsimp only [A,f]; ring))
  have hic : IntegrableOn (fun ts : ℝ × ℝ => ‖cubicLatticeSum L ts.1 ts.2 true a b c (ξ ts) (ζ ts) (ω ts)‖)
      ({t : ℝ | |t| ≤ B} ×ˢ {t : ℝ | |t| ≤ B}) := by
    apply (his.const_mul A).mono'
      (continuous_cubic_varying_frequencies hLp true a b c ξ ζ ω hξ hζ hω).norm.aestronglyMeasurable
    filter_upwards [] with ts
    rw [norm_norm]
    exact hpoint' ts
  refine ⟨hic,?_⟩
  have hscale : A*J^2*C₁ = C*L^(3*(d : ℝ)+1) := by
    dsimp only [A,J,M,C]
    rw [show 25*(12*L) = 300*L by ring,mul_pow]
    have hd' : 2*d+(d-3)+4 = 3*d+1 := by omega
    have hpow : L^(2*d)*L^(d-3)*L^4 = L^(3*d+1) := by rw [← pow_add,← pow_add,hd']
    have hrpow : L^(3*(d : ℝ)+1) = L^(3*d+1) := by
      norm_cast
    rw [hrpow]
    calc
      _ = (C₀^d*300^(d-3)*16*C₁)*(L^(2*d)*L^(d-3)*L^4) := by ring
      _ = _ := by rw [hpow]
  calc
    _ ≤ ∫ ts in ({t : ℝ | |t| ≤ B} ×ˢ {t : ℝ | |t| ≤ B}), A*f (ts.1/J,ts.2/J) :=
      integral_mono_ae hic (his.const_mul A) (Filter.Eventually.of_forall hpoint')
    _ = A*(J^2*∫ xy in ({t : ℝ | |t| ≤ T} ×ˢ {t : ℝ | |t| ≤ T}), f xy) := by
      rw [integral_const_mul,integral_fullSquare_div f B hJ]
    _ ≤ A*(J^2*(C₁*(M^(2*ε)*T^2+M^(-1+4*ε)*T+M^(-1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (sq_nonneg J)) hA
    _ = _ := by
      calc
        _ = (A*J^2*C₁)*(M^(2*ε)*T^2+M^(-1+4*ε)*T+M^(-1 : ℝ)) := by ring
        _ = _ := by rw [hscale]

end WaveTurbulence.CountLemmas
