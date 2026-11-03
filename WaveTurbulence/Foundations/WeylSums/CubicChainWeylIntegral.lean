/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicYoungWindow
public import WaveTurbulence.Foundations.WeylSums.WeylSymmetricMoment
public import WaveTurbulence.Foundations.WeylSums.TimeSquareScaling

/-! # Integrated Weyl majorant for the cubic chain -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- The cubic-chain majorant gains `T^(2/3)` because one Weyl moment is
localized away from the zero rational arc. -/
theorem exists_cubicChain_weyl_integral_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M A T : ℝ, 2 ≤ M → 1/M ≤ A → 0 ≤ T → T ≤ 1/4 →
      IntegrableOn (fun xy : ℝ × ℝ => weylSupremum M xy.1^d*
        weylSupremum M xy.2^d*weylSupremum M (xy.1+xy.2)^d) (timeSquareWindow A T) ∧
      (∫ xy : ℝ × ℝ in timeSquareWindow A T, weylSupremum M xy.1^d*
        weylSupremum M xy.2^d*weylSupremum M (xy.1+xy.2)^d) ≤
        C*M^(3*(d : ℝ)-4)*T^((2 : ℝ)/3) := by
  let p : ℝ := 3*(d : ℝ)/2
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 4 < p := by dsimp [p]; linarith
  obtain ⟨C₁,hC₁,_,hb₁⟩ := weyl_moment_bounds p hp
  obtain ⟨C₂,hC₂,hb₂⟩ := exists_weyl_symmetric_moment_bound p hp
  obtain ⟨C₀,hC₀,hi₀⟩ := exists_weylSupremum_local_integral_bound
  let K := C₁+C₂
  have hK : 0 < K := add_pos hC₁ hC₂
  refine ⟨2*K^2,by positivity,?_⟩
  intro M A T hM hA hT hTsmall
  have hMp : 0 < M := by linarith
  let u := fun t : ℝ => weylSupremum M t^d
  let g := fun t : ℝ => weylSupremum M t^p
  let H := K*M^(p-2)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hgn (t : ℝ) : 0 ≤ g t := Real.rpow_nonneg (weylSupremum_nonneg hMp t) _
  have hpow (t : ℝ) : u t^((3 : ℝ)/2) = g t := by
    dsimp [u,g]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (weylSupremum_nonneg hMp t)]
    congr 1
    dsimp [p]
    ring
  have hiRaw : IntegrableOn g {t : ℝ | 1/M ≤ |t| ∧ |t| ≤ T} :=
    (hi₀ M p T hM hp hT).1
  have hiLocal : IntegrableOn g {t : ℝ | A ≤ |t| ∧ |t| ≤ T} :=
    hiRaw.mono_set (fun t ht => ⟨hA.trans ht.1,ht.2⟩)
  have hiSym : IntegrableOn g {t : ℝ | |t| ≤ 1/2} := (hb₂ M (by linarith)).1
  have hiGlobal : IntegrableOn g {t : ℝ | |t| ≤ 2*T} :=
    hiSym.mono_set (fun t ht => (show |t| ≤ 2*T from ht).trans (by linarith only [hTsmall]))
  have hbLocal : (∫ t in {t : ℝ | A ≤ |t| ∧ |t| ≤ T}, g t) ≤ H*T := by
    calc
      _ ≤ ∫ t in {t : ℝ | 1/M ≤ |t| ∧ |t| ≤ T}, g t :=
        setIntegral_mono_set hiRaw (Filter.Eventually.of_forall hgn)
          (Filter.Eventually.of_forall (fun t ht => ⟨hA.trans ht.1,ht.2⟩))
      _ ≤ C₁*M^(p-2)*T := hb₁ M T hM hT
      _ ≤ H*T := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (by positivity)) hT
  have hbGlobal : (∫ t in {t : ℝ | |t| ≤ 2*T}, g t) ≤ H := by
    calc
      _ ≤ ∫ t in {t : ℝ | |t| ≤ 1/2}, g t := setIntegral_mono_set hiSym
        (Filter.Eventually.of_forall hgn) (Filter.Eventually.of_forall (fun t ht => (show |t| ≤ 2*T from ht).trans (by linarith only [hTsmall])))
      _ ≤ C₂*M^(p-2) := (hb₂ M (by linarith)).2
      _ ≤ H := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (by positivity)
  have hil : IntegrableOn (fun t => u t^((3 : ℝ)/2)) {t : ℝ | A ≤ |t| ∧ |t| ≤ T} := by
    simpa only [hpow] using hiLocal
  have hig : IntegrableOn (fun t => u t^((3 : ℝ)/2)) {t : ℝ | |t| ≤ 2*T} := by
    simpa only [hpow] using hiGlobal
  obtain ⟨hi,hb⟩ := integral_triple_add_window_le u ((measurable_weylSupremum hMp).pow_const d)
    (fun t => pow_nonneg (weylSupremum_nonneg hMp t) d) A T hT hil hig
  refine ⟨hi,?_⟩
  simp_rw [hpow] at hb
  have hloc := Real.rpow_le_rpow (integral_nonneg hgn) hbLocal (by norm_num : (0 : ℝ) ≤ 2/3)
  have hglob := Real.rpow_le_rpow (integral_nonneg hgn) hbGlobal (by norm_num : (0 : ℝ) ≤ 2/3)
  have hprod : 2*(∫ t in {t : ℝ | A ≤ |t| ∧ |t| ≤ T}, g t)^((2 : ℝ)/3)*
      (∫ t in {t : ℝ | |t| ≤ 2*T}, g t)^((2 : ℝ)/3)*
      (∫ t in {t : ℝ | |t| ≤ 2*T}, g t)^((2 : ℝ)/3) ≤
      2*(H*T)^((2 : ℝ)/3)*H^((2 : ℝ)/3)*H^((2 : ℝ)/3) := by
    have hgn0 : 0 ≤ (∫ t in {t : ℝ | |t| ≤ 2*T}, g t)^((2 : ℝ)/3) :=
      Real.rpow_nonneg (integral_nonneg hgn) _
    have hHT0 : 0 ≤ 2*(H*T)^((2 : ℝ)/3) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (mul_nonneg hH hT) _)
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hloc (by norm_num)) hglob hgn0 hHT0)
      hglob hgn0 (mul_nonneg hHT0 (Real.rpow_nonneg hH _))

  have hHpos : 0 < H := by dsimp [H]; positivity
  have halg : 2*(H*T)^((2 : ℝ)/3)*H^((2 : ℝ)/3)*H^((2 : ℝ)/3) =
      (2*K^2)*M^(3*(d : ℝ)-4)*T^((2 : ℝ)/3) := by
    rw [Real.mul_rpow hH hT]
    calc
      _ = 2*(H^((2 : ℝ)/3)*H^((2 : ℝ)/3)*H^((2 : ℝ)/3))*T^((2 : ℝ)/3) := by ring
      _ = 2*H^2*T^((2 : ℝ)/3) := by rw [← Real.rpow_add hHpos, ← Real.rpow_add hHpos]; norm_num
      _ = _ := by
        dsimp [H]
        rw [mul_pow, ← Real.rpow_two (M^(p-2)), ← Real.rpow_mul hMp.le]
        have heq : (p-2)*(2 : ℝ) = 3*(d : ℝ)-4 := by dsimp [p]; ring
        rw [heq]
        ring
  exact hb.trans (hprod.trans_eq halg)

end WaveTurbulence.WeylSums
