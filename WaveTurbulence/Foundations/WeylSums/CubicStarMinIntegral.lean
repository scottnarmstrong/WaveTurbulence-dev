/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.NormalizedWeyl
public import WaveTurbulence.Foundations.WeylSums.CubicMinima
public import WaveTurbulence.Foundations.WeylSums.TimeSquareScaling
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The product-moment reduction for the shared-vertex phase -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- The minor-arc minimum is reduced to a nonzero/nonzero product and a
nonzero/zero product. The three moments on the right are supplied by the
proved Weyl moment estimates. -/
theorem integral_normalizedWeyl_min_le_moments (d : ℕ) (hd : 3 ≤ d)
    (M A T a : ℝ) (hM : 0 < M) (hA : 1/M < A) (ha : 0 < a) (had : a < (d : ℝ))
    (hib : IntegrableOn (fun t => nonzeroWeylPart M t^((d : ℝ)/2)) {t : ℝ | |t| ≤ T})
    (hia : IntegrableOn (fun t => nonzeroWeylPart M t^a) {t : ℝ | |t| ≤ T})
    (hiz : IntegrableOn (fun t => zeroWeylPart M t^((d : ℝ)-a)) {t : ℝ | |t| ≤ T}) :
    IntegrableOn (fun xy : ℝ × ℝ => min (normalizedWeyl M xy.1^d) (normalizedWeyl M xy.2^d))
      (timeSquareWindow A T) ∧
    (∫ xy : ℝ × ℝ in timeSquareWindow A T,
      min (normalizedWeyl M xy.1^d) (normalizedWeyl M xy.2^d)) ≤
      2*(∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^((d : ℝ)/2))^2+
      2*(∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^a)*
        (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^((d : ℝ)-a)) := by
  let W := {t : ℝ | |t| ≤ T}
  let nb := W.indicator (fun t => nonzeroWeylPart M t^((d : ℝ)/2))
  let na := W.indicator (fun t => nonzeroWeylPart M t^a)
  let zk := W.indicator (fun t => zeroWeylPart M t^((d : ℝ)-a))
  let D := timeSquareWindow A T
  let f := fun xy : ℝ × ℝ => min (normalizedWeyl M xy.1^d) (normalizedWeyl M xy.2^d)
  have hW : MeasurableSet W := by dsimp [W]; measurability
  have hD : MeasurableSet D := measurableSet_timeSquareWindow A T
  have hinb : Integrable nb := hib.integrable_indicator hW
  have hina : Integrable na := hia.integrable_indicator hW
  have hizk : Integrable zk := hiz.integrable_indicator hW
  have hnb (t : ℝ) : 0 ≤ nb t := indicator_nonneg
    (fun t ht => Real.rpow_nonneg (nonzeroWeylPart_nonneg hM t) _) t
  have hna (t : ℝ) : 0 ≤ na t := indicator_nonneg
    (fun t ht => Real.rpow_nonneg (nonzeroWeylPart_nonneg hM t) _) t
  have hzk (t : ℝ) : 0 ≤ zk t := indicator_nonneg
    (fun t ht => Real.rpow_nonneg (zeroWeylPart_nonneg hM t) _) t
  have hnn (x y : ℝ) : min (nonzeroWeylPart M x^d) (nonzeroWeylPart M y^d) ≤
      nonzeroWeylPart M x^((d : ℝ)/2)*nonzeroWeylPart M y^((d : ℝ)/2) := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hh := min_rpow_le_rpow_mul (nonzeroWeylPart_nonneg hM x) (nonzeroWeylPart_nonneg hM y)
      (by linarith : 0 < (d : ℝ)/2) (by linarith : (d : ℝ)/2 < d)
    simpa only [Real.rpow_natCast,show (d : ℝ)-(d : ℝ)/2 = (d : ℝ)/2 by ring] using hh
  have hnz (x y : ℝ) : min (nonzeroWeylPart M x^d) (zeroWeylPart M y^d) ≤
      nonzeroWeylPart M x^a*zeroWeylPart M y^((d : ℝ)-a) := by
    simpa only [Real.rpow_natCast] using
      min_rpow_le_rpow_mul (nonzeroWeylPart_nonneg hM x) (zeroWeylPart_nonneg hM y) ha had
  have hlocal (x y : ℝ) (hx : A ≤ |x|) : f (x,y) ≤
      nonzeroWeylPart M x^((d : ℝ)/2)*nonzeroWeylPart M y^((d : ℝ)/2)+
      nonzeroWeylPart M x^a*zeroWeylPart M y^((d : ℝ)-a) := by
    have heq : normalizedWeyl M x = nonzeroWeylPart M x := by
      symm
      apply indicator_of_mem
      change 1/M < |x|
      exact hA.trans_le hx
    dsimp only [f]
    rw [heq,normalizedWeyl_pow_split M y (by omega : d ≠ 0)]
    exact (min_add_le_add_min (pow_nonneg (nonzeroWeylPart_nonneg hM x) d)
      (pow_nonneg (nonzeroWeylPart_nonneg hM y) d) (pow_nonneg (zeroWeylPart_nonneg hM y) d)).trans
      (add_le_add (hnn x y) (hnz x y))
  let F := fun xy : ℝ × ℝ => 2*(nb xy.1*nb xy.2)+na xy.1*zk xy.2+zk xy.1*na xy.2
  have hiF : Integrable F := ((hinb.mul_prod hinb).const_mul 2 |>.add (hina.mul_prod hizk)).add (hizk.mul_prod hina)
  have hm : Measurable f := ((measurable_normalizedWeyl hM).comp measurable_fst |>.pow_const d).min
    ((measurable_normalizedWeyl hM).comp measurable_snd |>.pow_const d)
  have hfn (xy : ℝ × ℝ) : 0 ≤ f xy := le_min (pow_nonneg (normalizedWeyl_nonneg hM _) d)
    (pow_nonneg (normalizedWeyl_nonneg hM _) d)
  have hmajor (xy : ℝ × ℝ) : D.indicator f xy ≤ F xy := by
    have hNN : 0 ≤ nb xy.1*nb xy.2 := mul_nonneg (hnb _) (hnb _)
    have hNZ : 0 ≤ na xy.1*zk xy.2 := mul_nonneg (hna _) (hzk _)
    have hZN : 0 ≤ zk xy.1*na xy.2 := mul_nonneg (hzk _) (hna _)
    by_cases hxy : xy ∈ D
    · rw [indicator_of_mem hxy]
      have hx : xy.1 ∈ W := hxy.2.1
      have hy : xy.2 ∈ W := hxy.2.2
      have hnbx : nb xy.1 = nonzeroWeylPart M xy.1^((d : ℝ)/2) := indicator_of_mem hx _
      have hnby : nb xy.2 = nonzeroWeylPart M xy.2^((d : ℝ)/2) := indicator_of_mem hy _
      have hnax : na xy.1 = nonzeroWeylPart M xy.1^a := indicator_of_mem hx _
      have hnay : na xy.2 = nonzeroWeylPart M xy.2^a := indicator_of_mem hy _
      have hzkx : zk xy.1 = zeroWeylPart M xy.1^((d : ℝ)-a) := indicator_of_mem hx _
      have hzky : zk xy.2 = zeroWeylPart M xy.2^((d : ℝ)-a) := indicator_of_mem hy _
      rcases le_max_iff.mp hxy.1 with hl | hr
      · have hh := hlocal xy.1 xy.2 hl
        rw [← hnbx,← hnby,← hnax,← hzky] at hh
        dsimp only [F]
        linarith only [hh,hNN,hZN]
      · have hh := hlocal xy.2 xy.1 hr
        have hswap : f (xy.2,xy.1) = f xy := min_comm _ _
        rw [hswap,← hnby,← hnbx,← hnay,← hzkx] at hh
        dsimp only [F]
        nlinarith only [hh,hNN,hNZ]
    · rw [indicator_of_notMem hxy]
      dsimp only [F]
      linarith only [hNN,hNZ,hZN]
  have hif : Integrable (D.indicator f) := by
    apply hiF.mono' (hm.indicator hD).aestronglyMeasurable
    filter_upwards [] with xy
    rw [Real.norm_of_nonneg (indicator_nonneg (fun x hx => hfn x) xy)]
    exact hmajor xy
  refine ⟨(integrable_indicator_iff hD).mp hif,?_⟩
  have hb := integral_mono_ae hif hiF (Filter.Eventually.of_forall hmajor)
  rw [integral_indicator hD] at hb
  have hFint : (∫ xy, F xy) = 2*(∫ t, nb t)^2+2*(∫ t, na t)*(∫ t, zk t) := by
    dsimp only [F]
    change (∫ xy : ℝ × ℝ, 2*(nb xy.1*nb xy.2)+na xy.1*zk xy.2+zk xy.1*na xy.2
      ∂((volume : Measure ℝ).prod volume)) = _
    have hadd₁ := integral_add ((hinb.mul_prod hinb).const_mul 2 |>.add (hina.mul_prod hizk)) (hizk.mul_prod hina)
    have hadd₂ := integral_add ((hinb.mul_prod hinb).const_mul 2) (hina.mul_prod hizk)
    simp only [Pi.add_apply] at hadd₁ hadd₂
    rw [hadd₁,hadd₂,integral_const_mul,integral_prod_mul,integral_prod_mul,integral_prod_mul]
    ring
  rw [hFint] at hb
  simpa only [nb,na,zk,integral_indicator hW] using hb

end WaveTurbulence.WeylSums
