/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicStarMinIntegral

/-! # The full-square Weyl minimum, including the zero/zero contribution -/

public section
open MeasureTheory Set
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

/-- Split the actual minimum into all four zero/nonzero arc combinations. -/
theorem min_add_add_le {u v w z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hz : 0 ≤ z) :
    min (u+v) (w+z) ≤ min u w+min u z+min v w+min v z := by
  have h₁ := min_add_le_add_min hw hu hv
  have h₂ := min_add_le_add_min hz hu hv
  have h₃ := min_add_le_add_min (add_nonneg hu hv) hw hz
  rw [min_comm w u,min_comm w v] at h₁
  rw [min_comm z u,min_comm z v] at h₂
  rw [min_comm w (u+v)] at h₁
  rw [min_comm z (u+v)] at h₂
  linarith only [h₁,h₂,h₃]

/-- The moment reduction on a full square adds exactly the zero/zero term
absent from the minor-arc estimate. All moments are of actual Weyl functions. -/
theorem integral_full_minimum_le (M T a : ℝ) (hM : 0 < M)
    (ha : 0 < a) (ha3 : a < 3)
    (hib : IntegrableOn (fun t => nonzeroWeylPart M t^((3 : ℝ)/2)) {t : ℝ | |t| ≤ T})
    (hia : IntegrableOn (fun t => nonzeroWeylPart M t^a) {t : ℝ | |t| ≤ T})
    (hiz : IntegrableOn (fun t => zeroWeylPart M t^(3-a)) {t : ℝ | |t| ≤ T})
    (hij : IntegrableOn (fun t => zeroWeylPart M t^((3 : ℝ)/2)) {t : ℝ | |t| ≤ T}) :
    IntegrableOn (fun xy : ℝ × ℝ => min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3))
      ({t : ℝ | |t| ≤ T} ×ˢ {t : ℝ | |t| ≤ T}) ∧
    (∫ xy : ℝ × ℝ in ({t : ℝ | |t| ≤ T} ×ˢ {t : ℝ | |t| ≤ T}),
      min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3)) ≤
      (∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^((3 : ℝ)/2))^2+
      2*(∫ t in {t : ℝ | |t| ≤ T}, nonzeroWeylPart M t^a)*
        (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^(3-a))+
      (∫ t in {t : ℝ | |t| ≤ T}, zeroWeylPart M t^((3 : ℝ)/2))^2 := by
  let W := {t : ℝ | |t| ≤ T}
  have hW : MeasurableSet W := by dsimp only [W]; measurability
  let nb := W.indicator (fun t => nonzeroWeylPart M t^((3 : ℝ)/2))
  let na := W.indicator (fun t => nonzeroWeylPart M t^a)
  let za := W.indicator (fun t => zeroWeylPart M t^(3-a))
  let zb := W.indicator (fun t => zeroWeylPart M t^((3 : ℝ)/2))
  have hinb : Integrable nb := hib.integrable_indicator hW
  have hina : Integrable na := hia.integrable_indicator hW
  have hiza : Integrable za := hiz.integrable_indicator hW
  have hizb : Integrable zb := hij.integrable_indicator hW
  let F := fun xy : ℝ × ℝ => nb xy.1*nb xy.2+na xy.1*za xy.2+
    za xy.1*na xy.2+zb xy.1*zb xy.2
  have hiF : Integrable F := (((hinb.mul_prod hinb).add (hina.mul_prod hiza)).add
    (hiza.mul_prod hina)).add (hizb.mul_prod hizb)
  let f := fun xy : ℝ × ℝ => min (normalizedWeyl M xy.1^3) (normalizedWeyl M xy.2^3)
  have hm : Measurable f := ((measurable_normalizedWeyl hM).comp measurable_fst |>.pow_const 3).min
    ((measurable_normalizedWeyl hM).comp measurable_snd |>.pow_const 3)
  have hfn (xy : ℝ × ℝ) : 0 ≤ f xy := le_min (pow_nonneg (normalizedWeyl_nonneg hM _) 3)
    (pow_nonneg (normalizedWeyl_nonneg hM _) 3)
  have hn (t : ℝ) : 0 ≤ nb t ∧ 0 ≤ na t ∧ 0 ≤ za t ∧ 0 ≤ zb t := by
    exact ⟨indicator_nonneg (fun _ _ => Real.rpow_nonneg (nonzeroWeylPart_nonneg hM _) _) _,
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (nonzeroWeylPart_nonneg hM _) _) _,
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (zeroWeylPart_nonneg hM _) _) _,
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (zeroWeylPart_nonneg hM _) _) _⟩
  have hmajor (xy : ℝ × ℝ) : (W ×ˢ W).indicator f xy ≤ F xy := by
    by_cases hxy : xy ∈ W ×ˢ W
    · rw [indicator_of_mem hxy]
      dsimp only [F,nb,na,za,zb]
      rw [indicator_of_mem hxy.1,indicator_of_mem hxy.2,indicator_of_mem hxy.1,
        indicator_of_mem hxy.2,indicator_of_mem hxy.1,indicator_of_mem hxy.2,
        indicator_of_mem hxy.1,indicator_of_mem hxy.2]
      dsimp only [f]
      rw [normalizedWeyl_pow_split M xy.1 (by norm_num : 3 ≠ 0),
        normalizedWeyl_pow_split M xy.2 (by norm_num : 3 ≠ 0)]
      have hsplit := min_add_add_le
        (pow_nonneg (nonzeroWeylPart_nonneg hM xy.1) 3)
        (pow_nonneg (zeroWeylPart_nonneg hM xy.1) 3)
        (pow_nonneg (nonzeroWeylPart_nonneg hM xy.2) 3)
        (pow_nonneg (zeroWeylPart_nonneg hM xy.2) 3)
      have hprod (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
          min (u^3) (v^3) ≤ u^((3 : ℝ)/2)*v^((3 : ℝ)/2) := by
        simpa only [Real.rpow_ofNat,show (3 : ℝ)-3/2 = 3/2 by norm_num] using
          min_rpow_le_rpow_mul hu hv (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (3 : ℝ)/2 < 3)
      have hnz (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
          min (u^3) (v^3) ≤ u^a*v^(3-a) := by
        simpa only [Real.rpow_ofNat] using min_rpow_le_rpow_mul hu hv ha ha3
      have h₁ := hprod _ _ (nonzeroWeylPart_nonneg hM xy.1) (nonzeroWeylPart_nonneg hM xy.2)
      have h₂ := hnz _ _ (nonzeroWeylPart_nonneg hM xy.1) (zeroWeylPart_nonneg hM xy.2)
      have h₃ := hnz _ _ (nonzeroWeylPart_nonneg hM xy.2) (zeroWeylPart_nonneg hM xy.1)
      have h₄ := hprod _ _ (zeroWeylPart_nonneg hM xy.1) (zeroWeylPart_nonneg hM xy.2)
      rw [min_comm] at h₃
      nlinarith only [hsplit,h₁,h₂,h₃,h₄]
    · rw [indicator_of_notMem hxy]
      dsimp only [F]
      exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg (hn _).1 (hn _).1)
        (mul_nonneg (hn _).2.1 (hn _).2.2.1))
        (mul_nonneg (hn _).2.2.1 (hn _).2.1)) (mul_nonneg (hn _).2.2.2 (hn _).2.2.2)
  have hi : Integrable ((W ×ˢ W).indicator f) := hiF.mono'
    (hm.indicator (hW.prod hW)).aestronglyMeasurable (by
      filter_upwards [] with xy
      rw [Real.norm_of_nonneg (indicator_nonneg (fun xy _ => hfn xy) xy)]
      exact hmajor xy)
  refine ⟨(integrable_indicator_iff (hW.prod hW)).mp hi,?_⟩
  have hb := integral_mono_ae hi hiF (Filter.Eventually.of_forall hmajor)
  rw [integral_indicator (hW.prod hW)] at hb
  have hF : (∫ xy, F xy) = (∫ t, nb t)^2+2*(∫ t, na t)*(∫ t, za t)+(∫ t, zb t)^2 := by
    dsimp only [F]
    change (∫ xy : ℝ × ℝ, nb xy.1*nb xy.2+na xy.1*za xy.2+
      za xy.1*na xy.2+zb xy.1*zb xy.2 ∂((volume : Measure ℝ).prod volume)) = _
    have h₁ := integral_add (((hinb.mul_prod hinb).add (hina.mul_prod hiza)).add (hiza.mul_prod hina)) (hizb.mul_prod hizb)
    have h₂ := integral_add ((hinb.mul_prod hinb).add (hina.mul_prod hiza)) (hiza.mul_prod hina)
    have h₃ := integral_add (hinb.mul_prod hinb) (hina.mul_prod hiza)
    simp only [Pi.add_apply] at h₁ h₂ h₃
    rw [h₁,h₂,h₃]
    rw [integral_prod_mul,integral_prod_mul,integral_prod_mul,integral_prod_mul]
    ring
  rw [hF] at hb
  simpa only [nb,na,za,zb,integral_indicator hW] using hb

end WaveTurbulence.CountLemmas
