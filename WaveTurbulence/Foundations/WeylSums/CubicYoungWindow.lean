/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicYoungReal
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Young's inequality on the two-time minor-arc window -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- The cubic Young reduction with one localized factor. The hypothesis
`A≤max(|x|,|y|)` is covered by the two possible localized coordinates. -/
theorem integral_triple_add_window_le (u : ℝ → ℝ) (hu : Measurable u)
    (hun : ∀ x, 0 ≤ u x) (A T : ℝ) (hT : 0 ≤ T)
    (hil : IntegrableOn (fun x => u x^((3 : ℝ)/2)) {x : ℝ | A ≤ |x| ∧ |x| ≤ T})
    (hig : IntegrableOn (fun x => u x^((3 : ℝ)/2)) {x : ℝ | |x| ≤ 2*T}) :
    IntegrableOn (fun xy : ℝ × ℝ => u xy.1*u xy.2*u (xy.1+xy.2))
      {xy : ℝ × ℝ | A ≤ max |xy.1| |xy.2| ∧ |xy.1| ≤ T ∧ |xy.2| ≤ T} ∧
    (∫ xy : ℝ × ℝ in {xy : ℝ × ℝ | A ≤ max |xy.1| |xy.2| ∧ |xy.1| ≤ T ∧ |xy.2| ≤ T},
      u xy.1*u xy.2*u (xy.1+xy.2)) ≤
      2*(∫ x in {x : ℝ | A ≤ |x| ∧ |x| ≤ T}, u x^((3 : ℝ)/2))^((2 : ℝ)/3)*
      (∫ x in {x : ℝ | |x| ≤ 2*T}, u x^((3 : ℝ)/2))^((2 : ℝ)/3)*
      (∫ x in {x : ℝ | |x| ≤ 2*T}, u x^((3 : ℝ)/2))^((2 : ℝ)/3) := by
  let S := {x : ℝ | A ≤ |x| ∧ |x| ≤ T}
  let V := {x : ℝ | |x| ≤ 2*T}
  let D := {xy : ℝ × ℝ | A ≤ max |xy.1| |xy.2| ∧ |xy.1| ≤ T ∧ |xy.2| ≤ T}
  let l := S.indicator u
  let g := V.indicator u
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hV : MeasurableSet V := by dsimp [V]; measurability
  have hD : MeasurableSet D := by dsimp [D]; measurability
  have hln (x : ℝ) : 0 ≤ l x := by exact indicator_nonneg (fun x hx => hun x) x
  have hgn (x : ℝ) : 0 ≤ g x := by exact indicator_nonneg (fun x hx => hun x) x
  have hpow (E : Set ℝ) : (fun x => (E.indicator u x)^((3 : ℝ)/2)) =
      E.indicator (fun x => u x^((3 : ℝ)/2)) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  have hli : Integrable (fun x => l x^((3 : ℝ)/2)) := by
    rw [show (fun x => l x^((3 : ℝ)/2)) = S.indicator (fun x => u x^((3 : ℝ)/2)) from hpow S]
    exact (integrable_indicator_iff hS).mpr hil
  have hgi : Integrable (fun x => g x^((3 : ℝ)/2)) := by
    rw [show (fun x => g x^((3 : ℝ)/2)) = V.indicator (fun x => u x^((3 : ℝ)/2)) from hpow V]
    exact (integrable_indicator_iff hV).mpr hig
  obtain ⟨hi₁,hb₁⟩ := integral_triple_add_le l g g (hu.indicator hS) (hu.indicator hV) (hu.indicator hV)
    hln hgn hgn hli hgi hgi
  obtain ⟨hi₂,hb₂⟩ := integral_triple_add_le g l g (hu.indicator hV) (hu.indicator hS) (hu.indicator hV)
    hgn hln hgn hgi hli hgi
  let f (xy : ℝ × ℝ) := u xy.1*u xy.2*u (xy.1+xy.2)
  have hfn (xy : ℝ × ℝ) : 0 ≤ f xy := mul_nonneg (mul_nonneg (hun _) (hun _)) (hun _)
  have hm : Measurable f := (hu.comp measurable_fst |>.mul (hu.comp measurable_snd)).mul
    (hu.comp (measurable_fst.add measurable_snd))
  have hmajor (xy : ℝ × ℝ) : D.indicator f xy ≤
      l xy.1*g xy.2*g (xy.1+xy.2)+g xy.1*l xy.2*g (xy.1+xy.2) := by
    by_cases hxy : xy ∈ D
    · have hx : xy.1 ∈ V := by dsimp [V]; linarith only [hxy.2.1,hT]
      have hy : xy.2 ∈ V := by dsimp [V]; linarith only [hxy.2.2,hT]
      have hz : xy.1+xy.2 ∈ V := (abs_add_le _ _).trans (add_le_add hxy.2.1 hxy.2.2) |>.trans_eq (two_mul T).symm
      rw [indicator_of_mem hxy]
      rcases le_max_iff.mp hxy.1 with hl | hr
      · have hxS : xy.1 ∈ S := ⟨hl,hxy.2.1⟩
        have heq : l xy.1*g xy.2*g (xy.1+xy.2) = f xy := by simp [l,g,hxS,hy,hz,f]
        rw [heq]
        exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (hgn _) (hln _)) (hgn _))
      · have hyS : xy.2 ∈ S := ⟨hr,hxy.2.2⟩
        have heq : g xy.1*l xy.2*g (xy.1+xy.2) = f xy := by simp [l,g,hx,hyS,hz,f]
        rw [heq]
        exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg (hln _) (hgn _)) (hgn _))
    · rw [indicator_of_notMem hxy]
      exact add_nonneg (mul_nonneg (mul_nonneg (hln _) (hgn _)) (hgn _))
        (mul_nonneg (mul_nonneg (hgn _) (hln _)) (hgn _))
  have hif : Integrable (D.indicator f) := by
    apply (hi₁.add hi₂).mono' (hm.indicator hD).aestronglyMeasurable
    filter_upwards [] with xy
    rw [Real.norm_of_nonneg (indicator_nonneg (fun x hx => hfn x) xy)]
    exact hmajor xy
  refine ⟨(integrable_indicator_iff hD).mp hif,?_⟩
  have hb := integral_mono_ae hif (hi₁.add hi₂) (Filter.Eventually.of_forall hmajor)
  rw [integral_indicator hD] at hb
  simp only [Pi.add_apply] at hb
  rw [integral_add hi₁ hi₂] at hb
  have hlint : (∫ x, l x^((3 : ℝ)/2)) = ∫ x in S, u x^((3 : ℝ)/2) := by
    rw [show (fun x => l x^((3 : ℝ)/2)) = S.indicator (fun x => u x^((3 : ℝ)/2)) from hpow S,
      integral_indicator hS]
  have hgint : (∫ x, g x^((3 : ℝ)/2)) = ∫ x in V, u x^((3 : ℝ)/2) := by
    rw [show (fun x => g x^((3 : ℝ)/2)) = V.indicator (fun x => u x^((3 : ℝ)/2)) from hpow V,
      integral_indicator hV]
  rw [hlint,hgint] at hb₁ hb₂
  exact hb.trans (by linarith only [hb₁,hb₂])

end WaveTurbulence.WeylSums
