/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalTimeRestriction
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ParametricHalfCell

/-! # Joint temporal and spatial frequency measurability of the actual remainder -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT WithLp

/-- Every literal NT term is jointly measurable in λ and both modulation arrays. -/
theorem stronglyMeasurable_localRemainder_joint {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (L δ γ : ℝ) (J : Finset (Fin n))
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C))
    (z : (Fin n × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      localRemainder L δ γ J C p.2.1 p.2.2 p.1 z) := by
  have hs : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      approxSum L (L^(2*γ)*δ) (halfCellAmplitude z p.2.1 p.2.2)
        (resProfile J (fun Ω => C (ofLp Ω) p.1))) := by
    apply measurable_approxSum_parameter L (L^(2*γ)*δ) J
      (W := fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) => halfCellAmplitude z p.2.1 p.2.2)
      (C := fun α p => C α p.1)
    · intro x y
      have hb := (continuous_halfCellAmplitude_joint z).measurable
      have hm : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
          (p.2,(x,y))) := measurable_snd.prodMk measurable_const
      have hh := hb.comp hm
      exact hh
    · intro α
      have hb : StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
          C α p.1) := hC.comp_measurable (measurable_const.prodMk measurable_fst)
      exact hb.measurable
  have hc : StronglyMeasurable (fun lam : ℝ × ℝ =>
      ∫ Ω : EuclideanSpace ℝ {j : Fin n // j ∉ J}, C (ofLp Ω) lam) := by
    have hm : StronglyMeasurable (fun p : EuclideanSpace ℝ {j : Fin n // j ∉ J} × (ℝ × ℝ) =>
        C (ofLp p.1) p.2) := hC.comp_measurable
      (((WithLp.measurable_ofLp 2 _).comp measurable_fst).prodMk measurable_snd)
    exact hm.integral_prod_left'
  have ha : StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      approxApp L δ γ J (fun Ω => C (ofLp Ω) p.1) (halfCellAmplitude z p.2.1 p.2.2)) :=
    (stronglyMeasurable_const.mul (hc.comp_measurable measurable_fst)).mul
      ((stronglyMeasurable_singInt_halfCellAmplitude hd hn J z).comp_measurable measurable_snd)
  exact stronglyMeasurable_const.mul (hs.stronglyMeasurable.sub ha)

end WaveTurbulence.RegAsymp
