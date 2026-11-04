/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CubicPhysicalIncoherence
public import WaveTurbulence.Foundations.Sumint.CubicMinorPhysicalWindow
public import WaveTurbulence.Foundations.Sumint.CubicParameterContinuity
public import WaveTurbulence.Foundations.Sumint.NonnegativeIntegralCover

/-!
# Complete normal endpoint-strip estimate in physical times

The bounded third-time interval supplies the half-moment gain in the
stationary region. The strip is discarded only in the Weyl region.
The inner two-time box uses its native product measure, exactly as in
source factor-mass recombination.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- The full normal endpoint-strip window with its two different contributions retained. -/
theorem exists_cubic_physical_endpoint_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm R : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (sel : Bool) (p q r : Mom d) (ξ ζ ω : ℝ → Mom d),
      Continuous ξ → Continuous ζ → Continuous ω →
      ∀ c h a b l u v w e : ℝ, 0 < c → 0 ≤ h → a ≤ b → l ≤ u → v ≤ w → w-v ≤ 3 →
      (∀ t ∈ Icc v w,
        (-(T₀*L^(2*γ)) ≤ c*(a-t) ∧ c*(b-t) ≤ T₀*L^(2*γ)) ∧
        (-(T₀*L^(2*γ)) ≤ c*(l-t) ∧ c*(u-t) ≤ T₀*L^(2*γ))) →
      (∫⁻ t in Icc v w, ∫⁻ z in Icc (a,l) (b,u),
        if |t-e| ≤ 2*h+(|z.1-t|+|z.2-t|) then
          ‖WeylSums.cubicLatticeSum L (c*(z.1-t)) (c*(z.2-t)) sel p q r (ξ t) (ζ t) (ω t)‖ₑ else 0) ≤
      ENNReal.ofReal (c⁻¹*c⁻¹*(Cs*L^(3*d)*(Real.sqrt h+c^(-(1/2:ℝ)))+
        (w-v)*Cm*L^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log L)) := by
  obtain ⟨Cs,hCs,hsmall⟩ := exists_cubic_physical_small_incoherence_bound d hd
  obtain ⟨Cm,R,hCm,hR,hminor⟩ := exists_cubic_minor_physical_window_bound d hd γ hγ T₀ hT₀
  refine ⟨Cs,Cm,R,hCs,hCm,hR,?_⟩
  intro L hL sel p q r ξ ζ ω hξ hζ hω c h a b l u v w e hc hh hab hlu hvw hlen hwin
  have hL1 : 1 ≤ L := by linarith [hR.trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  let N := fun x : ℝ × (ℝ × ℝ) =>
    ‖WeylSums.cubicLatticeSum L (c*(x.2.1-x.1)) (c*(x.2.2-x.1)) sel p q r (ξ x.1) (ζ x.1) (ω x.1)‖ₑ
  let F := fun x : ℝ × (ℝ × ℝ) =>
    if |x.1-e| ≤ 2*h+(|x.2.1-x.1|+|x.2.2-x.1|) then N x else 0
  let A := fun x : ℝ × (ℝ × ℝ) =>
    if |c*(x.2.1-x.1)| ≤ L ∧ |c*(x.2.2-x.1)| ≤ L ∧
      |x.1-e| ≤ 2*h+(|x.2.1-x.1|+|x.2.2-x.1|) then N x else 0
  let B := fun x : ℝ × (ℝ × ℝ) =>
    if L ≤ max |c*(x.2.1-x.1)| |c*(x.2.2-x.1)| ∧
      |c*(x.2.1-x.1)| ≤ T₀*L^(2*γ) ∧ |c*(x.2.2-x.1)| ≤ T₀*L^(2*γ) then N x else 0
  have hN : Measurable N :=
    (continuous_cubicLatticeSum_parameters hLp sel p q r
      (fun x : ℝ × (ℝ × ℝ) => c*(x.2.1-x.1)) (fun x => c*(x.2.2-x.1))
      (fun x => ξ x.1) (fun x => ζ x.1) (fun x => ω x.1)
      (by fun_prop) (by fun_prop) (hξ.comp continuous_fst) (hζ.comp continuous_fst) (hω.comp continuous_fst)).measurable.enorm
  have ht0 : Measurable (fun x : ℝ × (ℝ × ℝ) => |c*(x.2.1-x.1)|) := by fun_prop
  have ht1 : Measurable (fun x : ℝ × (ℝ × ℝ) => |c*(x.2.2-x.1)|) := by fun_prop
  have hs0 : Measurable (fun x : ℝ × (ℝ × ℝ) => |x.1-e|) := by fun_prop
  have hs1 : Measurable (fun x : ℝ × (ℝ × ℝ) => 2*h+(|x.2.1-x.1|+|x.2.2-x.1|)) := by fun_prop
  have hA : Measurable A := Measurable.ite
    ((measurableSet_le ht0 measurable_const).inter
      ((measurableSet_le ht1 measurable_const).inter (measurableSet_le hs0 hs1))) hN measurable_const
  have hB : Measurable B := Measurable.ite
    ((measurableSet_le measurable_const (ht0.max ht1)).inter
      ((measurableSet_le ht0 measurable_const).inter (measurableSet_le ht1 measurable_const))) hN measurable_const
  have hcover : ∀ t ∈ Icc v w, ∀ z ∈ Icc (a,l) (b,u), F (t,z) ≤ A (t,z)+B (t,z) := by
    intro t ht z hz
    dsimp only [F,A,B]
    by_cases hs : |t-e| ≤ 2*h+(|z.1-t|+|z.2-t|)
    · rw [ite_eq_left hs]
      by_cases hm : |c*(z.1-t)| ≤ L ∧ |c*(z.2-t)| ≤ L
      · rw [ite_eq_left ⟨hm.1,hm.2,hs⟩]
        exact le_add_right le_rfl
      · have hmax : L ≤ max |c*(z.1-t)| |c*(z.2-t)| := by
          by_contra hmax
          have hh' := max_lt_iff.mp (lt_of_not_ge hmax)
          exact hm ⟨hh'.1.le,hh'.2.le⟩
        have hw0 : |c*(z.1-t)| ≤ T₀*L^(2*γ) := abs_le.mpr ⟨
          (hwin t ht).1.1.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.1.1 t) hc.le),
          (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2.1 t) hc.le).trans (hwin t ht).1.2⟩
        have hw1 : |c*(z.2-t)| ≤ T₀*L^(2*γ) := abs_le.mpr ⟨
          (hwin t ht).2.1.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.1.2 t) hc.le),
          (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2.2 t) hc.le).trans (hwin t ht).2.2⟩
        have hnotA : ¬ (|c*(z.1-t)| ≤ L ∧ |c*(z.2-t)| ≤ L ∧
            |t-e| ≤ 2*h+(|z.1-t|+|z.2-t|)) := fun h => hm ⟨h.1,h.2.1⟩
        have hbig : L ≤ max |c*(z.1-t)| |c*(z.2-t)| ∧
            |c*(z.1-t)| ≤ T₀*L^(2*γ) ∧ |c*(z.2-t)| ≤ T₀*L^(2*γ) := ⟨hmax,hw0,hw1⟩
        simp only [ite_eq_right hnotA,ite_eq_left hbig,zero_add,le_refl]
    · rw [ite_eq_right hs]
      exact bot_le
  have hAnative (t : ℝ) : (∫⁻ z : ℝ × ℝ, A (t,z)) =
      ∫⁻ s : ℝ, ∫⁻ s' : ℝ, A (t,(s,s')) := by
    rw [Measure.volume_eq_prod]
    exact lintegral_prod _ ((hA.comp ((measurable_const (a := t)).prodMk measurable_id)).aemeasurable)
  have hBnative (t : ℝ) : (∫⁻ z : ℝ × ℝ, B (t,z)) =
      ∫⁻ s : ℝ, ∫⁻ s' : ℝ, B (t,(s,s')) := by
    rw [Measure.volume_eq_prod]
    exact lintegral_prod _ ((hB.comp ((measurable_const (a := t)).prodMk measurable_id)).aemeasurable)
  have ha : (∫⁻ t in Icc v w, ∫⁻ z : ℝ × ℝ, A (t,z)) ≤
      ENNReal.ofReal (c⁻¹*c⁻¹*(Cs*L^(3*d)*(Real.sqrt h+c^(-(1/2:ℝ))))) := by
    simp_rw [hAnative]
    exact hsmall hL1 hc hh sel p q r ξ ζ ω e v w hlen
  have hb : (∫⁻ t in Icc v w, ∫⁻ z : ℝ × ℝ, B (t,z)) ≤
      ENNReal.ofReal ((w-v)*c⁻¹*c⁻¹*Cm*L^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log L) := by
    simp_rw [hBnative]
    exact hminor L hL sel p q r ξ ζ ω c v w hc hvw
  have hsa : 0 ≤ c⁻¹*c⁻¹*(Cs*L^(3*d)*(Real.sqrt h+c^(-(1/2:ℝ)))) := by positivity
  have hsb : 0 ≤ (w-v)*c⁻¹*c⁻¹*Cm*L^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log L := by
    have hw : 0 ≤ w-v := sub_nonneg.mpr hvw
    positivity
  exact (lintegral_box_le_split F A B hA v w (Icc (a,l) (b,u)) measurableSet_Icc hcover).trans
    ((add_le_add ha hb).trans_eq (by rw [← ENNReal.ofReal_add hsa hsb]; congr 1; ring))

end WaveTurbulence.Sumint
