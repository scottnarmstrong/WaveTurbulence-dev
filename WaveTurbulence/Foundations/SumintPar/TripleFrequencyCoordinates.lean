/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ExitFrequencyCoordinates
public import WaveTurbulence.Foundations.SumintPar.TwoExitKernelBound

/-!
# Native three-frequency Fubini coordinates

The original frequency order is retained. Product Lebesgue measure is
preserved exactly, so scalar kernel estimates apply without Jacobians.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
namespace WaveTurbulence.SumintPar

/-- Native three-frequency coordinates in first/second/third order. -/
@[expose] def tripleFrequencyEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × ℝ × ℝ where
  toFun z := (z 0,z 1,z 2)
  invFun z := ![z.1,z.2.1,z.2.2]
  left_inv z := by funext j; fin_cases j <;> rfl
  right_inv z := by rcases z with ⟨x,y,z⟩; rfl
  measurable_toFun := by change Measurable (fun z : Fin 3 → ℝ => (z 0,z 1,z 2)); fun_prop
  measurable_invFun := by change Measurable (fun z : ℝ × ℝ × ℝ => ![z.1,z.2.1,z.2.2]); fun_prop

/-- Native triple-frequency Fubini preserves volume exactly. -/
theorem volume_preserving_tripleFrequencyEquiv : MeasurePreserving tripleFrequencyEquiv volume volume := by
  have hi : MeasurePreserving tripleFrequencyEquiv.symm volume volume := by
    refine ⟨tripleFrequencyEquiv.symm.measurable,(Measure.pi_eq fun s hs => ?_).symm⟩
    have hp : tripleFrequencyEquiv.symm ⁻¹' Set.pi Set.univ s = s 0 ×ˢ (s 1 ×ˢ s 2) := by
      ext z
      simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_prod]
      constructor
      · intro h
        exact ⟨h 0,h 1,h 2⟩
      · rintro ⟨h0,h1,h2⟩ j
        fin_cases j
        · exact h0
        · exact h1
        · exact h2
    rw [tripleFrequencyEquiv.symm.map_apply,hp]
    simp only [Measure.volume_eq_prod,Measure.prod_prod,Fin.prod_univ_three]
    ring
  exact MeasurePreserving.symm tripleFrequencyEquiv.symm hi

/-- The actual native two-exit kernel integral is precisely the scalar nested kernel pairing. -/
theorem lintegral_native_two_exit_eq (a b c : ℝ) (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
      scalarPowerKernel c (ξ 2)*H (ξ 0,ξ 1+ξ 2)) =
      ∫⁻ x : ℝ, scalarPowerKernel a x * ∫⁻ yz : ℝ × ℝ,
        scalarPowerKernel b yz.1*scalarPowerKernel c yz.2*H (x,yz.1+yz.2) := by
  let f (q : ℝ × ℝ × ℝ) := scalarPowerKernel a q.1*scalarPowerKernel b q.2.1*
    scalarPowerKernel c q.2.2*H (q.1,q.2.1+q.2.2)
  have he := volume_preserving_tripleFrequencyEquiv.lintegral_comp_emb
    tripleFrequencyEquiv.measurableEmbedding f
  change (∫⁻ ξ, f (tripleFrequencyEquiv ξ)) = _
  rw [he,Measure.volume_eq_prod]
  have hcoord : Measurable (fun q : ℝ × ℝ × ℝ => (q.1,q.2.1+q.2.2)) := by fun_prop
  have hm : Measurable f := (((measurable_scalarPowerKernel a).comp measurable_fst).mul
    ((measurable_scalarPowerKernel b).comp (measurable_fst.comp measurable_snd))).mul
    ((measurable_scalarPowerKernel c).comp (measurable_snd.comp measurable_snd)) |>.mul (hH.comp hcoord)
  rw [lintegral_prod f hm.aemeasurable]
  apply lintegral_congr
  intro x
  have hfinite : scalarPowerKernel a x ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← lintegral_const_mul' _ _ hfinite]
  apply lintegral_congr
  intro yz
  dsimp [f]
  ring

end WaveTurbulence.SumintPar
