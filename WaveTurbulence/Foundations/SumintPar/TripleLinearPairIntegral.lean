/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.TripleTimeBox

/-!
# Triple-time integration with a distinguished linear factor

The original pair variables are integrated first, retaining arbitrary
measurable dependence on the distinguished third time. Finite scalar
linear factors can then be pulled through both pair integrals.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
namespace WaveTurbulence.SumintPar

/-- Exact native triple-time Fubini with the distinguished linear factor outside the pair mass. -/
theorem lintegral_triple_linear_pair (lo hi : Fin 3 → ℝ) (F : ℝ → ℝ≥0∞)
    (G : ℝ → ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) (hFfin : ∀ s, F s ≠ ⊤)
    (hG : Measurable (Function.uncurry G)) :
    (∫⁻ z in Icc lo hi, F (z 2)*G (z 2) (z 0,z 1)) =
      ∫⁻ s in Icc (lo 2) (hi 2), F s*
        ∫⁻ w in Icc (lo 0,lo 1) (hi 0,hi 1), G s w := by
  have hcoord : Measurable (fun z : Fin 3 → ℝ => (z 2,(z 0,z 1))) := by fun_prop
  have hm : Measurable (fun z : Fin 3 → ℝ => F (z 2)*G (z 2) (z 0,z 1)) :=
    (hF.comp (measurable_pi_apply 2)).mul (hG.comp hcoord)
  rw [lintegral_triple_time_box _ hm]
  apply lintegral_congr
  intro s
  change (∫⁻ u in Icc (lo 0) (hi 0), ∫⁻ v in Icc (lo 1) (hi 1), F s*G s (u,v)) =
    F s*(∫⁻ w in Icc (lo 0,lo 1) (hi 0,hi 1), G s w)
  simp_rw [lintegral_const_mul' _ _ (hFfin s)]
  have hGs : Measurable (G s) := hG.comp (measurable_const.prodMk measurable_id)
  exact congrArg (fun q => F s*q) (lintegral_pair_Icc (G s) hGs (lo 0) (hi 0) (lo 1) (hi 1)).symm

end WaveTurbulence.SumintPar
