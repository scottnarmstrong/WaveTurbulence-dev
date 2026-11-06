/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamRungFiber
import Mathlib.Tactic

/-! # Source resonances and rail compatibility on the full rung fiber -/

public section
namespace WaveTurbulence.Vine.Param

/-- Shared rail orientation makes the outgoing upper rail exactly the
following rung's incoming upper rail, with the same physical gap. -/
theorem rung_compatible_ports {E : Type*} [AddCommGroup E]
    (P Q : RungPattern) (hPQ : P.signs 3=Q.signs 2) (r d : E) (xy : E×E) :
    P.upperAfter r d xy=Q.upperBefore r (P.lowerAfter d xy) := by
  cases P <;> cases Q <;> norm_num [RungPattern.signs] at hPQ <;> rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The full actual lower rung resonance is exactly bilinear in its two
free differences. Conservation supplies the physical following rail. -/
theorem rung_fiber_lower_phase (P : RungPattern) (r d : E) (q : RungFlowFiber P r d) :
    (P.signs 0 : ℝ)*‖q.1.1.1‖^2+(P.signs 1 : ℝ)*‖q.1.1.2‖^2+
      (P.signs 3 : ℝ)*‖q.1.2.2‖^2-(P.signs 2 : ℝ)*‖d‖^2=
      2*inner ℝ ((rungFiberChart P r d) q).1 ((rungFiberChart P r d) q).2 := by
  have hh := P.lowerPhase_eq d (P.encode d q.1.1)
  simp only [RungPattern.lowerPhase,P.decode_encode] at hh
  rw [P.lowerAfter_of_conservation q.1.1.1 q.1.1.2 d q.1.2.2 q.2.2] at hh
  exact hh

/-- The full actual upper rung resonance is the opposite bilinear term plus
the source ternary linear correction paired with the physical gap. -/
theorem rung_fiber_upper_phase (P : RungPattern) (r d : E) (q : RungFlowFiber P r d) :
    -(P.signs 0 : ℝ)*‖q.1.1.1‖^2-(P.signs 1 : ℝ)*‖q.1.1.2‖^2-
      (P.signs 3 : ℝ)*‖q.1.2.1‖^2+(P.signs 2 : ℝ)*‖P.upperBefore r d‖^2=
      -2*inner ℝ ((rungFiberChart P r d) q).1 ((rungFiberChart P r d) q).2+
        2*inner ℝ r (P.correction r ((rungFiberChart P r d) q)) := by
  have hh := P.upperPhase_eq r d (P.encode d q.1.1)
  simp only [RungPattern.upperPhase,P.decode_encode] at hh
  rw [P.upperAfter_of_conservation r q.1.1.1 q.1.1.2 d q.1.2.1 q.2.1] at hh
  exact hh

/-- Compatible consecutive full fibers share exactly the same upper rail,
so the local parametrizations glue without an additional momentum premise. -/
theorem rung_fiber_shared_upper {E : Type*} [AddCommGroup E]
    (P Q : RungPattern) (hPQ : P.signs 3=Q.signs 2) (r d : E) (q : RungFlowFiber P r d) :
    q.1.2.1=Q.upperBefore r q.1.2.2 := by
  rw [← P.upperAfter_of_conservation r q.1.1.1 q.1.1.2 d q.1.2.1 q.2.1,
    rung_compatible_ports P Q hPQ,
    P.lowerAfter_of_conservation q.1.1.1 q.1.1.2 d q.1.2.2 q.2.2]

end WaveTurbulence.Vine.Param
