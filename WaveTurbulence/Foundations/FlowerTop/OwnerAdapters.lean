/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.FinalAssembly
public import WaveTurbulence.Foundations.Cut2EB.Target

/-! One adapter per posted owner declaration, from the owner's statement to the consumer clause. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open Set

/-- FC23's cut1 clause is the cut1 case. -/
theorem cut1_of_FC23 {Pm : ℕ} {P : WTParams} (h : FC23.FC23Cut1At Pm P) : FlowerCaseAt CaseCut1 Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc _
  obtain ⟨hs1, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := Option.isSome_iff_exists.mp hs1
  have := h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger j
  unfold FlowerBoundAt
  simpa only [Option.elim, mul_one] using this

/-- C2-E-B's frozen positive-cut2 target is the positive cut2 case. -/
theorem cut2_of_C2EB {Pm : ℕ} {P : WTParams} (h : Cut2EB.PositiveCut2FrozenAt Pm P) :
    FlowerCaseAt CaseCut2Pos Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  obtain ⟨j, rfl, hj⟩ := hc
  have hex : ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖ := hcut j rfl
  have := h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 j hj hex
  unfold FlowerBoundAt
  simpa only [Option.elim, Cut2EB.frozen_exponent] using this

end WaveTurbulence.FlowerTop
