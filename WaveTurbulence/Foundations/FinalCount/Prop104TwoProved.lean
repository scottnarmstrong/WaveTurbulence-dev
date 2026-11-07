/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.Prop104Two
public import WaveTurbulence.Foundations.FinalCount.MergeInput
public import WaveTurbulence.Foundations.FinalCount.PairGainInput
public import WaveTurbulence.Foundations.FinalCount.SmallGapInput
public import WaveTurbulence.Foundations.FinalCount.BiBridgeEqual
public import WaveTurbulence.Foundations.FinalCount.BiBridge
public import WaveTurbulence.Foundations.FinalCount.BetaCut
public import WaveTurbulence.Foundations.FinalCount.BridgeSplit
public import WaveTurbulence.Foundations.FinalCount.Prop102Bridge
import Mathlib.Tactic

/-! # DH23 Proposition 10.4(2)′ for `1/2 < γ < 1`, with all counting inputs proved

`G8R.prop104_two` (the size-refit copy of MOLEPROP4-T's `prop104_two`) with its `Prop104TwoInputs` at `η, η/2, η/4`
discharged: the seven operation inputs (`BetaCut`, `BridgeSplit`, `BiBridge`, `BiBridgeEqual`, `PairGain`, `SmallGapPair`,
`Merge`) are proved in this packet, and Prop 10.2 (both statements, with the size bound) is APPB's `dh23_prop_10_2`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem prop104TwoInputs_proved (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1 - γ)) (hηs : 4 * 1440061 * η ≤ 1) : Prop104TwoInputs.{u, v} d γ η :=
  ⟨betaCutInput d γ η, bridgeSplitInput d γ η, biBridgeInput d γ η ⟨by linarith [hγ.1], hγ.2⟩,
    bibridgeEqualInput d γ η, pairGainInput hd γ η hγ.2, smallGapPairInput hd γ η hγ.2 hη.le,
    mergeInput hd γ η hγ.2,
    prop102InputSz d hd γ η ⟨by linarith [hγ.1], hγ.2⟩ hη hηγ hηs,
    prop102SecondInputSz d hd γ η ⟨by linarith [hγ.1], hγ.2⟩ hη hηγ hηs⟩

/-- **DH23 Prop 10.4(2)′, `1/2 < γ < 1`, all counting inputs proved.** -/
theorem prop104_two_proved (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
        (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
        (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
        (∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ w → b ≠ w →
          (Degen.eraseAtoms M {w}).SameComponent a b) →
        (∀ p q r s t u, 3 ≤ M.bondsBetween p q → 3 ≤ M.bondsBetween r s → 3 ≤ M.bondsBetween t u →
          s(p, q) = s(r, s) ∨ s(p, q) = s(t, u) ∨ s(r, s) = s(t, u)) → (∀ p q, M.bondsBetween p q ≤ 3) →
        (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        ¬ IsYExceptional M → ¬ YReachesSmallCell M →
        ∀ e : D, SplitBound M e d L γ δ η C1
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ((M.atoms.card + 1) * L ^ (-(η / 16))))
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16)))) :=
  prop104_two.{u, v} d hd γ ⟨by linarith [hγ.1], hγ.2⟩ η hη hη200 hηd hγ.1
    (prop104TwoInputs_proved d hd γ η hγ hη (by
      have := min_le_left γ (1 - γ); have := min_le_right γ (1 - γ)
      have : 0 < min γ (1 - γ) := lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
      linarith) hηs)
    (prop104TwoInputs_proved d hd γ (η / 2) hγ (by linarith) (by
      have : 0 < min γ (1 - γ) := lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
      linarith) (by linarith))
    (prop104TwoInputs_proved d hd γ (η / 4) hγ (by linarith) (by
      have : 0 < min γ (1 - γ) := lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
      linarith) (by linarith))

end WaveTurbulence.FinalCountG8
