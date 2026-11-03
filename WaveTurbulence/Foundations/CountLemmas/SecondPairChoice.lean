/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Quantitative standing smallness for DH23 Lemma A.2(2) -/

public section
namespace WaveTurbulence.CountLemmas

/-- One explicit choice realizing the source's sufficiently small η. -/
@[expose] noncomputable def secondPairEta0 (γ : ℝ) : ℝ :=
  min ((1-γ)/10000) (1/1000000)

theorem secondPairEta0_pos {γ : ℝ} (hγ : γ < 1) : 0 < secondPairEta0 γ :=
  lt_min (by linarith only [hγ]) (by norm_num)

/-- The chosen radius and density exponent have strict margins at γ=4/5. -/
theorem secondPairChoice_bounds {γ η : ℝ} (hγ1 : γ < 1)
    (hη : 0 < η) (hη0 : η ≤ secondPairEta0 γ) (hcritical : (4 : ℝ)/5-10*η < γ) :
    (1 : ℝ)/2 < γ ∧ 0 < 1-γ+40*η ∧ 1-γ+40*η ≤ 1 ∧
      1-γ+40*η < 2-2*γ ∧ 1-2*γ < -(1-γ+40*η) ∧
      2-2*γ+η ≤ 1/2 ∧ 81*(4-2*γ+η)/244 < γ-20*η := by
  have hsmall := hη0.trans (min_le_left _ _)
  have htiny := hη0.trans (min_le_right _ _)
  constructor
  · linarith only [hcritical,htiny]
  constructor
  · linarith only [hγ1,hη]
  constructor
  · linarith only [hcritical,htiny]
  constructor
  · linarith only [hsmall,hγ1]
  constructor
  · linarith only [hcritical,htiny]
  constructor
  · linarith only [hcritical,htiny]
  · linarith only [hcritical,htiny]

end WaveTurbulence.CountLemmas
