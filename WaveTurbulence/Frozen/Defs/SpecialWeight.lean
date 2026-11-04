/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.NodeSign
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# specialWeight

Wave B tier B2 (WaveB2-Regular.lean), source: T (regref1-3); DH21 Lemma 7.3; DH21 Lemma 5.8. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The weight `∏_{𝔫 ∈ Z} (−ζ_𝔫 π i)^{-1}` of a special subset (node signs from the root signs `σ`), for couples
and trees (F61, B2-CL-11).

TARGET (regref1-3) writes `∏_{𝔫∈Z} (ζ_𝔫 π i)^{-1}` and states that `𝒥ℬ*` does not depend on `Z`; that comes from
DH21 Lemma 7.3 (L1737). The source has a sign error there: the `χ_∞` part of `I_{εα}I_{μ−εα}` is
`−χ_∞(α)/(επiα)·I_μ`, as in DH21 Lemma 5.8's own term II and in the landed Lean `iker_comp_decompP`
(`Foundations/ClassJR/Lemma58.lean`, `T₀ = −I_μ`). DH21 sets `ε_j = ζ_𝔫`, and the `Ω` convention does not
compensate. So the `Z`-coefficient of a dominant couple is `(−1)^{|Z|}` times the `Z`-independent `𝒥ℬ*`. The
per-couple leading term therefore carries `∏_{𝔫∈Z} (−1)/(ζ_𝔫 π i)`. The sum over an equivalence class
(Prop 7.8, (regref2-3)) and the WKE identification (regref1-5) are unaffected, since `|Z|` is constant on a class.
Trace: `/home/scott/wt-scratch/wke/F61-sign-trace.md` (wt-wke). Ruling: F61 CONFIRMED (orchestrator, 2026-11-04).
Probe `specialWeight_eq_neg_one_pow_mul_old`: the new weight is `(−1)^{|Z|}` times the old one. -/
noncomputable def specialWeight {w : ℕ} (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) : ℂ :=
  ∏ z ∈ Z, (-((((nodeSign σ z : ℤˣ) : ℤ) : ℂ) * Real.pi * Complex.I))⁻¹

end WaveTurbulence
