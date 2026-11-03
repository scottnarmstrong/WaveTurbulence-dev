/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Products of scalar time cutoffs

A compact cutoff in every time coordinate gives compact support in the
full coordinate space. No regularity in momentum is involved.
-/

public section

open Set
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The scalar cutoff applied in every time coordinate. -/
@[expose] def coordinateCutoff {r : ℕ} (χ : ℝ → ℝ) (t : Fin r → ℝ) : ℂ :=
  ∏ j, (χ (t j) : ℂ)

/-- Products of smooth scalar cutoffs are smooth. -/
theorem coordinateCutoff_contDiff {r : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (coordinateCutoff (r := r) χ) := by
  apply contDiff_prod
  intro j _
  exact Complex.ofRealCLM.contDiff.comp (hχ.comp (by fun_prop))

/-- Products of compact scalar cutoffs have compact support in the whole time space. -/
theorem coordinateCutoff_hasCompactSupport {r : ℕ} {χ : ℝ → ℝ}
    (hc : HasCompactSupport χ) : HasCompactSupport (coordinateCutoff (r := r) χ) := by
  classical
  apply HasCompactSupport.intro (isCompact_univ_pi (fun _ : Fin r => hc))
  intro t ht
  have hi : ∃ j : Fin r, t j ∉ tsupport χ := by
    simpa only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] using ht
  obtain ⟨j, hj⟩ := hi
  have hz : χ (t j) = 0 := image_eq_zero_of_notMem_tsupport hj
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hz])

end WaveTurbulence.Fourier
