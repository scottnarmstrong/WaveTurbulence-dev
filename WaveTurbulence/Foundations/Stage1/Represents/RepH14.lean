/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH13
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.Stage1.Represents.RepCount2

/-!
# S2 REPRESENTS, VINE-D (14): a uniform bound for spliced kernels and countable sums of representations

`norm_splicedKernel_le`: under `SplicedAmplitudeBounds`, `‖K_G(D)‖ ≤ ‖coupling‖^{|G|} · ((⌊2L⌋+2)^d)^{#pairs}`: every
summand is bounded by `1` (epsilon, gap indicator, unit-bounded amplitudes, time domain of volume `≤ 1`) and vanishes
unless every bonded slot momentum is in the unit ball of its centre (finitely many decorations, `decoration_count`).
`RepIntC.tsum`: a countable sum of representations with summable masses is a representation (the per-mode sums of
INTERFACE v2 step 4).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ}

theorem norm_splicedTimeIntegral_le (G : Garden w) (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → Fin d → ℤ) : ‖splicedTimeIntegral G D L γ δ base z‖ ≤ 1 := by
  unfold splicedTimeIntegral
  have hvol := volume_splicedTimeDomain_le G D.layer D.rootTime
  have hfin : volume (splicedTimeDomain G D.layer D.rootTime) < ⊤ := lt_of_le_of_lt hvol ENNReal.one_lt_top
  rw [integral_indicator (measurableSet_splicedTimeDomain G D.layer D.rootTime)]
  have hb : ∀ τ : GBranch G.tree → ℝ, ‖phaseProd L γ δ G (cosetDecoration G L base z) τ *
      ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * τ v : ℝ) * Complex.I)‖ ≤ 1 := by
    intro τ
    rw [norm_mul, norm_phaseProd_le, one_mul, norm_prod]
    exact le_of_eq (Finset.prod_eq_one fun _ _ => Complex.norm_exp_ofReal_mul_I _)
  have h1 := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) (C := 1) hfin
    (Filter.Eventually.of_forall hb)
  refine h1.trans ?_
  rw [one_mul, Measure.real]
  have := ENNReal.toReal_mono ENNReal.one_ne_top hvol
  simpa using this

end WaveTurbulence.Represents
