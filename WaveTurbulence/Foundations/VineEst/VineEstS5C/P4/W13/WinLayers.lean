/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam

/-! # P4-W1: the windows of the clocks `t₁`, `s₁` are the windows `L₄`, `Lₕ` of the certificates

In the static case A (`CaseA`, `bundle_decomp`) the clock `t₁` lies in the window of layer `L₄ = zpQ4` and `s₁` in the window of
layer `Lₕ = zpQh`; in case M (`bundle_decomp_mirror`) the roles are exchanged.  So the certificates `(certC …).lo`, `.hi`
(`(certT …).lo`, `.hi`) of `SFF` are the ones for the clocks in the `L₄` resp. `Lₕ` window, in both cases.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.ZpSurj

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {pstar : ι} [Fintype ι] [DecidableEq ι] (A : FamilyReconstruction w ι)

theorem zpQh_eq_layers : zpQh A pstar =
    max (layOf A (qrOf (A.family.placement pstar))) (layOf A (qbOf (A.family.placement pstar))) := by
  unfold zpQh
  rw [zpBranchQ_fst]
  congr 1
  exact parentCore_partner A

/-- Case A: `s₁`'s node has layer `Lₕ`. -/
theorem layer_s1_caseA (hA : CaseA (pstar := pstar) A) :
    layOf A (if nuOf A pstar = 1 then qrOf (A.family.placement pstar) else qbOf (A.family.placement pstar)) = zpQh A pstar := by
  rw [zpQh_eq_layers]
  unfold CaseA at hA
  by_cases hn : nuOf A pstar = 1
  · simp only [hn, if_true] at hA ⊢; exact (max_eq_left hA).symm
  · simp only [hn, if_false] at hA ⊢; exact (max_eq_right hA).symm

/-- Case M: `t₁`'s node has layer `Lₕ`. -/
theorem layer_t1_caseM (hM : CaseM (pstar := pstar) A) :
    layOf A (if nuOf A pstar = 1 then qbOf (A.family.placement pstar) else qrOf (A.family.placement pstar)) = zpQh A pstar := by
  rw [zpQh_eq_layers]
  unfold CaseM at hM
  by_cases hn : nuOf A pstar = 1
  · simp only [hn, if_true] at hM ⊢; exact (max_eq_right hM).symm
  · simp only [hn, if_false] at hM ⊢; exact (max_eq_left hM).symm

end WaveTurbulence.VineEstS5C.P4.W13
