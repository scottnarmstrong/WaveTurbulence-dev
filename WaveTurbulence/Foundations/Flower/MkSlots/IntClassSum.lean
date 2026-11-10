/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember3

/-! # B3s MK-SLOTS (integration, class sum): the class value of a capped fine′ class as a mode sum

* `member_integ`, `member_hsm`: the integrability and decoration-summability hypotheses of the pinned T4 for a member
  of the run class (PVBInteg's `_fix` lemmas with B3's regional bound, rewritten to the representative's shape data
  and the member's unit kernels).
* **`class_modes`**: the sum over the fine′ output set `T` of the frozen class summands is the `G_sb` dagger constant
  times the mode sum, over the combined family `capFam`, of the pinned outer values of `G_sb` with the class kernels
  `unitHkFW` of the run assembly (the pinned T4 `weightedClassFactorizationμ` applied to the member identity
  `member_skelVal` + `member_hasSum`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WNoVine
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.Flower.V5W
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots.IntMember

section Facts
variable (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d) {R p : ℕ} {kind : Bool}
  (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 0 ≤ b)
  (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ) (tt : Fin (2 * R) → ℝ)
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hcanY : IsCanonGC (p + 1) y.1.layered) (hlay : ∀ x, stateLayer y.1 x ≤ p)

theorem frontierG_norm_le (Rf : Fin (2 * R) → Option ℝ) (j : Fin (2 * R)) (x : Mom P.d) :
    ‖frontierG (d := P.d) (Rf j) x‖ ≤ 1 := by
  unfold frontierG
  rw [Complex.norm_real, Real.norm_eq_abs]
  cases Rf j with
  | none => simp
  | some r =>
    simp only [Option.elim]
    rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact XChain.ProductCut.chi0_le_one _

end Facts

end WaveTurbulence.Flower.MkSlots.IntMember
