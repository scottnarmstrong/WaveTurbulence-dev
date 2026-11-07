/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.NestGeom

/-! # One level of the induction on the core vines (V5 Step 4d part C, WP-I)

`Ktil_eq_canon`: the common lower factor `K̃` of a split (the class sum `∑_{y ∈ Y(A)} kT y` of the lower blocks) is the class sum
`canonFinset` of the family restricted to the members below the split, at the chain region `chainOfSplit` (= the lower block), of
the literal kernel `twistedLocalKernel` with the boundary parameters `(t, E, F')`.  So `tildeJ2_canon` and `tildeJ2_bundle` apply
again to the lower factor (TARGET Step 4: the induction hypothesis for `U^{<p}`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
variable {w : ℕ} {ι ι' : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι}

theorem stateLayer_restrict (X : FamilyReconstruction w ι) (e : ι' → ι) (he : Function.Injective e) :
    stateLayer (restrictState X e he) = stateLayer X := rfl

theorem kT_eq_twistedLocalKernel (κ : KPar d) (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)
    (e : ι' → ι) (he : Function.Injective e) (hJ : ∀ j, e j ∈ J) (t : ℝ) (E F' : Mom d) :
    kT κ X sp t E F' = twistedLocalKernel (restrictState X e he) (chainOfSplit X sp e he hJ) κ.L κ.γ κ.δ κ.F κ.base t κ.t1 κ.t2 E F' κ.g κ.h := by
  unfold kT twistedLocalKernel
  exact clLocalKernel_idx rfl sp.joint rfl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

section
variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open Classical in
/-- **The common lower factor `K̃` of the member `pstar` is the class sum of the restricted problem.** -/
theorem Ktil_eq_canon (hc : Stage1.OpsCommute p kind w ι) (e : ι' → ι) (he : Function.Injective e)
    (hJ : ∀ j, e j ∈ J) (hJ' : ∀ i ∈ J, ∃ j, e j = i) (κ : KPar d) {A : FamilyReconstruction w ι}
    (hA : IsPrimeGarden A.skeleton) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) :
    Ktil (p := p) (kind := kind) κ A sp0 hA = fun t E F' =>
      ∑ z ∈ canonFinsetK p kind (restrictState A e he) (chainOfSplit A sp0 e he hJ),
        twistedLocalKernel z.1 z.2 κ.L κ.γ κ.δ κ.F κ.base t κ.t1 κ.t2 E F' κ.g κ.h := by
  funext t E F'
  rw [← sum_yA_eq_canon (g := fun X c => twistedLocalKernel X c κ.L κ.γ κ.δ κ.F κ.base t κ.t1 κ.t2 E F' κ.g κ.h)
    hc e he hJ hJ' hA sp0 hA0]
  unfold Ktil ktilde
  refine Finset.sum_congr rfl fun y hy => ?_
  have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
  unfold kTor
  rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]
  exact kT_eq_twistedLocalKernel κ y.1 y.2 e he hJ t E F'

end

end WaveTurbulence.VineEstS5C
