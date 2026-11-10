/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyReach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderStep
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild

/-! # The twisted kernel in sumint form (V5 Step 4b, P2.2)

* `Reach.sign_a`: the sign of the upper joint is the same at every state of a batch (the unit twist flips only the sign of
  the lower joint, `coreBranchEquiv_sign`, and the lower joint of a member differs from `a`).
* `recentered_twisted`: the factor `e^{-πiδL^{2γ}t_{u1}Γ}` of (vineest1), written with the sign of the START garden, times
  `twistedLocalKernel Bs c` is `clRecenteredLocalKernel` of the state (R31(2): the same recentering exponent).
* `twistedKernel_sumintForm`: V4's identity `vineChain_eq_sumintForm'` applied at the twisted state, with the iterated twist
  `B'` of the chain assembly (`Reach.exists_asm`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.RegRed VineParamContract TTree
variable {w : ℕ} {ι : Type*}

theorem sign_step (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι) (ε : Bool) :
    (chosenSkeleton A.skeleton (A.family.placement i) ε).sign (ChainAt.nextA A c i ε).a.toNode =
      A.skeleton.sign c.a.toNode := by
  rw [nextA_a]
  cases ε
  · rfl
  · change (unitTwistGarden A.skeleton (A.family.placement i)).sign
      (coreBranchEquiv A.skeleton (A.family.placement i) c.a).toNode = _
    have hne : c.a ≠ (A.family.placement i).lower := (c.lower_ne i).symm
    rw [coreBranchEquiv_sign]
    simp [hne]

theorem Reach.sign_a {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') :
    B.skeleton.sign c'.a.toNode = A.skeleton.sign c.a.toNode := by
  induction h with
  | nil A c => rfl
  | skip i h ih => exact ih
  | apply op h ih => exact ih.trans (sign_step _ _ _ op.choice)

end WaveTurbulence.VineEstS4
