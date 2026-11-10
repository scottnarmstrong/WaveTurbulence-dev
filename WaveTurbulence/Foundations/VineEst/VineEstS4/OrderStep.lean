/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderCore
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Transport

/-! # `n_(2)` is invariant along an LF batch (V5 Step 4b, R31(2))

`order2_step_gen`: one LF operation (twist or not) keeps `n_(2)` (`localOrder2`) of the transported region: the two
designated regular objects (the tree at the lower joint, the couple at the exceptional pair) are replaced with the same
combined order (`LFConstruction.combinedOrder`), all other replacement data are carried along the bijections, and the
exceptional pair is regional on both sides.  `Reach.order2` is the batch version.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*}

theorem cast_a {S : Garden w} {F F' : CoreFamily S ι} (e : F' = F) (x : ChainAt S F') :
    (e ▸ x : ChainAt S F).a = x.a := by
  subst e
  rfl

theorem nextA_a (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι) (ε : Bool) :
    (ChainAt.nextA A c i ε).a = chosenBranchEquiv A.skeleton (A.family.placement i) ε c.a := by
  unfold ChainAt.nextA
  rw [cast_a]
  cases ε <;> rfl

end WaveTurbulence.VineEstS4
