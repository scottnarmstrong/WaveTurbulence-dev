/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Core
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowReach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowOrder
public import WaveTurbulence.Foundations.VineEst.VineEstS4.TwistedKernelForm
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyReach

/-! # V5-CONT, members: continuity of the recentered kernel of a reached state

`reach_stateLayer_le`: the layers of a reached state are at most `p` (start: hypothesis; reached: the state is canonical, so
`CanonCriterion p`).  `member_continuousOn`: for a state `Bs` reached from `(A, c)` by a batch (any `kind`), the recentered
kernel `clRecenteredLocalKernel` of `Bs` at its region is continuous in `(t₀,t₁,t₂)` on the closed cube `cubeSet q₀`, for
every `E` of the output set of the START datum.  The cube and the output set are those of the start: the datum of the member
is `step3W` of the iterated twist `B1` of the start assembly (`Reach.exists_asm`) with the SAME output indices `q₀`
(their compatibility with the member needs only `hqo`: `q₀ 0` is the layer of `a`, and the leaf-child time condition, both
preserved by the batch through `atomLayer`), and the row eligibility of the member is carried from the start
(`Reach.rowCoherent`, `Reach.order_eq`).  Everything here is independent of `kind`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.Cont
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
  MeasureTheory
open scoped ENNReal

variable {w : ℕ} {ι : Type*}

/-- The layers `layer`-function of a state is bounded iff the layers of its layered garden are. -/
theorem stateLayer_le_of_layered {p : ℕ} (Bs : FamilyReconstruction w ι) (h : ∀ x, Bs.layered.layer x ≤ p) :
    ∀ x, stateLayer Bs x ≤ p := by
  have key : ∀ X : LayeredGarden w,
      layeredReconstruction Bs.data Bs.plain (stateLayer Bs) (stateLayer_isLayering Bs) = X →
      (∀ x, X.layer x ≤ p) → ∀ x, stateLayer Bs x ≤ p := by
    intro X hX hx
    subst hX
    exact hx
  exact key Bs.layered (stateLayer_spec Bs) h

/-- The layers of every state reached from the start are `≤ p` (the reached state is canonical or is the start). -/
theorem reach_stateLayer_le {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c')
    (hA : ∀ x, stateLayer A x ≤ p) : ∀ x, stateLayer B x ≤ p := by
  rcases h.canonical_or_eq with ⟨hB, _⟩ | hcan
  · subst hB
    exact hA
  · exact stateLayer_le_of_layered B hcan.criterion.1

end WaveTurbulence.VineEstS5C.Cont
