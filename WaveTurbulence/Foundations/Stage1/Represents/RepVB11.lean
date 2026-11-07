/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB10
public import WaveTurbulence.Foundations.Vine.C.VCApi
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: VINE-B♯'s unit factor is VINE-C's `unitRecenteredW`

`UnitAt.clBlock`: the CL block of a unit region of VINE-C.  `unitKernelM_eq_unitRecenteredW`: for the blocks of the unit
regions `us j` of a state `X` (decoded by `layer`), VINE-B♯'s `unitKernelM` is VINE-C's `unitRecenteredW` with `W = modW λ` and
the unit profile `unitProfile blk h j`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.LGSpine WaveTurbulence.VineB WaveTurbulence.VineC

/-- The CL block of a unit region. -/
def unitClBlock {w : ℕ} {ι : Type*} {S : Garden w} {F : CoreFamily S ι} {Q : ι → Prop}
    (u : UnitAt S F Q) : CLBlock S :=
  ⟨u.blk.U, u.blk.a, u.blk.b, u.blk.block, u.cl⟩

theorem unitKernelM_eq_unitRecenteredW {w d : ℕ} {ι : Type*} {J : Type} [Fintype J] [DecidableEq J] {Q : J → ι → Prop}
    (X : FamilyReconstruction w ι) (us : ∀ j, UnitAt X.skeleton X.family (Q j))
    (layer : GNode (X.data.forest X.plain) → ℕ) (hL : IsLayering (X.data.garden X.plain) layer)
    (hspec : layeredReconstruction X.data X.plain layer hL = X.layered) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (base : Mom d) (j : J) (lam : ℤ) (t : Fin 3 → ℝ) (k : Fin 4 → Mom d) :
    unitKernelM (fun j => unitClBlock (us j)) X.data X.plain L γ δ h layer hL base j lam t k =
      unitRecenteredW X (us j) L γ δ (unitProfile (fun j => unitClBlock (us j)) h j) base (modW lam)
        (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) :=
  clRecenteredLocalKernelModC_eq_unit X (us j) _ layer hL hspec L γ δ _ base lam (t 0) (t 1) (t 2)
    (k 0) (k 1) (k 2) (k 3)

end WaveTurbulence.Represents
