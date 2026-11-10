/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp15SokOp
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp10KT

/-! # (tildeJ2) for an abstract split (V5 Step 4b, step 4)

`tildeJ2_of_split`: for a start state `A` with a prime skeleton and a split `sp0` (with the members that may carry an operation
below `pstar` in `J`, all other members except `pstar` carrying no operation at `A`),
`∑_{x ∈ canon} K^U_x = ∑_{G ∈ Zp(A)} sSumAt G (K̃_T^G)`, where `K̃_T^G(t; E, F') = ∑_{y ∈ Y(A)} K^{T_y}_y(t; E, F')` for `G` untwisted at
`pstar` and with `(E, F')` exchanged for a twist at `pstar` (the common factor of TARGET (tildeJ2)).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

/-- The common lower factor `K̃_T` for the twist `G` of `A` at `pstar`: the sum of the lower kernels over `Y(A)`. -/
@[expose] noncomputable def ktilde (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) : ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  ∑ y ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩, kTor κ A G.1 pstar y t E F'

theorem HF_of_all {w d : ℕ} {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain) (L : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (base : Mom d)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |F k (base + latticePoint L n)|) : HF D hG L F layer base :=
  fun _ _ => hF _

end WaveTurbulence.VineEstS4
