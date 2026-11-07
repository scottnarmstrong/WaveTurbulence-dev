/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc2

/-! # The top level of the induction over the core vines (V5 Step 4d part C, WP-I)

`Lvl.top`: all core members and the whole chain region of the assembly; `Lvl.top_classSum`: its class sum is the sum over `canonFinset`
of the start state of `twistedLocalKernel` (definitional), i.e. the left-hand side of `VineEstCanon` up to the recentering factor.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The top level: all core members, the whole chain region. -/
noncomputable def Lvl.top : Lvl B where
  ι := (assemblySourceFamily B).CoreIndex
  e := id
  he := Function.injective_id
  k0 := n
  hk0 := le_refl _
  hmem := fun j => j.1.2
  hsurj := fun i _ => ⟨i, rfl⟩
  c := chainStart B
  hcU := (iregion_full B).symm
  hca := (jointAt_top B).symm
  hcb := rfl

theorem Lvl.top_classSum (κ0 : KPar d) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    (Lvl.top B).classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h =
      ∑ z ∈ canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B),
        twistedLocalKernel z.1 z.2 κ0.L κ0.γ κ0.δ κ0.F κ0.base t0 t1 t2 e f g h := rfl

end WaveTurbulence.VineEstS5C
