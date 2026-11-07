/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp2Split
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp1Geom
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls1State
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RegionUnique
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainSplit

/-! # The factorized kernel of a split state (V5 Step 4b, step 4, WP-D)

For a state `X` with a split `sp`, the region data `RU`, `RS`, `RT` of `c.U = sb ∪ tb`, `sb`, `tb` are derived from the CL parent
pattern of the chain region (`clBlockConcat_parentPatterns`).  `kU_eq_sSumAt`: `twistedLocalKernel X sp.c = sSumAt X sp (kT X sp)`,
the per-state form of TARGET (tildeJ2) (hypotheses: `L ≠ 0`, `HF`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*}

/-- The numerical parameters of a kernel evaluation. -/
structure KPar (d : ℕ) where
  L : ℝ
  γ : ℝ
  δ : ℝ
  F : ℕ → Mom d → ℝ
  base : Mom d
  t0 : ℝ
  t1 : ℝ
  t2 : ℝ
  e : Mom d
  f : Mom d
  g : Mom d
  h : Mom d

namespace SplitAt
variable {S : Garden w} {F : CoreFamily S ι} {pstar : ι} {J : Set ι} (sp : SplitAt S F pstar J)

theorem hT : S.molecule.IsBlock sp.tb.U sp.sb.b sp.tb.b := by
  rw [sp.joint]; exact sp.tb.block

theorem hi : sp.sb.U ∩ sp.tb.U = {sp.sb.b} := by
  rw [sp.joint]; exact sp.inter

theorem hU : S.molecule.IsBlock (sp.sb.U ∪ sp.tb.U) sp.sb.a sp.tb.b := by
  rw [← sp.union, sp.sa, sp.tbb]; exact sp.c.block

theorem clU : Mole.CLParentPattern S (sp.sb.U ∪ sp.tb.U) sp.sb.a sp.tb.b := by
  rw [← sp.union, sp.sa, sp.tbb]; exact sp.c.cl

/-- The region data of the whole chain `sb ∪ tb`. -/
@[expose] noncomputable def RU : CLRegionData S (sp.sb.U ∪ sp.tb.U) sp.sb.a sp.tb.b := clRegionData S sp.hU sp.clU

theorem clST : Mole.CLParentPattern S sp.sb.U sp.sb.a sp.sb.b ∧ Mole.CLParentPattern S sp.tb.U sp.sb.b sp.tb.b :=
  clBlockConcat_parentPatterns sp.sb.block sp.hT sp.hi sp.hU sp.RU

/-- The region data of the upper block. -/
@[expose] noncomputable def RS : CLRegionData S sp.sb.U sp.sb.a sp.sb.b := clRegionData S sp.sb.block sp.clST.1

/-- The region data of the lower block. -/
@[expose] noncomputable def RT : CLRegionData S sp.tb.U sp.sb.b sp.tb.b := clRegionData S sp.hT sp.clST.2

end SplitAt

theorem clLocalKernel_idx {w d : ℕ} {G : Garden w} {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree}
    (hU : U = U') (ha : a = a') (hb : b = b') (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b')
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    clLocalKernel D hG R L γ δ F layer hLayer base t0 t1 t2 e f g h =
      clLocalKernel D hG R' L γ δ F layer hLayer base t0 t1 t2 e f g h := by
  subst hU ha hb
  rw [regionData_subsingleton R R']

section State
variable {d : ℕ} {pstar : ι} {J : Set ι} (κ : KPar d) (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)

/-- `K^U` of the state at its chain region. -/
@[expose] noncomputable def kU : ℂ :=
  twistedLocalKernel X sp.c κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h

/-- The lower kernel `K^T(t, t₁, t₂; E, F', g, h)` of the state. -/
@[expose] noncomputable def kT : ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  clLocalKernel X.data X.plain sp.RT κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X) κ.base t κ.t1 κ.t2 E F' κ.g κ.h

/-- The S-side with an arbitrary lower factor `Φ`. -/
@[expose] noncomputable def sSumAt (Φ : ℝ → Mom d → Mom d → ℂ) : ℂ :=
  sSum sp.RS X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
    sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ

theorem kU_eq_sSumAt (hL : κ.L ≠ 0) (hF : HF X.data X.plain κ.L κ.F (stateLayer X) κ.base) :
    kU κ X sp = sSumAt κ X sp (kT κ X sp) := by
  have hex : sp.RT.excluded = sp.RS.kept :=
    split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT
  have h1 := clLocalKernel_eq_sSum sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT X.data X.plain κ.L κ.γ κ.δ κ.F
    (stateLayer X) (stateLayer_isLayering X) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h hL hF
  unfold kU twistedLocalKernel
  rw [clLocalKernel_idx sp.union sp.sa.symm sp.tbb.symm (clRegionData X.skeleton sp.c.block sp.c.cl) sp.RU]
  rw [h1]
  unfold sSumAt kT
  have hb0 : clBoundaryNodes sp.RT 0 = sp.sb.b.toNode := rfl
  have hb1 : clBoundaryNodes sp.RT 1 = sp.sb.b.child sp.RS.kept := by
    change sp.sb.b.child sp.RT.excluded = _
    rw [hex]
  rw [hb0, hb1]

end State

end WaveTurbulence.VineEstS4
