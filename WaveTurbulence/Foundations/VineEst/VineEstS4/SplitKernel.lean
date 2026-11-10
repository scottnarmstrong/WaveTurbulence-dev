/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitSummand

/-! # The CL-local kernel of `U = S ∪ T` at the joint `b` (V5 Step 4b, P2.3)

`clLocalKernel_split_sigma`: the kernel `K^U` is `coupling^{n_1(U)} ζ_U` times the sum, over the pairs `(xS, κT)` of an upper-block
decoration `xS` and a decoration `κT` of `T` with boundary `(base + xS(b), base + xS(b.child kept), g, h)`, of the time integral of
`spart(xS) * (summand of T at upper time u_b)`.  This is the exact content of TARGET (tildeJ2) before the sums and integrals of the
two factors are separated.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

section Const
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)
include hS hT hi hU

theorem order1_split (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) :
    clLocalOrder1 RU = clLocalOrder1 RS + clLocalOrder1 RT := by
  unfold clLocalOrder1 clInteriorBranches
  rw [split_interior hS hT hi hU]
  exact Finset.card_union_of_disjoint (split_interior_disjoint hS hT hi hU)

theorem zeta_split (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c) :
    clLocalZeta RU = clLocalZeta RS * clLocalZeta RT := by
  unfold clLocalZeta clInteriorBranches
  rw [split_interior hS hT hi hU]
  exact Finset.prod_union (split_interior_disjoint hS hT hi hU)

end Const

section Sigma
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)

/-- Extended decorations of `U` as pairs of an upper-block decoration and a local decoration of `T`. -/
@[expose] noncomputable def splitExtEquiv (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
    (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (βU : Fin 4 → Mom d) :
    ExtCL RU L base βU ≃
      Σ xS : ExtS RS L base (βU 0) (βU 1), CLLocalDecoration RT L base (bdT RT L base xS.1 (βU 2) (βU 3)) :=
  (splitDecEquiv hS hT hi hU RU RS RT hL base βU).trans
    (Equiv.sigmaCongrRight fun xS => (clExtEquiv RT L base (bdT RT L base xS.1 (βU 2) (βU 3))).symm)

/-- Local decorations of `U` as pairs of an upper-block decoration and a local decoration of `T`. -/
@[expose] noncomputable def splitLocalEquiv (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
    (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (βU : Fin 4 → Mom d) :
    CLLocalDecoration RU L base βU ≃
      Σ xS : ExtS RS L base (βU 0) (βU 1), CLLocalDecoration RT L base (bdT RT L base xS.1 (βU 2) (βU 3)) :=
  (clExtEquiv RU L base βU).trans (splitExtEquiv hS hT hi hU RU RS RT hL base βU)

theorem splitLocalEquiv_symm_val (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
    (RT : CLRegionData G T b c) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (βU : Fin 4 → Mom d)
    (p : Σ xS : ExtS RS L base (βU 0) (βU 1), CLLocalDecoration RT L base (bdT RT L base xS.1 (βU 2) (βU 3))) :
    clExtendIndices RU ((splitLocalEquiv hS hT hi hU RU RS RT hL base βU).symm p).1 =
      glue RS p.1.1 (clExtendIndices RT p.2.1) := by
  have h1 : clExtendIndices RU ((splitLocalEquiv hS hT hi hU RU RS RT hL base βU).symm p).1 =
      ((clExtEquiv RU L base βU) ((clExtEquiv RU L base βU).symm
        ((splitExtEquiv hS hT hi hU RU RS RT hL base βU).symm p))).1 := rfl
  rw [h1, Equiv.apply_symm_apply]
  rfl


end Sigma

end WaveTurbulence.VineEstS4
