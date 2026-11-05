/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.UnitTwistInvolution

/-! # Exact sign cancellation for a unit-twist pair

TARGET twistexplain (b) and the cancellation opened by the twist. The
branch sign product is negated. Consequently the two signed terms cancel
for a common amplitude; this is not an assertion that the original
unequal time-integration domains agree pointwise.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- The actual product of all branching signs. -/
@[expose] def branchSignProduct {w : ℕ} (G : Garden w) : ℤˣ :=
  ∏ b : GBranch G.tree, G.sign b.toNode

/-- The actual unit twist negates the full branching sign product. -/
theorem branchSignProduct_unitTwist {w : ℕ} (G : Garden w) (P : CorePlacement G) :
    branchSignProduct (unitTwistGarden G P) = -branchSignProduct G := by
  classical
  have he := Fintype.prod_equiv (coreBranchEquiv G P)
    (fun b => (unitTwistGarden G P).sign (coreBranchEquiv G P b).toNode)
    (fun b => (unitTwistGarden G P).sign b.toNode) (fun _ => rfl)
  change (∏ b : GBranch (coreTwistForest G P), (unitTwistGarden G P).sign b.toNode) = _
  rw [← he]
  simp_rw [coreBranchEquiv_sign]
  have hprod : (∏ b : GBranch G.tree, if b = P.lower then -G.sign b.toNode else G.sign b.toNode) =
      (∏ b : GBranch G.tree, if b = P.lower then (-1 : ℤˣ) else 1) * branchSignProduct G := by
    unfold branchSignProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro b _hb
    split <;> simp
  rw [hprod]
  simp

/-- Two actual unit-twist signs cancel against a common complex amplitude. -/
theorem unitTwist_common_amplitude_cancel {w : ℕ} (G : Garden w) (P : CorePlacement G) (A : ℂ) :
    (((branchSignProduct G : ℤ) : ℂ) * A) +
      (((branchSignProduct (unitTwistGarden G P) : ℤ) : ℂ) * A) = 0 := by
  rw [branchSignProduct_unitTwist]
  simp

end WaveTurbulence.Twist
