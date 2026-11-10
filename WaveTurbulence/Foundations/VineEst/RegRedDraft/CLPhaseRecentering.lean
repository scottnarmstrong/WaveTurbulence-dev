/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLBoundaryIdentities
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PhaseRecentering
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PhaseFactorization

/-! # Actual four-boundary phase recentering in TARGET vineest Step 1 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree

noncomputable def boundaryEnergyFromMomenta {d : ℕ} (ζ : ℤˣ) (e f g h : Mom d) : ℝ :=
  ((ζ : ℤ) : ℝ) * ‖f‖^2 + ‖g‖^2 - ‖h‖^2 - ((ζ : ℤ) : ℝ) * ‖e‖^2

theorem clBoundaryEnergy_eq_fourMomenta {w d : ℕ} {G : Garden w}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (D : CLRegionData G S a b)
    (k : GNode G.tree → Mom d) :
    clBoundaryEnergy D k = boundaryEnergyFromMomenta (G.sign a.toNode)
      (k a.toNode) (k (a.child D.excluded)) (k (b.child D.positive)) (k (b.child D.negative)) := by
  unfold clBoundaryEnergy boundaryEnergyFromMomenta
  rw [Mole.outer_child_sign G a D.excluded D.excluded_ne_middle,D.positive_sign,D.negative_sign]
  simp only [Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul]
  ring

end WaveTurbulence.RegRed
