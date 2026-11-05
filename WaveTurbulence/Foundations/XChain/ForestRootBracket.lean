/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BracketFiniteSum
public import WaveTurbulence.Foundations.XChain.ForestLeafLabels
/-! Branch momentum conservation transfers leaf-bracket decay to each literal root. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def latticePointAddHom {d : ℕ} (L : ℝ) : (Fin d → ℤ) →+ Mom d where
  toFun := latticePoint L
  map_zero' := by ext j; simp [latticePoint]
  map_add' n m := by ext j; simp [latticePoint, add_div]

theorem latticePoint_units_smul {d : ℕ} (L : ℝ) (ζ : ℤˣ) (n : Fin d → ℤ) :
    latticePoint L ((ζ : ℤ) • n) = (ζ : ℤ) • latticePoint L n :=
  (latticePointAddHom L).map_zsmul (ζ : ℤ) n

theorem forest_root_jbr_le {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) (L : ℝ) (j : Fin w) :
    jbr (latticePoint L (n j)) ≤
      2 ^ (GNode.root top j).leavesBelow.card *
        ∏ l ∈ (GNode.root top j).leavesBelow, jbr (latticePoint L (κ.1 l.toNode)) := by
  classical
  have hr : n j = ∑ l ∈ (GNode.root top j).leavesBelow,
      (nodeSign (fun _ : Fin w => (1 : ℤˣ)) l.1 : ℤ) • κ.1 l.toNode := by
    have h := sum_rule (fun _ : Fin w => (1 : ℤˣ)) κ.1 κ.2.1 (GNode.root top j)
    have hs : nodeSign (fun _ : Fin w => (1 : ℤˣ)) (GNode.root top j).1 = 1 := by
      simp [nodeSign, GNode.root, TTree.pathSign]
    rw [hs, Units.val_one, one_smul, κ.2.2 j] at h
    exact h
  have hm := congrArg (latticePointAddHom L) hr
  simp only [map_sum] at hm
  change latticePoint L (n j) = ∑ l ∈ (GNode.root top j).leavesBelow,
    latticePoint L ((nodeSign (fun _ : Fin w => (1 : ℤˣ)) l.1 : ℤ) • κ.1 l.toNode) at hm
  rw [hm]
  have hb := jbr_finset_sum_le (GNode.root top j).leavesBelow
    (fun l => latticePoint L ((nodeSign (fun _ : Fin w => (1 : ℤˣ)) l.1 : ℤ) • κ.1 l.toNode))
  simpa only [latticePoint_units_smul, jbr_units_smul] using hb

end WaveTurbulence.Induct
