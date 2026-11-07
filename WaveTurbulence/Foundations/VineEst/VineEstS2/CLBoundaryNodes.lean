/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLBoundaryIsolation

/-! # The four boundary node addresses are distinct -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clBoundaryNodes_injective (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    Function.Injective (clBoundaryNodes R) := by
  have hlt := (Mole.cl_parent_strict_descendant G hU
    R.parentPattern).2
  have h0 : (clBoundaryNodes R 0).1.2.length = a.1.2.length := rfl
  have h1 : (clBoundaryNodes R 1).1.2.length = a.1.2.length+1 := by
    change (a.1.2++[R.excluded]).length = _
    rw [List.length_append,List.length_singleton]
  have h2 : (clBoundaryNodes R 2).1.2.length = b.1.2.length+1 := by
    change (b.1.2++[R.positive]).length = _
    rw [List.length_append,List.length_singleton]
  have h3 : (clBoundaryNodes R 3).1.2.length = b.1.2.length+1 := by
    change (b.1.2++[R.negative]).length = _
    rw [List.length_append,List.length_singleton]
  intro i j he
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;> try rfl
  all_goals
    have hd := congrArg (fun x : GNode G.tree => x.1.2.length) he
    simp only [h0,h1,h2,h3] at hd
    try omega
  all_goals
    have hs := congrArg (fun x : GNode G.tree => (G.sign x : ℤ)) he
    norm_num [clBoundaryNodes,R.positive_sign,R.negative_sign] at hs

end WaveTurbulence.VineEstS2
