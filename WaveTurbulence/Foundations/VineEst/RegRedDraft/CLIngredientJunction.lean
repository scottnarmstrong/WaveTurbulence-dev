/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionData
public import WaveTurbulence.Foundations.Molecule.BlockChains

/-! # Actual shared child of consecutive bottom-to-top CL ingredients -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree

 theorem cl_internalPositions_disjoint {w : ℕ} {G : Garden w}
    {A B : Finset (GBranch G.tree)} {a c : GBranch G.tree}
    (hA : G.molecule.IsBlock A a c) (hi : A ∩ B = {c}) :
    Disjoint (Mole.internalPositions G A c) (Mole.internalPositions G B c) := by
  classical
  obtain ⟨hdeg,hconn⟩ := (isBlock_iff_degree_connected _ _ _ _).mp hA
  apply Finset.disjoint_left.mpr
  intro i hia hib
  obtain ⟨x,hx,hAx,hix⟩ := (Mole.mem_internalPositions G).mp hia
  obtain ⟨y,hy,hBy,hiy⟩ := (Mole.mem_internalPositions G).mp hib
  have he : x = y := Mole.atom_position_injective G (Prod.ext (hx.trans hy.symm) (hix.trans hiy.symm))
  subst y
  have hm : G.molecule.atom (G.molecule.mate x) = c := by
    have hmem : G.molecule.atom (G.molecule.mate x) ∈ A ∩ B := Finset.mem_inter.mpr ⟨hAx.2,hBy.2⟩
    rw [hi] at hmem
    exact Finset.mem_singleton.mp hmem
  exact Mole.connected_block_no_joint_loop G.molecule hA hconn (Or.inr hx) (hm.trans hx.symm)

/-- The upper excluded child of ingredient i is exactly the lower retained
child of ingredient i+1. Both slot choices come from actual connected blocks. -/
theorem cl_ingredient_shared_child {w : ℕ} {G : Garden w}
    {A B : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hA : G.molecule.IsBlock A c a) (hB : G.molecule.IsBlock B b c)
    (RA : CLRegionData G A c a) (RB : CLRegionData G B b c)
    (hi : A ∩ B = {c}) : c.child RA.excluded = c.child RB.kept := by
  have hs : G.molecule.IsBlock A a c := Mole.block_swap_joints G.molecule hA
  have hd := cl_internalPositions_disjoint hs hi
  have hb := (RB.lower RB.kept).mpr rfl
  have hn : RB.kept = RA.excluded := by
    by_contra hne
    exact Finset.disjoint_left.mp hd ((RA.upper RB.kept).mpr hne) hb
  exact congrArg c.child hn.symm

end WaveTurbulence.RegRed
