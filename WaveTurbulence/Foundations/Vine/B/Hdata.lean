/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.PointB
import Mathlib.Tactic

/-!
# VINE-B: the unit data of `G_sb` (`hclk`, `hmom`)

For a unit `j`: `hmom j` are the four `G_sb` nodes mapping to `clBoundaryNodes` (`u1, u11, u21, u22`), `hclk j` the
three exterior clock sources (`t_{u1}` is the hinge clock, a leaf boundary child gets the root time of its tree).
`bdry_eq`: the boundary momenta of a decoration `z` of `G_sb` are `z ∘ hmom j`.  `clocks_eq_hclk`: the exterior
clocks `clocks τ' j` agree with `clockOf ∘ hclk j` (up to the unused clock of a leaf boundary child).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

/-- The clock source of a node of `G_sb` that is a branch (its own clock), else the root time of its tree. -/
noncomputable def nodeClk (G : Garden w) (y : GNode G.tree) : ClkSrc G := by
  classical
  exact if h : y.1.2 ∈ (G.tree y.1.1).branching then Sum.inr ⟨y.1, h⟩ else Sum.inl y.1.1

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- The four boundary nodes `u1, u11, u21, u22` of unit `j` as nodes of `G_sb`. -/
noncomputable def hmom (hd : Disj blk) (j : J) (i : Fin 4) : GNode Gsb.tree :=
  Φ.nodeEquiv.symm ⟨clBoundaryNodes (regionOf (blk j)) i, Φ.ret_bdryNode hd j i⟩

theorem node_hmom (hd : Disj blk) (j : J) (i : Fin 4) :
    Φ.node (Φ.hmom hd j i) = clBoundaryNodes (regionOf (blk j)) i :=
  Φ.node_nodeEquiv_symm ⟨clBoundaryNodes (regionOf (blk j)) i, Φ.ret_bdryNode hd j i⟩

theorem bdry_eq (hd : Disj blk) (L : ℝ) (base : Mom d) (z : GNode Gsb.tree → (Fin d → ℤ)) (j : J) :
    Φ.bdry L base z j = fun i => base + latticePoint L (z (Φ.hmom hd j i)) := by
  funext i
  unfold bdry
  rw [← Φ.node_hmom hd j i, Φ.ext_node]

/-- The exterior clock sources of unit `j`. -/
noncomputable def hclk (hd : Disj blk) (j : J) : Fin 3 → ClkSrc Gsb :=
  ![Sum.inr (Φ.hinge hd j), nodeClk Gsb (Φ.hmom hd j 2), nodeClk Gsb (Φ.hmom hd j 3)]

/-- A node of `G_sb` is a branching node iff its image is. -/
theorem branching_iff (y : GNode Gsb.tree) :
    y.1.2 ∈ (Gsb.tree y.1.1).branching ↔ (Φ.node y).1.2 ∈ (S.tree (Φ.node y).1.1).branching := by
  rcases node_cases y with ⟨c, rfl⟩ | ⟨ℓ, rfl⟩
  · constructor
    · intro _
      rw [← Φ.br_node]
      exact (Φ.br c).2
    · intro _; exact c.2
  · constructor
    · intro hb
      exact (TTree.not_mem_branching_of_mem_leaves _ ℓ.2 hb).elim
    · intro hb
      rw [← Φ.leaf_node] at hb
      exact (TTree.not_mem_branching_of_mem_leaves _ (Φ.leaf ℓ).2 hb).elim

theorem clock_hmom (hd : Disj blk) (tt : Fin w → ℝ) (τ' : GBranch Gsb.tree → ℝ) (j : J) (i : Fin 4)
    (hb : (clBoundaryNodes (regionOf (blk j)) i).1.2 ∈
      (S.tree (clBoundaryNodes (regionOf (blk j)) i).1.1).branching) :
    clBranchClock (Φ.extTime τ') (clBoundaryNodes (regionOf (blk j)) i) =
      clockOf Gsb tt τ' (nodeClk Gsb (Φ.hmom hd j i)) := by
  set y := Φ.hmom hd j i with hy
  have hny := Φ.node_hmom hd j i
  rw [← hny] at hb ⊢
  have hyb : y.1.2 ∈ (Gsb.tree y.1.1).branching := (Φ.branching_iff y).mpr hb
  unfold clBranchClock nodeClk clockOf
  rw [dif_pos hb, dif_pos hyb]
  show Φ.extTime τ' ⟨(Φ.node y).1, hb⟩ = τ' ⟨y.1, hyb⟩
  have : (⟨(Φ.node y).1, hb⟩ : GBranch S.tree) = Φ.br ⟨y.1, hyb⟩ := by
    apply Subtype.ext
    have := Φ.br_node ⟨y.1, hyb⟩
    exact (congrArg (fun x : GNode S.tree => x.1) this).symm
  rw [this]
  exact Φ.extTime_br τ' ⟨y.1, hyb⟩

end SpliceShape

end WaveTurbulence.VineB
