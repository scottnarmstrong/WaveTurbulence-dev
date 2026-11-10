/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.DecSplit
import Mathlib.Tactic

/-!
# VINE-B: gluing decorations, and the decoration equivalence

`decSplit`: `GenDecoration S ≃ Σ z : GenDecoration G_sb, Π_j CLLocalDecoration (U_j) (bdry z j)` (TARGET L1950–L1957).
The inverse glues the local decorations into the retained values; the four boundary momenta of a local decoration
fix its lattice values at the joints and the boundary nodes (`L ≠ 0`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- Glue a function on `G_sb` and local functions on the unit supports. -/
noncomputable def glueFun (z : GNode Gsb.tree → (Fin d → ℤ))
    (κs : ∀ j, ↥(clLocalSupport (regionOf (blk j))) → (Fin d → ℤ)) (x : GNode S.tree) : Fin d → ℤ := by
  classical
  exact if h : ∃ j, x ∈ clRealizationNodes S (blk j).atoms ∧ x ≠ (blk j).upper.toNode then
    clExtendIndices (regionOf (blk (Classical.choose h))) (κs (Classical.choose h)) x else Φ.ext z x

theorem glue_ret (z : GNode Gsb.tree → (Fin d → ℤ)) (κs : ∀ j, ↥(clLocalSupport (regionOf (blk j))) → (Fin d → ℤ))
    {x : GNode S.tree} (hx : Ret blk x) : Φ.glueFun z κs x = Φ.ext z x := by
  classical
  unfold glueFun
  rw [dite_eq_right_iff.mpr]
  rintro ⟨j, h1, h2⟩
  exact (not_ret_of_interior h1 h2 hx).elim

theorem glue_interior (hd : Disj blk) (z : GNode Gsb.tree → (Fin d → ℤ))
    (κs : ∀ j, ↥(clLocalSupport (regionOf (blk j))) → (Fin d → ℤ)) {x : GNode S.tree} {j : J}
    (h1 : x ∈ clRealizationNodes S (blk j).atoms) (h2 : x ≠ (blk j).upper.toNode) :
    Φ.glueFun z κs x = clExtendIndices (regionOf (blk j)) (κs j) x := by
  classical
  have h : ∃ j, x ∈ clRealizationNodes S (blk j).atoms ∧ x ≠ (blk j).upper.toNode := ⟨j, h1, h2⟩
  unfold glueFun
  rw [dif_pos h]
  have hc := Classical.choose_spec h
  have he : Classical.choose h = j := interior_unique hd hc.1 hc.2 h1
  rw [he]

theorem glue_support (hd : Disj blk) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (z : GNode Gsb.tree → (Fin d → ℤ))
    (κs : ∀ j, ↥(clLocalSupport (regionOf (blk j))) → (Fin d → ℤ)) (j : J)
    (hb : ∀ i, base + latticePoint L (clExtendIndices (regionOf (blk j)) (κs j)
      (clBoundaryNodes (regionOf (blk j)) i)) = Φ.bdry L base z j i)
    {x : GNode S.tree} (hx : x ∈ clLocalSupport (regionOf (blk j))) :
    Φ.glueFun z κs x = clExtendIndices (regionOf (blk j)) (κs j) x := by
  have hbd : ∀ i, Φ.glueFun z κs (clBoundaryNodes (regionOf (blk j)) i) =
      clExtendIndices (regionOf (blk j)) (κs j) (clBoundaryNodes (regionOf (blk j)) i) := by
    intro i
    rw [Φ.glue_ret z κs (ret_bdryNode Φ hd j i)]
    exact (latticePoint_injective_of_ne_zero hL (add_left_cancel (hb i))).symm
  rcases Finset.mem_union.mp hx with h | h
  · by_cases he : x = (blk j).upper.toNode
    · subst he; exact hbd 0
    · exact Φ.glue_interior hd z κs h he
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
    exact hbd i

/-- The glued skeleton decoration. -/
noncomputable def glueDec (hS : S.IsPlain) (hd : Disj blk) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    GenDecoration S d roots 0 := by
  refine ⟨Φ.glueFun z.1 (fun j => (κs j).1), ⟨fun v => ?_, fun ℓ => ?_⟩, fun i => ?_, fun ℓ hℓ => ?_⟩
  · by_cases hv : ∃ j, v ∈ (blk j).atoms
    · obtain ⟨j, hj⟩ := hv
      have hs := fun x hx => Φ.glue_support hd hL base z.1 (fun j => (κs j).1) j (κs j).2.2.2 (x := x) hx
      rw [hs _ (cl_realization_mem_support _ ((branch_mem_clRealizationNodes v).mpr hj)),
        hs _ (cl_child_mem_support (blk j).isBlock _ hj 0), hs _ (cl_child_mem_support (blk j).isBlock _ hj 1),
        hs _ (cl_child_mem_support (blk j).isBlock _ hj 2)]
      exact (κs j).2.1 v hj
    · push Not at hv
      have hr : Ret blk v.toNode := (ret_branch_iff v).mpr fun j => Or.inl (hv j)
      have hh : ∀ j, v ≠ (blk j).upper := fun j h => hv j (h ▸ upper_mem _)
      obtain ⟨c, rfl⟩ := Φ.exists_br hr
      have hh' : ∀ j, Φ.br c ≠ (blk j).upper := hh
      have hc : ∀ i, Φ.glueFun z.1 (fun j => (κs j).1) ((Φ.br c).child i) = z.1 (c.child i) := fun i => by
        rw [Φ.glue_ret _ _ (ret_child hr hh i), ← Φ.child c i hh', Φ.ext_node]
      rw [hc 0, hc 1, hc 2, Φ.glue_ret _ _ hr, Φ.br_node, Φ.ext_node]
      exact z.2.1.1 c
  · by_cases hr : Ret blk ℓ.toNode
    · obtain ⟨m, rfl⟩ := Φ.exists_leaf hr
      rw [← Φ.pair, Φ.glue_ret _ _ hr, Φ.glue_ret _ _ (Φ.ret_leaf _), Φ.leaf_node, Φ.leaf_node, Φ.ext_node,
        Φ.ext_node]
      exact z.2.1.2 m
    · rcases ret_or_interior (blk := blk) ℓ.toNode with h | ⟨j, h1, h2⟩
      · exact (hr h).elim
      have hℓ : Mole.IsInternalLeaf S (blk j).atoms ℓ := (leaf_mem_clRealizationNodes ℓ).mp h1
      have hs := fun x hx => Φ.glue_support hd hL base z.1 (fun j => (κs j).1) j (κs j).2.2.2 (x := x) hx
      rw [hs _ (cl_realization_mem_support _ h1),
        hs _ (cl_realization_mem_support _ ((leaf_mem_clRealizationNodes _).mpr
          ((Mole.internal_leaf_pair_iff S _ ℓ).mpr hℓ)))]
      exact (κs j).2.2.1 ℓ hℓ
  · rw [← Φ.root, Φ.glue_ret _ _ (Φ.ret_node _), Φ.ext_node]
    exact z.2.2.1 i
  · exact absurd hℓ (by simp [Garden.IsFlower, hS ℓ])

theorem glueDec_val (hS : S.IsPlain) (hd : Disj blk) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    (Φ.glueDec hS hd hL base z κs).1 = Φ.glueFun z.1 (fun j => (κs j).1) := rfl

theorem resDec_val (hS : S.IsPlain) (hd : Disj blk) {roots : Fin w → (Fin d → ℤ)}
    (κ : GenDecoration S d roots 0) : (Φ.resDec hS hd κ).1 = fun y => κ.1 (Φ.node y) := rfl

theorem resLoc_val (hS : S.IsPlain) (hd : Disj blk) {L : ℝ} {base : Mom d}
    {roots : Fin w → (Fin d → ℤ)} (κ : GenDecoration S d roots 0) (j : J) :
    (Φ.resLoc hS hd κ j (L := L) (base := base)).1 = fun x => κ.1 x.1 := rfl

theorem sigma_ext_dec {L : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)}
    {z z' : GenDecoration Gsb d roots 0} (h : z.1 = z'.1)
    {κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)}
    {κs' : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z'.1 j)}
    (h2 : ∀ j, (κs j).1 = (κs' j).1) :
    (⟨z, κs⟩ : Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) = ⟨z', κs'⟩ := by
  have hz : z = z' := Subtype.ext h
  subst hz
  congr 1
  funext j
  exact Subtype.ext (h2 j)

/-- **The decoration split** (TARGET L1950–L1957). -/
noncomputable def decSplit (hS : S.IsPlain) (hd : Disj blk) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) :
    GenDecoration S d roots 0 ≃
      Σ z : GenDecoration Gsb d roots 0, ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j) where
  toFun κ := ⟨Φ.resDec hS hd κ, fun j => Φ.resLoc hS hd κ j⟩
  invFun p := Φ.glueDec hS hd hL base p.1 p.2
  left_inv κ := by
    apply Subtype.ext
    funext x
    show (Φ.glueDec hS hd hL base (Φ.resDec hS hd κ) (fun j => Φ.resLoc hS hd κ j)).1 x = κ.1 x
    rw [Φ.glueDec_val]
    rcases ret_or_interior (blk := blk) x with h | ⟨j, h1, h2⟩
    · rw [Φ.glue_ret _ _ h]
      exact Φ.ext_resDec hS hd κ h
    · rw [Φ.glue_interior hd _ _ h1 h2, Φ.resLoc_val]
      exact clExtendIndices_restrict _ κ.1 x (cl_realization_mem_support _ h1)
  right_inv p := by
    obtain ⟨z, κs⟩ := p
    apply Φ.sigma_ext_dec
    · funext y
      show (Φ.glueDec hS hd hL base z κs).1 (Φ.node y) = z.1 y
      rw [Φ.glueDec_val, Φ.glue_ret _ _ (Φ.ret_node y), Φ.ext_node]
    · intro j
      funext x
      show (Φ.glueDec hS hd hL base z κs).1 x.1 = (κs j).1 x
      rw [Φ.glueDec_val, Φ.glue_support hd hL base z.1 (fun j => (κs j).1) j (κs j).2.2.2 x.2]
      exact clExtendIndices_apply _ _ _ x.2

end SpliceShape

end WaveTurbulence.VineB
