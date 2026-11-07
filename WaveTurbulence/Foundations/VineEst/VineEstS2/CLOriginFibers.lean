/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLeafOrigins

/-! # Exact fibers of the regional leaf-origin map -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clLeafOrigin_eq_pair_iff (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (l : GLeaf (CLTreeForest R)) (p : ↥(clRegionalPairs hG U)) :
    clLeafOrigin hU R hG l = .inl p ↔
      l = clPairFirstLeaf hU R hG p ∨ l = clPairSecondLeaf hU R hG p := by
  constructor
  · obtain ⟨x,rfl⟩ := (clLeafEquiv hU R hG).surjective l
    rw [clLeafOrigin_apply]
    rcases x with ⟨q,c⟩ | j
    · intro hp
      have hq : q = p := Sum.inl.inj hp
      subst q
      have hc : c = 0 ∨ c = 1 := by omega
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hp
      cases hp
  · rintro (rfl | rfl)
    · exact clLeafOrigin_first hU R hG p
    · exact clLeafOrigin_second hU R hG p

theorem clLeafOrigin_eq_boundary_iff (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (l : GLeaf (CLTreeForest R)) (j : Fin 3) :
    clLeafOrigin hU R hG l = .inr j.succ ↔ l = clBoundaryLeaf hU R j := by
  constructor
  · obtain ⟨x,rfl⟩ := (clLeafEquiv hU R hG).surjective l
    rw [clLeafOrigin_apply]
    rcases x with ⟨p,c⟩ | k
    · intro hp
      cases hp
    · intro hk
      have he : k = j := Fin.ext (by have := congrArg Fin.val (Sum.inr.inj hk); simpa using this)
      subst k
      rfl
  · rintro rfl
    exact clLeafOrigin_boundary hU R hG j

theorem clLeafOrigin_ne_upper (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (l : GLeaf (CLTreeForest R)) : clLeafOrigin hU R hG l ≠ .inr 0 := by
  obtain ⟨x,rfl⟩ := (clLeafEquiv hU R hG).surjective l
  rw [clLeafOrigin_apply]
  rcases x with ⟨p,c⟩ | j
  · intro hj
    cases hj
  · intro hj
    have := congrArg Fin.val (Sum.inr.inj hj)
    simp only [Fin.val_succ,Fin.val_zero] at this
    omega

end WaveTurbulence.VineEstS2
