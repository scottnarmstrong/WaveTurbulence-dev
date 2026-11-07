/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Reloc3

/-! # ZP-SURJ: the roots of a pattern lie below the parent layers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {w : ℕ}

theorem layerPatternN_root_le {LG : LayeredGarden w} {pa pb : ℕ} {Q : RegCpl} {a b : Fin w × Path}
    (h : LayerPatternN LG pa pb Q a b) : layerAt LG a ≤ pa ∧ layerAt LG b ≤ pb := by
  obtain ⟨-, h2⟩ := h
  cases Q with
  | triv =>
    have ha := h2 a (left_mem_cplNodes _ a b)
    have hb := h2 b (right_mem_cplNodes _ a b)
    exact ⟨ha ▸ min_le_left _ _, hb ▸ min_le_right _ _⟩
  | type1 c Q₁ Q₂ Q₃ =>
    have ha := h2 a (left_mem_cplNodes _ a b)
    have hb := h2 b (right_mem_cplNodes _ a b)
    exact ⟨ha ▸ min_le_left _ _, hb ▸ min_le_right _ _⟩
  | type2 Xp Xm Qlp =>
    obtain ⟨c1, -, -, c4, c5⟩ := h2
    constructor
    · cases Xp with
      | nil =>
        have h := left_mem_cplNodes Qlp (addrExt a RegChain.nil.lonePath) (addrExt b Xm.lonePath)
        have h1 := c1 _ h
        rw [show addrExt a RegChain.nil.lonePath = a from addrExt_nil a] at h1
        exact h1.trans_le (min_le_left _ _)
      | pair m Qr Qg inner rest =>
        exact (c4 a (root_mem_chainNodesSet m Qr Qg inner rest 1 a)).2
    · cases Xm with
      | nil =>
        have h := right_mem_cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b RegChain.nil.lonePath)
        have h1 := c1 _ h
        rw [show addrExt b RegChain.nil.lonePath = b from addrExt_nil b] at h1
        exact h1.trans_le (min_le_right _ _)
      | pair m Qr Qg inner rest =>
        exact (c5 b (root_mem_chainNodesSet m Qr Qg inner rest (-1) b)).2

theorem treePatternN_root_le {LG : LayeredGarden w} {pa : ℕ} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path}
    (h : TreePatternN LG pa X ζ a) (hX : X.isNil = false) : layerAt LG a ≤ pa := by
  cases X with
  | nil => simp [RegChain.isNil] at hX
  | pair m Qr Qg inner rest =>
    exact (h.2.2 a (root_mem_chainNodesSet m Qr Qg inner rest ζ a)).2

end WaveTurbulence.ZpSurj
