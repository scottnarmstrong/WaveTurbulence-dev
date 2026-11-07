/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.AttachmentMomenta
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairAtSides

/-! # Every actual decoration descends to the original skeleton -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem attachedNode_root {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (j : Fin w) :
    attachedNode D hS (GNode.root S.tree j) = GNode.root (D.forest hS) j :=
  Subtype.ext (inflatedPosition_root S D.tree j)

theorem attachedNode_child {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (i : Fin 3) :
    attachedNode D hS (b.child i) = (D.coreBranch hS b).child i :=
  Subtype.ext (D.core_child_position b i)

/-- TARGET regred: collapsing regular pieces yields a genuine source decoration
of the skeleton. The skeleton conservation and matching equations are derived. -/
theorem collapsed_isDecoration {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {V : Type*} [AddCommGroup V] (κ : GNode (D.forest hS) → V)
    (hκ : IsDecoration (D.garden hS) κ) :
    IsDecoration S (fun a => κ (attachedNode D hS a)) := by
  constructor
  · intro b
    exact (chain_attachment_momentum D hS κ hκ b).trans
      ((hκ.1 (D.coreBranch hS b)).trans
        (congrArg₂ (· + ·)
          (congrArg₂ (· - ·) (congrArg κ (attachedNode_child D hS b 0)).symm
            (congrArg κ (attachedNode_child D hS b 1)).symm)
          (congrArg κ (attachedNode_child D hS b 2)).symm))
  · intro ℓ
    have h := couple_attachment_momentum D hS κ hκ (pairOfLeaf S hS ℓ)
    by_cases hs : nodeSign S.sig ℓ.1 = 1
    · obtain ⟨h₁,h₂⟩ := pairOfLeaf_sides_pos S hS ℓ hs
      rw [h₁,h₂] at h
      exact h
    · obtain ⟨h₁,h₂⟩ := pairOfLeaf_sides_neg S hS ℓ hs
      rw [h₁,h₂] at h
      exact h.symm

noncomputable def collapseGenDecoration {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) : GenDecoration S d n nfl :=
  ⟨fun a => κ.1 (attachedNode D hS a),collapsed_isDecoration D hS κ.1 κ.2.1,
    fun j => (congrArg κ.1 (attachedNode_root D hS j)).trans (κ.2.2.1 j),
    fun ℓ hℓ => (by
      have hm := hS ℓ
      change S.mark ℓ = some .equal at hℓ
      rw [hℓ] at hm
      contradiction)⟩

end WaveTurbulence.RegRed
