/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Piece
public import WaveTurbulence.Foundations.Vine.B.TimeDomain

/-! # B3s-HELPER5 (γ) T1, transport step 1: core stem nodes read on the skeleton

The first step of the class-common transport of T1 (see `PROGRESS.md` for the plan). On any decoded garden, whether
the core branch of a skeleton branch `β` lies on a capped stem is a property of the skeleton alone: it is iff `β` is
an ancestor of the skeleton leaf that owns a capped flower (`corePosition_onStem_iff`). Through a splice shape this
is a statement about `G_sb` (shape ancestry, next step), and the owner of the flower is the `G_sb` partner of the cap
root, the same for every member of a run class.

* `onStem_of_desc`: `β` an ancestor of the leaf `σ` owning a capped flower ⇒ the core of `β` is a stem address;
* `desc_of_onStem`: the core of `β` below… a capped flower `ℓ` ⇒ `β` is an ancestor of the owner of `ℓ`;
* **`corePosition_onStem_iff`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.Flower.MkMark (owner CapFlowerAt mem_ownRegion_owner owner_isDesc_of_addrBelow)

namespace WaveTurbulence.Flower.MkSlotsT

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) {LG : LayeredGarden w} {J : Finset (Fin w)}

/-- An ancestor of the leaf owning a capped flower has its core on the capped stem. -/
theorem onStem_of_desc {ℓ : Address w} (hℓ : CapFlowerAt LG J ℓ) {σ : GLeaf S.tree}
    (hσ : owner S D.tree ℓ = σ.toNode) {β : GBranch S.tree} (hβ : β.toNode.IsDesc σ.toNode) :
    OnStemAddr LG J (D.corePosition β) := by
  have hne : β.toNode ≠ σ.toNode := fun h => Mole.branch_toNode_ne_leaf β σ h
  obtain ⟨i, hi⟩ := VineB.exists_child_isDesc β hβ hne
  have h1 : AddrBelow (D.corePosition β) (inflatedPosition S D.tree (β.child i)) := by
    rw [D.core_child_position β i]
    exact MkMark.addrBelow_addrExt _ _
  have h2 : AddrBelow (inflatedPosition S D.tree (β.child i)) (inflatedPosition S D.tree σ.toNode) :=
    MkMark.addrBelow_inflatedPosition S D.tree hi
  have h3 : AddrBelow (inflatedPosition S D.tree σ.toNode) ℓ := by
    have := (mem_ownRegion_owner S D.tree ℓ).1
    rwa [hσ] at this
  exact ⟨ℓ, hℓ, MkMark.addrBelow_trans h1 (MkMark.addrBelow_trans h2 h3)⟩

/-- A core on the capped stem of a flower `ℓ` is an ancestor of the owner of `ℓ`. -/
theorem desc_of_onStem {ℓ : Address w} {β : GBranch S.tree} (h : AddrBelow (D.corePosition β) ℓ) :
    β.toNode.IsDesc (owner S D.tree ℓ) := by
  have := owner_isDesc_of_addrBelow S D.tree h
  rwa [owner_corePosition D β] at this

/-- **Core stem nodes are read on the skeleton** (given that capped flowers are owned by skeleton leaves). -/
theorem corePosition_onStem_iff (hleaf : ∀ ℓ, CapFlowerAt LG J ℓ → ∃ σ : GLeaf S.tree, owner S D.tree ℓ = σ.toNode)
    (β : GBranch S.tree) :
    OnStemAddr LG J (D.corePosition β) ↔
      ∃ ℓ, CapFlowerAt LG J ℓ ∧ ∃ σ : GLeaf S.tree, owner S D.tree ℓ = σ.toNode ∧ β.toNode.IsDesc σ.toNode := by
  constructor
  · rintro ⟨ℓ, hℓ, hb⟩
    obtain ⟨σ, hσ⟩ := hleaf ℓ hℓ
    have := desc_of_onStem D hb
    rw [hσ] at this
    exact ⟨ℓ, hℓ, σ, hσ, this⟩
  · rintro ⟨ℓ, hℓ, σ, hσ, hβ⟩
    exact onStem_of_desc D hℓ hσ hβ

end WaveTurbulence.Flower.MkSlotsT
