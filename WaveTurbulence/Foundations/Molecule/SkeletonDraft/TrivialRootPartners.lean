/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.TrivialGardens
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData

/-! # The actual root-pair involution of a trivial skeleton -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Reg.Skeleton
open TTree

noncomputable def IsTrivialGarden.rootLeaf {w : ℕ} {S : Garden w}
    (hS : IsTrivialGarden S) (j : Fin w) : GLeaf S.tree :=
  ⟨(j,[]),by rw [hS.2 j]; exact Finset.mem_singleton_self _⟩

theorem IsTrivialGarden.leaf_path_nil {w : ℕ} {S : Garden w}
    (hS : IsTrivialGarden S) (ℓ : GLeaf S.tree) : ℓ.1.2 = [] := by
  have h := ℓ.2
  rw [hS.2 ℓ.1.1] at h
  exact Finset.mem_singleton.mp h

theorem IsTrivialGarden.leaf_eq_rootLeaf {w : ℕ} {S : Garden w}
    (hS : IsTrivialGarden S) (ℓ : GLeaf S.tree) : ℓ = hS.rootLeaf ℓ.1.1 :=
  Subtype.ext (Prod.ext rfl (hS.leaf_path_nil ℓ))

noncomputable def IsTrivialGarden.rootPartner {w : ℕ} {S : Garden w}
    (hS : IsTrivialGarden S) (j : Fin w) : Fin w := (S.pair (hS.rootLeaf j)).1.1

theorem IsTrivialGarden.rootLeaf_partner {w : ℕ} {S : Garden w}
    (hS : IsTrivialGarden S) (j : Fin w) :
    hS.rootLeaf (hS.rootPartner j) = S.pair (hS.rootLeaf j) :=
  (hS.leaf_eq_rootLeaf _).symm

theorem IsTrivialGarden.rootPartner_involutive {w : ℕ} {S : Garden w}
    (hS : IsTrivialGarden S) : Function.Involutive hS.rootPartner := by
  intro j
  change (S.pair (hS.rootLeaf (hS.rootPartner j))).1.1 = j
  rw [hS.rootLeaf_partner,S.pair_pair]
  rfl

theorem IsTrivialGarden.rootPartner_ne {w : ℕ} {S : Garden w}
    (hS : IsTrivialGarden S) (j : Fin w) : hS.rootPartner j ≠ j := by
  intro he
  apply Comb.pair_ne_of_plain hS.1 (hS.rootLeaf j)
  rw [← hS.rootLeaf_partner,he]

end WaveTurbulence.Reg.Skeleton
