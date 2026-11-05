/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeSubtreeMembership
public import WaveTurbulence.Foundations.Canon.Decomp
/-! Literal ordered subforests rooted at a finite antichain of original nodes. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def subforestRoot {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (k : Fin U.card) : GNode tree := (U.equivFin.symm k).1

noncomputable def subforestTrees {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (k : Fin U.card) : TTree :=
  subtreeAt (tree (subforestRoot U k).1.1) (subforestRoot U k).1.2

theorem subforestRoot_mem {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (k : Fin U.card) : subforestRoot U k ∈ U := (U.equivFin.symm k).2

noncomputable def subforestLeafMap {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (ℓ : GLeaf (subforestTrees U)) : GLeaf tree :=
  ⟨((subforestRoot U ℓ.1.1).1.1, (subforestRoot U ℓ.1.1).1.2 ++ ℓ.1.2),
    (subtreeAt_leaves_iff _ _ (subforestRoot U ℓ.1.1).2 _).mp ℓ.2⟩

theorem subforestLeafMap_below {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (ℓ : GLeaf (subforestTrees U)) :
    (subforestRoot U ℓ.1.1).IsDesc (subforestLeafMap U ℓ).toNode :=
  ⟨rfl, List.prefix_append _ _⟩

theorem subforestLeafMap_injective {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U) :
    Function.Injective (subforestLeafMap U) := by
  intro a b hab
  have hda := subforestLeafMap_below U a
  have hdb : (subforestRoot U b.1.1).IsDesc (subforestLeafMap U a).toNode :=
    hab.symm ▸ subforestLeafMap_below U b
  have he : subforestRoot U a.1.1 = subforestRoot U b.1.1 := by
    by_contra hne
    have hinc := hU _ (subforestRoot_mem U a.1.1) _ (subforestRoot_mem U b.1.1) hne
    rcases Canon.isDesc_total hda hdb with h | h
    · exact hinc.1 h
    · exact hinc.2 h
  have hi : a.1.1 = b.1.1 := (U.equivFin.symm).injective (Subtype.ext he)
  have hp := congrArg (fun ℓ : GLeaf LG.garden.tree => ℓ.1.2) hab
  have hs := congrArg (fun u : GNode LG.garden.tree => u.1.2) he
  have hpath : a.1.2 = b.1.2 := List.append_cancel_left
    (hp.trans (congrArg (fun s => s ++ b.1.2) hs.symm))
  exact Subtype.ext (Prod.ext hi hpath)

noncomputable def subforestLeafEmbedding {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U) :
    GLeaf (subforestTrees U) ↪ GLeaf LG.garden.tree :=
  ⟨subforestLeafMap U, subforestLeafMap_injective LG U hU⟩

theorem subforestRoot_equivFin {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (u : ↥U) : subforestRoot U (U.equivFin u) = u.1 :=
  congrArg Subtype.val (U.equivFin.symm_apply_apply u)

theorem subforestTrees_equivFin {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (u : ↥U) :
    subforestTrees U (U.equivFin u) = subtreeAt (tree u.1.1.1) u.1.1.2 :=
  congrArg (fun a : GNode tree => subtreeAt (tree a.1.1) a.1.2) (subforestRoot_equivFin U u)

noncomputable def subforestLeafEquiv {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U) :
    GLeaf (subforestTrees U) ≃ ↥(LG.leavesBelowSet U) :=
  Equiv.ofBijective (fun ℓ => ⟨subforestLeafMap U ℓ,
    Canon.Rel.mem_leavesBelowSet.mpr ⟨subforestRoot U ℓ.1.1, subforestRoot_mem U ℓ.1.1,
      subforestLeafMap_below U ℓ⟩⟩) (by
    constructor
    · intro a b he
      exact subforestLeafMap_injective LG U hU (congrArg Subtype.val he)
    · rintro ⟨ℓ, hℓ⟩
      obtain ⟨u, hu, hr, hp⟩ := Canon.Rel.mem_leavesBelowSet.mp hℓ
      obtain ⟨b, hb⟩ := hp
      let k := U.equivFin ⟨u, hu⟩
      have hmem : b ∈ (subforestTrees U k).leaves := by
        rw [subforestTrees_equivFin U ⟨u, hu⟩]
        apply (subtreeAt_leaves_iff _ _ u.2 b).mpr
        rw [hb, hr]
        exact ℓ.2
      let a : GLeaf (subforestTrees U) := ⟨(k, b), hmem⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have he := subforestRoot_equivFin U ⟨u, hu⟩
      have hv := congrArg (fun z : GNode LG.garden.tree => (z.1.1, z.1.2 ++ b)) he
      exact hv.trans (Prod.ext hr hb))

end WaveTurbulence.Induct
