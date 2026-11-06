/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.GardenOfPairsCanonical

/-! # Exact endpoint bijections prohibit duplicate literal pair slots -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem completePairList_nodup {w : ℕ} (tree : Fin w → TTree) (P : List (Pair w))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P)
    (hn : P.length * 2 = Fintype.card (GLeaf tree)) : P.Nodup := by
  let E := endpointEquiv tree P hv hc hn
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  have hh : E (⟨i,hi⟩,0) = E (⟨j,hj⟩,0) := Subtype.ext (congrArg Prod.fst he)
  exact congrArg (fun z : Fin P.length × Fin 2 => z.1.val) (E.injective hh)

end WaveTurbulence.Reg.Skeleton
