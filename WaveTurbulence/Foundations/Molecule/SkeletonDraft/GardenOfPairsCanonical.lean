/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Carrier
public import WaveTurbulence.Foundations.RegStruct.PairSlots

/-! # The garden constructed from a complete oriented list retains exactly its canonical pairs -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem sourcePairs_gardenOfPairs {w : ℕ} (tree : Fin w → TTree) (σ : Fin w → ℤˣ)
    (P : List (Pair w))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P)
    (hn : P.length * 2 = Fintype.card (GLeaf tree))
    (hs : ∀ p ∈ P, nodeSign σ p.1 = 1 ∧ nodeSign σ p.2 = -1) :
    sourcePairs (gardenOfPairs tree σ P hv hc hn hs) = P.toFinset := by
  classical
  let G := gardenOfPairs tree σ P hv hc hn hs
  let E := endpointEquiv tree P hv hc hn
  ext p
  constructor
  · intro hp
    obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hp
    have hpos : nodeSign σ ℓ.1 = 1 := (Finset.mem_filter.mp hℓ).2
    have hpair := gardenOfPairs_pair_mem tree σ P hv hc hn hs ℓ
    rcases (mem_symmPairs_iff _ _).mp hpair with h | h
    · exact List.mem_toFinset.mpr h
    · have hneg := (hs _ h).2
      change nodeSign σ ℓ.1 = -1 at hneg
      rw [hpos] at hneg
      contradiction
  · intro hp
    obtain ⟨i,hi,hei⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hp)
    let x : Fin P.length × Fin 2 := (⟨i,hi⟩,0)
    let ℓ := E x
    have hpair : G.pair ℓ = E (⟨i,hi⟩,1) := by
      change E ((pairSlots P.length).pair (E.symm (E x))) = _
      rw [Equiv.symm_apply_apply]
      rfl
    apply Finset.mem_image.mpr
    refine ⟨ℓ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · exact (hs _ (List.getElem_mem (l := P) hi)).1
    · change (ℓ.1,(G.pair ℓ).1) = p
      rw [hpair]
      change (P[i].1,P[i].2) = p
      simpa only [Prod.eta] using hei

end WaveTurbulence.Reg.Skeleton
