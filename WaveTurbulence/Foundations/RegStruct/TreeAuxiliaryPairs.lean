/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OneSidedCodeShape

/-! # Recovering the lone position and internal pairs from an auxiliary couple -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- The auxiliary terminal pair in the tree's own orientation. -/
theorem treeAuxCode_cross_pair (X : RegChain) (ζ : ℤˣ) :
    (((if ζ = 1 then 0 else 1 : Fin 2),X.lonePath),(1-(if ζ = 1 then 0 else 1),[])) ∈
      symmPairs (treeAuxCode X ζ).raw.2 := by
  by_cases hζ : ζ = 1
  · subst ζ
    exact (mem_symmPairs_iff _ _).mpr (Or.inl (treeAuxCode_positive_terminal_pair X))
  · have hm : ζ = -1 := (Int.units_eq_one_or _).resolve_left hζ
    subst ζ
    exact (mem_symmPairs_iff _ _).mpr (Or.inr (treeAuxCode_negative_terminal_pair X))

/-- The source tree matching determines the exact lone-leaf path of its chain code. -/
theorem matching_aux_lone_iff (X : RegChain) (G : Garden 1)
    (hM : G.MatchesTreeCouple (treeAuxCode X (G.sig 0)).raw) (ℓ : GLeaf G.tree) :
    G.IsLone ℓ ↔ ℓ.1.2 = X.lonePath := by
  let s : Fin 2 := if G.sig 0 = 1 then 0 else 1
  let C := treeAuxCode X (G.sig 0)
  have hp : ((s,ℓ.1.2),if G.IsLone ℓ then (1-s,[]) else (s,(G.pair ℓ).1.2)) ∈ symmPairs C.raw.2 := hM.2.2 ℓ
  have hc : ((s,X.lonePath),(1-s,[])) ∈ symmPairs C.raw.2 := treeAuxCode_cross_pair X (G.sig 0)
  constructor
  · intro hl
    rw [ite_eq_left hl] at hp
    have hps := symmPairs_swap_mem C.raw.2 _ hp
    have hcs := symmPairs_swap_mem C.raw.2 _ hc
    have he := decodedPair_functional C hps hcs
    exact congrArg (fun z : Fin 2 × Path => z.2) he
  · intro hpath
    by_contra hl
    rw [ite_eq_right hl,hpath] at hp
    have he := decodedPair_functional C hp hc
    have hs := congrArg (fun z : Fin 2 × Path => z.1) he
    have hbad : ∀ t : Fin 2, t ≠ 1-t := by intro t; fin_cases t <;> decide
    exact hbad s hs

/-- The auxiliary positive pair list consists exactly of internal pairs and the lone-root pair. -/
theorem treeAuxCode_positive_mem (X : RegChain) (p : (Fin 2 × Path) × (Fin 2 × Path)) :
    p ∈ (treeAuxCode X 1).raw.2 ↔ p ∈ X.pairsAt 1 (0,[]) ∨ p = ((0,X.lonePath),(1,[])) := by
  rw [treeAuxCode,ite_eq_left rfl]
  change p ∈ (joinChains X .nil .triv).pairsAt (0,[]) (1,[]) ↔ _
  rw [mem_joinChains_pairsAt]
  simp [RegChain.pairsAt,RegChain.lonePath,RegCpl.pairsAt,addrExt]

/-- The negative orientation has the analogous source pair list. -/
theorem treeAuxCode_negative_mem (X : RegChain) (p : (Fin 2 × Path) × (Fin 2 × Path)) :
    p ∈ (treeAuxCode X (-1)).raw.2 ↔ p ∈ X.pairsAt (-1) (1,[]) ∨ p = ((0,[]),(1,X.lonePath)) := by
  rw [treeAuxCode,ite_eq_right (by decide)]
  change p ∈ (joinChains .nil X .triv).pairsAt (0,[]) (1,[]) ↔ _
  rw [mem_joinChains_pairsAt]
  simp [RegChain.pairsAt,RegChain.lonePath,RegCpl.pairsAt,addrExt]

/-- Same-side positive pairs are exactly the chain's internal pairs. -/
theorem treeAuxCode_positive_internal (X : RegChain) (p q : Path)
    (hp : (((0 : Fin 2),p),(0,q)) ∈ symmPairs (treeAuxCode X 1).raw.2) :
    (((0 : Fin 2),p),(0,q)) ∈ symmPairs (X.pairsAt 1 (0,[])) := by
  rw [mem_symmPairs_iff] at hp ⊢
  simp only [treeAuxCode_positive_mem,Prod.swap,Prod.mk.injEq] at hp
  simpa using hp

/-- Same-side negative pairs are exactly the chain's internal pairs. -/
theorem treeAuxCode_negative_internal (X : RegChain) (p q : Path)
    (hp : (((1 : Fin 2),p),(1,q)) ∈ symmPairs (treeAuxCode X (-1)).raw.2) :
    (((1 : Fin 2),p),(1,q)) ∈ symmPairs (X.pairsAt (-1) (1,[])) := by
  rw [mem_symmPairs_iff] at hp ⊢
  simp only [treeAuxCode_negative_mem,Prod.swap,Prod.mk.injEq] at hp
  simpa using hp

/-- Forget which auxiliary tree carries the actual paired tree. -/
def projectTreeAddress (z : Fin 2 × Path) : Fin 1 × Path := (0,z.2)

/-- Project an actual internal unordered pair to the one-tree code. -/
theorem chain_pairs_project (X : RegChain) (ζ : ℤˣ) (s : Fin 2)
    (p q : Path) (hp : ((s,p),(s,q)) ∈ symmPairs (X.pairsAt ζ (s,[]))) :
    (((0 : Fin 1),p),(0,q)) ∈ symmPairs (X.pairsAt ζ (0,[])) := by
  have hm := chain_pairsAt_map X projectTreeAddress (fun _ _ => rfl) ζ (s,[])
  change X.pairsAt ζ ((0 : Fin 1),[]) = _ at hm
  rw [hm,mem_symmPairs_iff]
  rw [mem_symmPairs_iff] at hp
  rcases hp with hp | hp
  · exact Or.inl (List.mem_map.mpr ⟨((s,p),(s,q)),hp,rfl⟩)
  · exact Or.inr (List.mem_map.mpr ⟨((s,q),(s,p)),hp,rfl⟩)

end WaveTurbulence.Reg
