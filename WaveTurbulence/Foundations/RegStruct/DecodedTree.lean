/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PairSlotsWithLoneProperties
public import WaveTurbulence.Foundations.RegStruct.ChainMiniFidelity

/-! # The actual paired-tree carrier of every chain code -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- Actual one-tree forest decoded by the chain. -/
def chainTreeForest (X : RegChain) (ζ : ℤˣ) : Fin 1 → TTree := fun _ => X.plug ζ .leaf

/-- The chain's actual distinguished terminal leaf. -/
def chainLoneLeaf (X : RegChain) (ζ : ℤˣ) : GLeaf (chainTreeForest X ζ) :=
  ⟨(0,X.lonePath),chain_lone_mem_leaves X ζ⟩

/-- Leaf membership at the original one-tree root is literal path membership. -/
theorem leafAddresses_one_root (t : TTree) (z : Fin 1 × Path) :
    z ∈ leafAddresses t (0,[]) ↔ z.2 ∈ t.leaves := by
  obtain ⟨j,p⟩ := z
  fin_cases j
  simp [leafAddresses,addrExt]

/-- Every chain pair endpoint is an actual leaf of its decoded one-tree forest. -/
theorem decodedTree_pairs_valid (X : RegChain) (ζ : ℤˣ)
    (p : (Fin 1 × Path) × (Fin 1 × Path)) (hp : p ∈ X.pairsAt ζ (0,[])) :
    p.1.2 ∈ (chainTreeForest X ζ p.1.1).leaves ∧ p.2.2 ∈ (chainTreeForest X ζ p.2.1).leaves := by
  have he := chain_leafAddresses X ζ .leaf ((0 : Fin 1),[])
  constructor
  · apply (leafAddresses_one_root (X.plug ζ .leaf) p.1).mp
    rw [he]
    exact Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩)
  · apply (leafAddresses_one_root (X.plug ζ .leaf) p.2).mp
    rw [he]
    exact Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inr rfl⟩)

/-- Every actual leaf is a listed endpoint or the actual lone leaf. -/
theorem decodedTree_pairs_cover (X : RegChain) (ζ : ℤˣ) (ℓ : GLeaf (chainTreeForest X ζ)) :
    ℓ.1 ∈ pairEndpoints (X.pairsAt ζ ((0 : Fin 1),[])) ∨ ℓ = chainLoneLeaf X ζ := by
  have hm := (leafAddresses_one_root (X.plug ζ .leaf) ℓ.1).mpr ℓ.2
  rw [chain_leafAddresses,leafAddresses_leaf] at hm
  rcases Finset.mem_union.mp hm with hp | hp
  · exact Or.inl hp
  · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp hp))

/-- The exact pair-slot count plus one lone slot equals the actual leaf count. -/
theorem decodedTree_pair_card (X : RegChain) (ζ : ℤˣ) :
    (X.pairsAt ζ ((0 : Fin 1),[])).length*2+1 = Fintype.card (GLeaf (chainTreeForest X ζ)) := by
  rw [chain_pairsAt_length,Comb.card_gleaf]
  simp only [chainTreeForest,Fin.sum_univ_one,code_plug_order,TTree.order,Nat.add_zero]
  omega

/-- Literal internal endpoint signs agree with the given root sign. -/
theorem decodedTree_pair_signs (X : RegChain) (ζ : ℤˣ) :
    ∀ p ∈ X.pairsAt ζ ((0 : Fin 1),[]), nodeSign (fun _ : Fin 1 => ζ) p.1 = 1 ∧
      nodeSign (fun _ : Fin 1 => ζ) p.2 = -1 :=
  chain_pairsAt_signs X (fun _ : Fin 1 => ζ) ζ (0,[]) (by simp [nodeSign,pathSign])

/-- The actual paired tree with the specified code, actual pairing and unique lower mark. -/
noncomputable def decodedTree (X : RegChain) (ζ : ℤˣ) : Garden 1 :=
  gardenOfPairsAndLone (chainTreeForest X ζ) (fun _ => ζ) (X.pairsAt ζ (0,[]))
    (decodedTree_pairs_valid X ζ) (chainLoneLeaf X ζ) (decodedTree_pairs_cover X ζ)
    (decodedTree_pair_card X ζ) (decodedTree_pair_signs X ζ)

/-- The actual constructed tree has the requested root sign. -/
theorem decodedTree_sign (X : RegChain) (ζ : ℤˣ) : (decodedTree X ζ).sig 0 = ζ := rfl

/-- The actual constructed carrier satisfies the exact B2 tree decoder. -/
theorem decodedTree_decodes (X : RegChain) (ζ : ℤˣ) : X.DecodesTree (decodedTree X ζ) := by
  refine ⟨rfl,?_,?_⟩
  · intro ℓ
    have hm := gardenOfPairsAndLone_mark (chainTreeForest X ζ) (fun _ => ζ) (X.pairsAt ζ (0,[]))
      (decodedTree_pairs_valid X ζ) (chainLoneLeaf X ζ) (decodedTree_pairs_cover X ζ)
      (decodedTree_pair_card X ζ) (decodedTree_pair_signs X ζ) ℓ
    change (decodedTree X ζ).mark ℓ = _ at hm
    rw [hm]
    have he : ℓ = chainLoneLeaf X ζ ↔ ℓ.1.2 = X.lonePath := by
      constructor
      · intro h; exact congrArg (fun ℓ => ℓ.1.2) h
      · intro h; exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)
    by_cases hp : ℓ.1.2 = X.lonePath
    · exact (ite_eq_left (he.mpr hp)).trans (ite_eq_left hp).symm
    · exact (ite_eq_right (fun h => hp (he.mp h))).trans (ite_eq_right hp).symm
  · intro ℓ hn
    apply gardenOfPairsAndLone_pair_mem
    intro he
    exact hn (congrArg (fun ℓ => ℓ.1.2) he)

end WaveTurbulence.Reg
