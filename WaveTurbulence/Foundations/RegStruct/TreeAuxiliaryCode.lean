/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.TreeMatchingCarrier

/-! # The actual auxiliary couple code of a paired-tree code -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Adjoin the source's auxiliary trivial tree, preserving the root sign. -/
def treeAuxCode (X : RegChain) (ζ : ℤˣ) : RegCpl :=
  if ζ = 1 then joinChains X .nil .triv else joinChains .nil X .triv

/-- Actual well-formed chain data give actual well-formed auxiliary couple data. -/
theorem treeAuxCode_wf (X : RegChain) (ζ : ℤˣ) (hw : X.wf = true) : (treeAuxCode X ζ).wf = true := by
  by_cases hζ : ζ = 1
  · rw [treeAuxCode,ite_eq_left hζ]
    exact joinChains_wf X .nil .triv hw rfl rfl rfl
  · rw [treeAuxCode,ite_eq_right hζ]
    exact joinChains_wf .nil X .triv rfl hw rfl rfl

/-- The auxiliary code retains every piece of the chain data. -/
theorem treeAuxCode_injective (ζ : ℤˣ) : Function.Injective (fun X => treeAuxCode X ζ) := by
  intro X Y he
  by_cases hζ : ζ = 1 <;> cases X <;> cases Y <;>
    simp_all [treeAuxCode,joinChains,RegChain.isNil]

/-- Put the one-tree leaf addresses in the chosen side of the auxiliary couple. -/
def liftTreeAddress (s : Fin 2) (z : Fin 1 × Path) : Fin 2 × Path := (s,z.2)

/-- This literal lift respects every path extension. -/
theorem liftTreeAddress_respects (s : Fin 2) (z : Fin 1 × Path) (p : Path) :
    liftTreeAddress s (addrExt z p) = addrExt (liftTreeAddress s z) p := rfl

/-- Actual unordered chain pairs lift literally to either side of the auxiliary couple. -/
theorem chain_pairs_lift (X : RegChain) (ζ : ℤˣ) (s : Fin 2)
    (p : (Fin 1 × Path) × (Fin 1 × Path)) (hp : p ∈ symmPairs (X.pairsAt ζ (0,[]))) :
    (liftTreeAddress s p.1,liftTreeAddress s p.2) ∈ symmPairs (X.pairsAt ζ (s,[])) := by
  have hm := chain_pairsAt_map X (liftTreeAddress s) (liftTreeAddress_respects s) ζ (0,[])
  change X.pairsAt ζ (s,[]) = _ at hm
  rw [mem_symmPairs_iff] at hp ⊢
  rw [hm]
  rcases hp with hp | hp
  · exact Or.inl (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact Or.inr (List.mem_map.mpr ⟨p.swap,hp,rfl⟩)

/-- In the positive orientation all internal chain pairs are included unchanged. -/
theorem treeAuxCode_positive_pair_inclusion (X : RegChain) (p)
    (hp : p ∈ X.pairsAt 1 ((0 : Fin 2),[])) : p ∈ (treeAuxCode X 1).raw.2 := by
  rw [treeAuxCode,ite_eq_left rfl]
  exact (mem_joinChains_pairsAt X .nil .triv (0,[]) (1,[]) p).mpr (Or.inl hp)

/-- In the negative orientation all internal chain pairs are included unchanged. -/
theorem treeAuxCode_negative_pair_inclusion (X : RegChain) (p)
    (hp : p ∈ X.pairsAt (-1) ((1 : Fin 2),[])) : p ∈ (treeAuxCode X (-1)).raw.2 := by
  rw [treeAuxCode,ite_eq_right (by decide)]
  exact (mem_joinChains_pairsAt .nil X .triv (0,[]) (1,[]) p).mpr (Or.inr (Or.inl hp))

/-- The positive lone leaf is paired with the auxiliary root. -/
theorem treeAuxCode_positive_terminal_pair (X : RegChain) :
    (((0 : Fin 2),X.lonePath),(1,[])) ∈ (treeAuxCode X 1).raw.2 := by
  rw [treeAuxCode,ite_eq_left rfl]
  apply (mem_joinChains_pairsAt X .nil .triv (0,[]) (1,[]) _).mpr
  exact Or.inr (Or.inr (by simp [RegCpl.pairsAt,RegChain.lonePath,addrExt]))

/-- The negative lone leaf is paired with the auxiliary root with positive endpoint first. -/
theorem treeAuxCode_negative_terminal_pair (X : RegChain) :
    (((0 : Fin 2),[]),(1,X.lonePath)) ∈ (treeAuxCode X (-1)).raw.2 := by
  rw [treeAuxCode,ite_eq_right (by decide)]
  apply (mem_joinChains_pairsAt .nil X .triv (0,[]) (1,[]) _).mpr
  exact Or.inr (Or.inr (by simp [RegCpl.pairsAt,RegChain.lonePath,addrExt]))

end WaveTurbulence.Reg
