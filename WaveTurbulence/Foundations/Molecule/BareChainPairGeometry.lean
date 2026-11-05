/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SourceChainHistory
public import WaveTurbulence.Foundations.Molecule.ChainCount

/-! # Actual non-sibling side pairings and source chain structure data -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The two physical side slots belong to different branching levels, independently of orientation. -/
theorem trivial_side_pair_depth_ne (k : MiniTreeCode) (i : RegChain) (ε : ℤˣ) (a : Fin 2 × Path)
    (j l : Fin 3) (p : (Fin 2 × Path) × (Fin 2 × Path))
    (hp : p ∈ sidePairs .triv ε (addrExt a [j]) (backRoot a k i l)) : p.1.2.length ≠ p.2.2.length := by
  by_cases he : ε = 1
  · simp only [sidePairs,he,ite_true,RegCpl.pairsAt,List.mem_singleton] at hp
    subst p
    simp only [backRoot,addrExt,List.length_append,List.length_singleton]
    omega
  · simp only [sidePairs,he,ite_false,RegCpl.pairsAt,List.mem_singleton] at hp
    subst p
    simp only [backRoot,addrExt,List.length_append,List.length_singleton]
    omega

/-- Every actual pair in a bare chain joins different branching-node levels. -/
theorem bareChain_pair_depth_ne (X : RegChain) (hX : BareChain X) (ζ : ℤˣ) (a : Fin 2 × Path)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ X.pairsAt ζ a) : p.1.2.length ≠ p.2.2.length := by
  cases X with
  | nil => simp [RegChain.pairsAt] at hp
  | pair k r g i s =>
    obtain ⟨rfl,rfl,hi,hs⟩ := hX
    rw [chain_pairsAt_blocks] at hp
    simp only [List.mem_append] at hp
    rcases hp with ((hr | hg) | hinner) | hrest
    · exact trivial_side_pair_depth_ne k i _ a _ _ p hr
    · exact trivial_side_pair_depth_ne k i _ a _ _ p hg
    · exact bareChain_pair_depth_ne i hi _ _ p hinner
    · exact bareChain_pair_depth_ne s hs _ _ p hrest
termination_by structural X

/-- TARGET's no-siblings condition for every actual internal pair of a bare chain. -/
theorem bareChain_no_sibling_pair (X : RegChain) (hX : BareChain X) (ζ : ℤˣ) (a : Fin 2 × Path)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ X.pairsAt ζ a)
    (q : Path) (j l : Fin 3) : ¬ (p.1.2 = q ++ [j] ∧ p.2.2 = q ++ [l]) := by
  rintro ⟨h0,h1⟩
  apply bareChain_pair_depth_ne X hX ζ a p hp
  rw [h0,h1,List.length_append,List.length_append,List.length_singleton,List.length_singleton]

/-- DH21 Proposition 4.7 for an actual B-only chain history: a saturated ordered
spine, its exact legal partition, and one of six source mini-tree codes per pair. -/
theorem RawChainHistory.exists_structure {ζ : ℤˣ} {R : RawCpl} {lp : Path} (h : RawChainHistory ζ R lp) :
    ∃ X : RegChain, BareChain X ∧ X.lonePath = lp ∧ RawRep (treeAuxCode X ζ) R ∧
      (chainPartition X).Legal ∧ X.lonePath.length = 2*(chainShape X).numNodes ∧
      (chainLabels X).length = (chainShape X).numNodes := by
  obtain ⟨X,hX,hLp,hrep⟩ := h.exists_bare_rep
  exact ⟨X,hX,hLp,hrep,chainPartition_legal X,chain_lonePath_length X,chainLabels_length X⟩

end WaveTurbulence.Reg
