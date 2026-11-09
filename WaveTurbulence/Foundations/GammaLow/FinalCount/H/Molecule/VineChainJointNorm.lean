/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineChainJointNorm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineChainJointNorm`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # A contained VC meeting an outer chain junction has the same gap norm -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc's junction test: if an inner VC contains a junction
of an outer chain split, conservation forces their actual gap norms to agree.
The inner ingredient at the junction is localized geometrically first. -/
theorem VC_at_chain_split_joint_norm (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b c x y : V} {n : ℕ}
    (hS : Src.Chain Src.γL M S a b n) (hT : Src.IsSomeVine Src.γL M T b c)
    (hi : S ∩ T={b}) (hU : M.IsBlock (S ∪ T) a c)
    (hA : Src.IsVC Src.γL M A x y) (hAU : A ⊆ S ∪ T) (hbA : b ∈ A)
    (k : D → Mom d) (hk : ∀ z,k (M.mate z)=k z)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ z ∈ M.dartsAt v,M.dartSign z • k z=0) :
    ‖groupFlow M A k x‖=‖groupFlow M (S ∪ T) k a‖ := by
  obtain ⟨hAB,m,hchain⟩ := hA
  obtain ⟨B,p,q,hI,hbB⟩ := chain_atom_ingredient hchain hbA
  obtain ⟨_hIB,hY,hBA⟩ := chainIngredient_spec hI
  have hBY := hBA.trans hAU
  have hflow := (chainIngredient_flow_eq M hM k hk hc hI hAB).1
  have hprefix := chain_prefix_isBlock M hM hS hT hi hU
  rcases vine_in_terminal_splitS M hM hT.block hU (chain_joints_mem hS).2 hY hBY with hBS | hBT
  · have hn := nested_block_at_joint_flow_norm M hM hY.block hprefix hBS hbB (Or.inr rfl) k hk hc
    have hfirst := nested_groupFlow_eq M (show S ⊆ S ∪ T from Finset.subset_union_left) a
      ((Mole.block_joint_degrees M hprefix).1.trans (Mole.block_joint_degrees M hU).1.symm) k
    calc
      ‖groupFlow M A k x‖ = ‖groupFlow M B k p‖ := congrArg norm hflow.symm
      _ = ‖groupFlow M S k b‖ := hn
      _ = ‖groupFlow M S k a‖ := by rw [block_jointFlow_neg M hM hprefix k hk hc,norm_neg]
      _ = ‖groupFlow M (S ∪ T) k a‖ := congrArg norm hfirst
  · have hn := nested_block_at_joint_flow_norm M hM hY.block hT.block hBT hbB (Or.inl rfl) k hk hc
    calc
      ‖groupFlow M A k x‖ = ‖groupFlow M B k p‖ := congrArg norm hflow.symm
      _ = ‖groupFlow M T k b‖ := hn
      _ = ‖groupFlow M (S ∪ T) k a‖ := congrArg norm
        (terminal_block_initialFlow M hM hT.block hU Finset.subset_union_right k hk hc)

end WaveTurbulence.GammaLow.FinalCount.H
