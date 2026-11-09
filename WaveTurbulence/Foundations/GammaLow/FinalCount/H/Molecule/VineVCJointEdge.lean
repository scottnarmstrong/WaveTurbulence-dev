/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineVCJointEdge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Base
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineVCJointEdge`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # A direct bond between VC joints forces one actual vine ingredient 

**Low-range change (L6-HDS).** main's `VC_joint_pair_degree_one_isVineV` (the VC is a vine (V)) becomes
`VC_joint_pair_degree_one_isTVine` (a T-vine; `H/DS/DV.lean`). `VC_with_joint_adj_isSomeVine` is main's, ported.
-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A direct endpoint bond in a VC excludes a nontrivial chain split:
the terminal joint has already used its whole degree within the last vine. -/
theorem VC_with_joint_adj_isSomeVine (M : Molecule V D) {U : Finset V} {a b : V}
    (hU : Src.IsVC Src.γL M U a b) (hab : M.Adj a b) : Src.IsSomeVine Src.γL M U a b := by
  obtain ⟨hB,n,hchain⟩ := hU
  cases hchain with
  | single h => exact h
  | @append S T a b c n hS hT hi _hne =>
    have hX := hT
    have haT := nested_block_joint_adj_mem M hX.block hB subset_union_right hX.block.2.2.1
      (Or.inr rfl) hB.2.1 (Mole.adj_symmetric M hab)
    have haS := (chain_joints_mem hS).1
    have hmem : a ∈ S ∩ T := mem_inter.mpr ⟨haS,haT⟩
    rw [hi] at hmem
    exact False.elim (chain_joints_ne hS (mem_singleton.mp hmem))

/-- The only VC of the low family whose joint-pair induced degree is one is a T-vine: it is a single vine (it has a joint
bond), `degIn {a, b} a = 2·mult(a, a) + σ(a, b)` gives `σ = 1`, and a member with `σ = 1` is a T-vine. -/
theorem VC_joint_pair_degree_one_isTVine (M : Molecule V D) {U : Finset V} {a b : V}
    (hU : Src.IsVC Src.γL M U a b) (hd : M.degIn {a,b} a=1) : M.IsTVine U a b := by
  have hX := VC_with_joint_adj_isSomeVine M hU (pair_degree_one_adj M hd)
  have hσ : M.sigma a b = 1 := by
    have := DS.degIn_pair (M := M) hU.1.2.2.2.1
    omega
  exact DS.isTVine_of_sigma_one hX hσ

end WaveTurbulence.GammaLow.FinalCount.H
