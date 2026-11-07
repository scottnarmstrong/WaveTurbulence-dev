/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineChainConnected

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CurrentBlocks
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainInteriorPartition

/-! # Actual vine-chain ingredients partition its interior branches -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- One actual source vine with ordered joints. -/
structure ChainPiece (M : Molecule V D) where
  vineType : VineType
  atoms : Finset V
  upper : V
  lower : V
  vine : M.IsVine vineType atoms upper lower

noncomputable def ChainPiece.interior {M : Molecule V D} (P : ChainPiece M) : Finset V := P.atoms.erase P.upper

noncomputable def chainPieceUnion {M : Molecule V D} (L : List (ChainPiece M)) : Finset V := by
  classical
  exact L.toFinset.biUnion ChainPiece.interior

open Classical in
theorem mem_chainPieceUnion {M : Molecule V D} (L : List (ChainPiece M)) (v : V) :
    v ∈ chainPieceUnion L ↔ ∃ P ∈ L, v ∈ P.interior := by
  simp only [chainPieceUnion,Finset.mem_biUnion,List.mem_toFinset]

/-- This is a source-chain conclusion: no coverage or disjointness
certificate is assumed. The order is bottom-to-top, as in TARGET Step2. -/
theorem exists_chainInteriorPieces {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Vine.Chain M S a b n) :
    ∃ L : List (ChainPiece M), L.length = n ∧ chainPieceUnion L = S.erase a ∧
      L.Pairwise (fun P Q => Disjoint P.interior Q.interior) ∧
      (L.map (fun P => P.interior.card)).sum = (S.erase a).card := by
  classical
  induction h with
  | @single S a b hv =>
    obtain ⟨X,hX⟩ := hv
    let P : ChainPiece M := ⟨X,S,a,b,hX⟩
    refine ⟨[P],rfl,?_,by simp,?_⟩
    · simp only [chainPieceUnion,List.toFinset_cons,List.toFinset_nil,
        Finset.insert_empty]
      exact Finset.singleton_biUnion
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rfl
  | @append S T a b c n hS hT hi hne ih =>
    obtain ⟨X,hX⟩ := hT
    obtain ⟨L,hL,hU,hdis,hcard⟩ := ih
    have hmem := Vine.chain_joints_mem hS
    have hab : a ≠ b := by
      cases hS with
      | single hv => obtain ⟨Y,hY⟩ := hv; exact hY.1.2.2.2.1
      | append _ _ _ hne => exact hne
    let P : ChainPiece M := ⟨X,T,b,c,hX⟩
    have hpart := chainInterior_union S T a b hmem.1 hmem.2 hab hi
    have hd := chainInterior_disjoint S T a b hi
    refine ⟨P::L,by simp only [List.length_cons,hL],?_,?_,?_⟩
    · simp only [chainPieceUnion,List.toFinset_cons,Finset.biUnion_insert]
      change T.erase b ∪ chainPieceUnion L = _
      rw [hU,Finset.union_comm]
      exact hpart.symm
    · apply List.pairwise_cons.mpr
      refine ⟨?_,hdis⟩
      intro Q hQ
      change Disjoint (T.erase b) Q.interior
      apply Disjoint.mono_right ?_ hd.symm
      intro v hv
      rw [← hU]
      exact (mem_chainPieceUnion L v).mpr ⟨Q,hQ,hv⟩
    · simp only [List.map_cons,List.sum_cons]
      change (T.erase b).card+_ = _
      rw [hcard,chainInterior_card S T a b hmem.1 hmem.2 hab hi,Nat.add_comm]

end WaveTurbulence.VineEstS2
