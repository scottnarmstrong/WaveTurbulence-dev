/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPieces
public import Mathlib.Data.List.Pairwise

/-! # Source-chain interior coding without multiplicities -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D}

noncomputable def chainPieceNode (L : List (ChainPiece M))
    (x : Σ i : Fin L.length, ↥((L.get i).interior)) : ↥(chainPieceUnion L) :=
  ⟨x.2.1,(mem_chainPieceUnion L x.2.1).mpr ⟨L.get x.1,List.get_mem L x.1,x.2.2⟩⟩

theorem chainPieceNode_injective (L : List (ChainPiece M))
    (hL : L.Pairwise (fun P Q => Disjoint P.interior Q.interior)) :
    Function.Injective (chainPieceNode L) := by
  rintro ⟨i,v⟩ ⟨j,w⟩ he
  have hvw : v.1 = w.1 := congrArg (fun q : ↥(chainPieceUnion L) => q.1) he
  by_cases hij : i = j
  · subst j
    have hv : v = w := Subtype.ext hvw
    subst w
    rfl
  · have hd : Disjoint (L.get i).interior (L.get j).interior := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hL.rel_get_of_lt h
      · exact (hL.rel_get_of_lt h).symm
    exact (Finset.disjoint_left.mp hd v.2 (hvw.symm ▸ w.2)).elim

theorem chainPieceNode_surjective (L : List (ChainPiece M)) : Function.Surjective (chainPieceNode L) := by
  intro v
  obtain ⟨P,hP,hv⟩ := (mem_chainPieceUnion L v.1).mp v.2
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hP
  subst P
  exact ⟨⟨i,⟨v.1,hv⟩⟩,Subtype.ext rfl⟩

/-- The bijection uses the actual source atom name as its map. -/
noncomputable def chainPieceNodeEquiv (L : List (ChainPiece M))
    (hL : L.Pairwise (fun P Q => Disjoint P.interior Q.interior)) :
    (Σ i : Fin L.length, ↥((L.get i).interior)) ≃ ↥(chainPieceUnion L) :=
  Equiv.ofBijective (chainPieceNode L) ⟨chainPieceNode_injective L hL,chainPieceNode_surjective L⟩

end WaveTurbulence.VineEstS2
