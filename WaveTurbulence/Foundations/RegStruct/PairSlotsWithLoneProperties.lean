/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PairSlotsWithLone

/-! # Exact marks and literal pairs of the one-lone-leaf carrier -/

public section
namespace WaveTurbulence.Reg
open TTree
variable {w : ℕ} (tree : Fin w → TTree) (σ : Fin w → ℤˣ)
  (P : List ((Fin w × Path) × (Fin w × Path)))
  (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
  (L : GLeaf tree) (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P ∨ ℓ = L)
  (hn : P.length*2+1 = Fintype.card (GLeaf tree))
  (hs : ∀ p ∈ P, nodeSign σ p.1 = 1 ∧ nodeSign σ p.2 = -1)

/-- The unique marked leaf is exactly the supplied actual lone leaf. -/
theorem gardenOfPairsAndLone_mark (ℓ : GLeaf tree) :
    (gardenOfPairsAndLone tree σ P hv L hc hn hs).mark ℓ =
      if ℓ = L then some MarkTag.lower else none := by
  let E := endpointWithLoneEquiv tree P hv L hc hn
  change (pairSlotsWithLone P.length (nodeSign σ L.1)).mark (E.symm ℓ) = _
  have hL : E.symm L = Sum.inr () := by
    have he : E (Sum.inr ()) = L := rfl
    rw [← he]
    exact E.symm_apply_apply _
  generalize hx : E.symm ℓ = x
  cases x with
  | inl x =>
    have hne : ℓ ≠ L := by
      intro he
      have hh := congrArg E.symm he
      rw [hx,hL] at hh
      cases hh
    rw [ite_eq_right hne]
    rfl
  | inr u =>
    cases u
    have he := E.apply_symm_apply ℓ
    rw [hx] at he
    change L = ℓ at he
    rw [← he,ite_eq_left rfl]
    rfl

/-- Every nonlone leaf has precisely its listed source partner. -/
theorem gardenOfPairsAndLone_pair_mem (ℓ : GLeaf tree) (hne : ℓ ≠ L) :
    (ℓ.1,((gardenOfPairsAndLone tree σ P hv L hc hn hs).pair ℓ).1) ∈ symmPairs P := by
  let E := endpointWithLoneEquiv tree P hv L hc hn
  change (ℓ.1,(E ((pairSlotsWithLone P.length (nodeSign σ L.1)).pair (E.symm ℓ))).1) ∈ symmPairs P
  generalize hx : E.symm ℓ = x
  have he : ℓ = E x := by rw [← hx]; exact (E.apply_symm_apply ℓ).symm
  cases x with
  | inl x =>
    rw [he]
    change ((endpointLeaf tree P hv x).1,
      (endpointLeaf tree P hv ((pairSlots P.length).pair x)).1) ∈ symmPairs P
    obtain ⟨i,j⟩ := x
    fin_cases j
    · apply (mem_symmPairs_iff P _).mpr
      left
      change (P[i.val].1,P[i.val].2) ∈ P
      simpa only [Prod.eta] using List.getElem_mem (l := P) i.isLt
    · apply (mem_symmPairs_iff P _).mpr
      right
      change (P[i.val].1,P[i.val].2) ∈ P
      simpa only [Prod.eta] using List.getElem_mem (l := P) i.isLt
  | inr u =>
    change ℓ = L at he
    exact (hne he).elim

end WaveTurbulence.Reg
