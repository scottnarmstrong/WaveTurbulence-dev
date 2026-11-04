/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PairSlots

/-! # Actual finite pairings with exactly one marked lower leaf -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Complete paired endpoint slots and one actual lower/lone slot. -/
def pairSlotsWithLone (n : ℕ) (ζ : ℤˣ) : Comb.SignedPairing ((Fin n × Fin 2) ⊕ Unit) where
  sign := Sum.elim (pairSlots n).sign (fun _ => ζ)
  pair := Sum.map (pairSlots n).pair id
  mark := Sum.elim (fun _ => none) (fun _ => some MarkTag.lower)
  pair_pair x := by cases x with | inl x => simp [(pairSlots n).pair_pair] | inr u => rfl
  pair_eq_iff x := by
    cases x with
    | inl x => obtain ⟨i,j⟩ := x; fin_cases j <;> simp [pairSlots]
    | inr u => simp
  pair_sign x hn := by
    cases x with
    | inl x =>
      change (pairSlots n).sign ((pairSlots n).pair x) = -(pairSlots n).sign x
      exact (pairSlots n).pair_sign x (by obtain ⟨i,j⟩ := x; fin_cases j <;> simp [pairSlots])
    | inr u => exact (hn rfl).elim

/-- Map the extra slot to the actual distinguished leaf. -/
def endpointWithLone {w : ℕ} (tree : Fin w → TTree)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (L : GLeaf tree) : ((Fin P.length × Fin 2) ⊕ Unit) → GLeaf tree :=
  Sum.elim (endpointLeaf tree P hv) (fun _ => L)

/-- Exact coverage of pairs and the lone leaf gives the actual endpoint bijection. -/
noncomputable def endpointWithLoneEquiv {w : ℕ} (tree : Fin w → TTree)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (L : GLeaf tree) (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P ∨ ℓ = L)
    (hn : P.length*2+1 = Fintype.card (GLeaf tree)) :
    ((Fin P.length × Fin 2) ⊕ Unit) ≃ GLeaf tree :=
  Equiv.ofBijective (endpointWithLone tree P hv L)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨by
      intro ℓ
      rcases hc ℓ with hp | rfl
      · obtain ⟨p,hp,hx | hx⟩ := (mem_pairEndpoints_iff P ℓ.1).mp hp
        · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
          refine ⟨.inl (⟨i,hi⟩,0),Subtype.ext ?_⟩
          change P[i].1 = ℓ.1
          rw [he]
          exact hx.symm
        · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
          refine ⟨.inl (⟨i,hi⟩,1),Subtype.ext ?_⟩
          change P[i].2 = ℓ.1
          rw [he]
          exact hx.symm
      · exact ⟨.inr (),rfl⟩,
      by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit] using hn⟩)

/-- Construct the actual garden, preserving the literal pair slots and the lone slot. -/
noncomputable def gardenOfPairsAndLone {w : ℕ} (tree : Fin w → TTree) (σ : Fin w → ℤˣ)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (L : GLeaf tree) (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P ∨ ℓ = L)
    (hn : P.length*2+1 = Fintype.card (GLeaf tree))
    (hs : ∀ p ∈ P, nodeSign σ p.1 = 1 ∧ nodeSign σ p.2 = -1) : Garden w :=
  Comb.gardenFromLeafEquiv tree σ (pairSlotsWithLone P.length (nodeSign σ L.1))
    (endpointWithLoneEquiv tree P hv L hc hn).symm (fun ℓ => by
      let E := endpointWithLoneEquiv tree P hv L hc hn
      have he := E.apply_symm_apply ℓ
      generalize hx : E.symm ℓ = x
      cases x with
      | inl x =>
        have hm := endpointLeaf_sign tree σ P hv hs x
        rw [hx] at he
        change endpointLeaf tree P hv x = ℓ at he
        change nodeSign σ ℓ.1 = (pairSlots P.length).sign x
        rw [← he]
        exact hm
      | inr u =>
        rw [hx] at he
        change L = ℓ at he
        change nodeSign σ ℓ.1 = nodeSign σ L.1
        rw [he])

end WaveTurbulence.Reg
