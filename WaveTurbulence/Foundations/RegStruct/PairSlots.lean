/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.SignedPairing
public import WaveTurbulence.Foundations.RegStruct.PairRelations
public import WaveTurbulence.Foundations.RegStruct.LeafAddresses

/-! # Perfect matching from a complete finite pair list

The endpoint count turns coverage into bijectivity. Literal endpoint addresses
are retained, so the resulting garden carries the given source pair relation.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Abstract positive and negative endpoints of n pair slots. -/
def pairSlots (n : ℕ) : Comb.SignedPairing (Fin n × Fin 2) where
  sign x := if x.2 = 0 then 1 else -1
  pair x := (x.1,1-x.2)
  mark _ := none
  pair_pair x := by rcases x with ⟨i,j⟩; fin_cases j <;> rfl
  pair_eq_iff x := by rcases x with ⟨i,j⟩; fin_cases j <;> simp
  pair_sign x _ := by rcases x with ⟨i,j⟩; fin_cases j <;> rfl

/-- The actual endpoint leaf corresponding to one finite pair slot. -/
def endpointLeaf {w : ℕ} (tree : Fin w → TTree)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (x : Fin P.length × Fin 2) : GLeaf tree :=
  if x.2 = 0 then ⟨P[x.1.val].1, (hv _ (List.getElem_mem _)).1⟩
  else ⟨P[x.1.val].2, (hv _ (List.getElem_mem _)).2⟩

/-- Coverage of all leaves gives a surjection from the pair slots. -/
theorem endpointLeaf_surjective {w : ℕ} (tree : Fin w → TTree)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P) : Function.Surjective (endpointLeaf tree P hv) := by
  intro ℓ
  obtain ⟨p,hp,hx | hx⟩ := (mem_pairEndpoints_iff P ℓ.1).mp (hc ℓ)
  · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    refine ⟨(⟨i,hi⟩,0), Subtype.ext ?_⟩
    change P[i].1 = ℓ.1
    rw [he]
    exact hx.symm
  · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    refine ⟨(⟨i,hi⟩,1), Subtype.ext ?_⟩
    change P[i].2 = ℓ.1
    rw [he]
    exact hx.symm

/-- Coverage with the exact endpoint count leaves no duplicates and no ambiguous partners. -/
noncomputable def endpointEquiv {w : ℕ} (tree : Fin w → TTree)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P)
    (hn : P.length * 2 = Fintype.card (GLeaf tree)) :
    (Fin P.length × Fin 2) ≃ GLeaf tree :=
  Equiv.ofBijective (endpointLeaf tree P hv)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨endpointLeaf_surjective tree P hv hc, by simpa only [Fintype.card_prod,Fintype.card_fin] using hn⟩)

/-- Slot signs agree with the actual endpoint signs of a source-oriented list. -/
theorem endpointLeaf_sign {w : ℕ} (tree : Fin w → TTree) (σ : Fin w → ℤˣ)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (hs : ∀ p ∈ P, nodeSign σ p.1 = 1 ∧ nodeSign σ p.2 = -1)
    (x : Fin P.length × Fin 2) :
    nodeSign σ (endpointLeaf tree P hv x).1 = (pairSlots P.length).sign x := by
  obtain ⟨i,j⟩ := x
  have hi := hs P[i.val] (List.getElem_mem _)
  fin_cases j
  · exact hi.1
  · exact hi.2

/-- Construct the actual garden from a complete, correctly oriented finite pair list. -/
noncomputable def gardenOfPairs {w : ℕ} (tree : Fin w → TTree) (σ : Fin w → ℤˣ)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P)
    (hn : P.length * 2 = Fintype.card (GLeaf tree))
    (hs : ∀ p ∈ P, nodeSign σ p.1 = 1 ∧ nodeSign σ p.2 = -1) : Garden w :=
  Comb.gardenFromLeafEquiv tree σ (pairSlots P.length) (endpointEquiv tree P hv hc hn).symm
    (fun ℓ => by
      have h := endpointLeaf_sign tree σ P hv hs ((endpointEquiv tree P hv hc hn).symm ℓ)
      change nodeSign σ ((endpointEquiv tree P hv hc hn)
        ((endpointEquiv tree P hv hc hn).symm ℓ)).1 = _ at h
      simpa only [Equiv.apply_symm_apply] using h)

/-- The garden built from a complete pair list has no marked leaves. -/
theorem gardenOfPairs_plain {w : ℕ} (tree : Fin w → TTree) (σ : Fin w → ℤˣ)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P)
    (hn : P.length * 2 = Fintype.card (GLeaf tree))
    (hs : ∀ p ∈ P, nodeSign σ p.1 = 1 ∧ nodeSign σ p.2 = -1) :
    (gardenOfPairs tree σ P hv hc hn hs).IsPlain := fun _ => rfl

/-- The constructed garden retains the original listed partner of every leaf. -/
theorem gardenOfPairs_pair_mem {w : ℕ} (tree : Fin w → TTree) (σ : Fin w → ℤˣ)
    (P : List ((Fin w × Path) × (Fin w × Path)))
    (hv : ∀ p ∈ P, p.1.2 ∈ (tree p.1.1).leaves ∧ p.2.2 ∈ (tree p.2.1).leaves)
    (hc : ∀ ℓ : GLeaf tree, ℓ.1 ∈ pairEndpoints P)
    (hn : P.length * 2 = Fintype.card (GLeaf tree))
    (hs : ∀ p ∈ P, nodeSign σ p.1 = 1 ∧ nodeSign σ p.2 = -1)
    (ℓ : GLeaf tree) :
    (ℓ.1, ((gardenOfPairs tree σ P hv hc hn hs).pair ℓ).1) ∈ symmPairs P := by
  let E := endpointEquiv tree P hv hc hn
  let x := E.symm ℓ
  have he : ℓ = E x := (E.apply_symm_apply ℓ).symm
  change (ℓ.1,(E ((pairSlots P.length).pair x)).1) ∈ symmPairs P
  rw [he]
  change ((endpointLeaf tree P hv x).1,
    (endpointLeaf tree P hv ((pairSlots P.length).pair x)).1) ∈ symmPairs P
  obtain ⟨i,j⟩ := x
  fin_cases j
  · apply (mem_symmPairs_iff P _).mpr
    left
    change (P[i.val].1,P[i.val].2) ∈ P
    simpa only [Prod.eta] using (List.getElem_mem (l := P) i.isLt)
  · apply (mem_symmPairs_iff P _).mpr
    right
    change (P[i.val].1,P[i.val].2) ∈ P
    simpa only [Prod.eta] using (List.getElem_mem (l := P) i.isLt)

end WaveTurbulence.Reg
