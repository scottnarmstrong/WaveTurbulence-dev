/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Dec
public import WaveTurbulence.Foundations.RegStruct.DecodedLeaves
public import WaveTurbulence.Foundations.RegStruct.CodeOrders
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Trees

/-!
# Links partition the branching nodes (packet C2)

For a couple code `Q`, the endpoints of its links (B2 draft `RegCpl.linksAt`) are exactly the
branching nodes of the decoded trees (`couple_branchAddresses`), there are `n(𝒬)/2` links
(`couple_linksAt_length`), and every branching node lies in exactly one link
(`couple_links_flat_nodup`): TARGET Prop `deflink` ("a unique way to divide all the branching nodes
into two-element subsets"), DH21 Prop 4.3. The chosen set `𝒩^ch` has `n(𝒬)/2` elements.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg Finset

/-- The branching-node addresses of `t` placed at the global address `a`. -/
def branchAddresses {w : ℕ} (t : TTree) (a : Fin w × Path) : Finset (Fin w × Path) :=
  t.branching.image (addrExt a)

@[simp] theorem branchAddresses_leaf {w : ℕ} (a : Fin w × Path) :
    branchAddresses .leaf a = ∅ := by simp [branchAddresses, TTree.branching]

theorem branchAddresses_node {w : ℕ} (l m r : TTree) (a : Fin w × Path) :
    branchAddresses (.node l m r) a =
      insert a (branchAddresses l (addrExt a [0]) ∪ branchAddresses m (addrExt a [1]) ∪
        branchAddresses r (addrExt a [2])) := by
  simp only [branchAddresses, TTree.branching, Finset.image_insert, Finset.image_union, TTree.pre,
    Finset.image_image, Function.comp_def]
  have h0 : (fun p => addrExt a ((0 : Fin 3) :: p)) = addrExt (addrExt a [0]) :=
    funext (addrExt_cons a 0)
  have h1 : (fun p => addrExt a ((1 : Fin 3) :: p)) = addrExt (addrExt a [1]) :=
    funext (addrExt_cons a 1)
  have h2 : (fun p => addrExt a ((2 : Fin 3) :: p)) = addrExt (addrExt a [2]) :=
    funext (addrExt_cons a 2)
  have hr : addrExt a [] = a := by simp [addrExt]
  rw [h0, h1, h2, hr]

theorem pairEndpoints_cons {α : Type*} [DecidableEq α] (x y : α) (L : List (α × α)) :
    pairEndpoints ((x, y) :: L) = {x} ∪ ({y} ∪ pairEndpoints L) := by
  ext z; simp only [pairEndpoints, List.map_cons, List.toFinset_cons, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]; tauto

theorem branchAddresses_node' {w : ℕ} (l m r : TTree) (a : Fin w × Path) :
    branchAddresses (.node l m r) a =
      {a} ∪ (branchAddresses l (addrExt a [0]) ∪ branchAddresses m (addrExt a [1]) ∪
        branchAddresses r (addrExt a [2])) := by
  rw [branchAddresses_node, Finset.insert_eq]

mutual
/-- **The link endpoints of a decoded couple are its branching nodes.** -/
theorem couple_branchAddresses {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    branchAddresses Q.trees.1 a ∪ branchAddresses Q.trees.2 b = pairEndpoints (Q.linksAt a b) := by
  cases Q with
  | triv => simp [RegCpl.trees, RegCpl.linksAt]
  | type1 c r g d =>
    rw [RegCpl.linksAt, pairEndpoints_cons, pairEndpoints_append, pairEndpoints_append,
      ← couple_branchAddresses r, ← couple_branchAddresses g, ← couple_branchAddresses d]
    fin_cases c <;>
      simp only [RegCpl.trees, MiniCplCode.partner, branchAddresses_node', Fin.isValue,
        Fin.zero_eta, ↓reduceIte, Fin.mk_one, one_ne_zero] <;>
      (try simp only [show (2 : Fin 3) - 0 = 2 from rfl, show (2 : Fin 3) - 2 = 0 from rfl]) <;>
      ac_rfl
  | type2 p m q =>
    rw [RegCpl.trees, chain_branchAddresses p, chain_branchAddresses m, RegCpl.linksAt,
      pairEndpoints_append, pairEndpoints_append, ← couple_branchAddresses q]
    ac_rfl
termination_by structural Q

/-- A decoded chain's link endpoints are its branching nodes, outside the subtree at its lone
position. -/
theorem chain_branchAddresses {w : ℕ} (X : RegChain) (ζ : ℤˣ) (h : TTree) (a : Fin w × Path) :
    branchAddresses (X.plug ζ h) a =
      pairEndpoints (X.linksAt ζ a) ∪ branchAddresses h (addrExt a X.lonePath) := by
  cases X with
  | nil => simp [RegChain.plug, RegChain.linksAt, RegChain.lonePath, addrExt]
  | pair m r g i s =>
    have hr :=
      (couple_branchAddresses r
        (if slotSign ζ m.red.1 = 1 then addrExt a [m.red.1]
         else addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
        (if slotSign ζ m.red.1 = 1 then addrExt a ([m.c] ++ i.lonePath ++ [m.red.2])
         else addrExt a [m.red.1]))
    have hg :=
      (couple_branchAddresses g
        (if slotSign ζ m.green.1 = 1 then addrExt a [m.green.1]
         else addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
        (if slotSign ζ m.green.1 = 1 then addrExt a ([m.c] ++ i.lonePath ++ [m.green.2])
         else addrExt a [m.green.1]))
    obtain ⟨c,b⟩ := m
    rcases Int.units_eq_one_or ζ with hz | hz <;> subst ζ
    all_goals
      fin_cases c <;> fin_cases b
      all_goals
        simp [MiniTreeCode.red, MiniTreeCode.green, slotSign] at hr hg
        simp [RegChain.plug, RegChain.linksAt, RegChain.lonePath, node3, pairEndpoints_cons,
          MiniTreeCode.lone, MiniTreeCode.red, MiniTreeCode.green,
          slotSign, treeOfSign, branchAddresses_node', chain_branchAddresses i,
          chain_branchAddresses s, pairEndpoints_append, ← hr, ← hg, addrExt_append,
          List.append_assoc]
        ac_rfl
termination_by structural X
end

/-! ### Counting: `n(𝒬)/2` links, each branching node in exactly one link -/

mutual
/-- A couple code of order `n` has `n/2` links. -/
theorem couple_linksAt_length {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    (Q.linksAt a b).length * 2 = Q.size := by
  cases Q with
  | triv => rfl
  | type1 c r g d =>
    simp only [RegCpl.linksAt, List.length_cons, List.length_append, RegCpl.size]
    have := couple_linksAt_length r (addrExt a [0]) (addrExt b [c.partner 0])
    have := couple_linksAt_length g (addrExt b [1]) (addrExt a [1])
    have := couple_linksAt_length d (addrExt a [2]) (addrExt b [c.partner 2])
    omega
  | type2 p m q =>
    simp only [RegCpl.linksAt, List.length_append, RegCpl.size]
    have := chain_linksAt_length p 1 a
    have := chain_linksAt_length m (-1) b
    have := couple_linksAt_length q (addrExt a p.lonePath) (addrExt b m.lonePath)
    omega
termination_by structural Q

/-- A chain code of order `n` has `n/2` links. -/
theorem chain_linksAt_length {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (X.linksAt ζ a).length * 2 = X.size := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    have hr₁ := couple_linksAt_length r (addrExt a [m.red.1])
      (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
    have hr₂ := couple_linksAt_length r (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
      (addrExt a [m.red.1])
    have hg₁ := couple_linksAt_length g (addrExt a [m.green.1])
      (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
    have hg₂ := couple_linksAt_length g (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
      (addrExt a [m.green.1])
    have hi := chain_linksAt_length i (slotSign ζ m.c) (addrExt a [m.c])
    have hs := chain_linksAt_length s (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))
    by_cases hr : slotSign ζ m.red.1 = 1 <;> by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp only [RegChain.linksAt, hr, hg, ite_true, ite_false, List.length_cons,
        List.length_append, RegChain.size] <;> omega
termination_by structural X
end

/-- The flat list `[u₁, v₁, u₂, v₂, …]` of link endpoints. -/
def flatPairs {α : Type*} (L : List (α × α)) : List α := L.flatMap fun p => [p.1, p.2]

theorem flatPairs_length {α : Type*} (L : List (α × α)) : (flatPairs L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons p L ih => simp only [flatPairs, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢; rw [ih]; ring

theorem flatPairs_toFinset {α : Type*} [DecidableEq α] (L : List (α × α)) :
    (flatPairs L).toFinset = pairEndpoints L := by
  ext x
  simp only [flatPairs, List.mem_toFinset, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, pairEndpoints, Finset.mem_union, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨p, hp, Or.inl rfl⟩
    · exact ⟨p, hp, Or.inr rfl⟩

theorem card_branchAddresses {w : ℕ} (t : TTree) (a : Fin w × Path) :
    (branchAddresses t a).card = t.order := by
  rw [branchAddresses, Finset.card_image_of_injective _ (fun p q h => by
    simpa [addrExt] using h), Comb.card_branching]

theorem nodup_of_card {α : Type*} [DecidableEq α] {l : List α} (h : l.toFinset.card = l.length) :
    l.Nodup :=
  Multiset.toFinset_card_eq_card_iff_nodup (m := (l : Multiset α)) |>.mp h

/-- **Every branching node of a decoded couple lies in exactly one link**: the flat list of link
endpoints has no repetition (TARGET Prop `deflink`). -/
theorem couple_links_flat_nodup (Q : RegCpl) : (flatPairs Q.links).Nodup := by
  apply nodup_of_card
  rw [flatPairs_toFinset, flatPairs_length, RegCpl.links, ← couple_branchAddresses,
    Finset.card_union_of_disjoint, card_branchAddresses, card_branchAddresses, code_trees_order]
  · have := couple_linksAt_length Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))
    omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [branchAddresses, Finset.mem_image, addrExt] at hx hx'
    obtain ⟨p, -, rfl⟩ := hx
    obtain ⟨q, -, h⟩ := hx'
    simp at h

/-- The chosen set `𝒩^ch` (DH21 Def 4.11; B2 draft `chosenSet`) has `n(𝒬)/2` elements. -/
theorem card_chosenSet (Q : RegCpl) : (chosenSet Q.links).card * 2 = Q.size := by
  have hnd := couple_links_flat_nodup Q
  have hfst : (Q.links.map Prod.fst).Nodup := by
    refine List.Nodup.sublist ?_ hnd
    clear hnd
    induction Q.links with
    | nil => simp [flatPairs]
    | cons p L ih =>
      simp only [List.map_cons, flatPairs, List.flatMap_cons, List.cons_append] at ih ⊢
      exact (List.Sublist.cons₂ _ (List.Sublist.cons _ ih))
  rw [chosenSet, List.toFinset_card_of_nodup hfst, List.length_map, RegCpl.links,
    couple_linksAt_length]

end WaveTurbulence.Links
