/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueTree
public import WaveTurbulence.Foundations.IncohInst.Links.Bridge
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks

/-!
# Decorations along a split chain (code level)

LINKS reads decorations of decoded carriers along the structure code (`CplDec`, `ChainDec`; bridges
`cplDec_of_decoration`, `isDecoration_of_cplDec`, `chainDec_of_decoration`). For the layer splitting of
TARGET L1236–L1246:

* `cplDec_comp`, `chainDec_comp`: relabelling the addresses by a map commuting with `addrExt`;
* `chainDec_append`: a decoration of an appended chain is a decoration of each piece;
* `chainDec_congr`: a chain decoration only reads the values at the nodes of the placed chain;
* `isDecoration_of_chainDec`: the converse bridge for decoded paired trees.
-/

@[expose] public section

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V]

theorem append_child_mem_nodes : ∀ (t : TTree) (p : Path), p ∈ t.branching → ∀ i : Fin 3,
    p ++ [i] ∈ t.nodes := by
  intro t
  induction t with
  | leaf => exact fun p hp => by simp [TTree.branching] at hp
  | node l m r ihl ihm ihr =>
    intro p hp i
    rcases p with _ | ⟨j, p⟩
    · simp only [List.nil_append]
      rw [cons_mem_nodes_node]
      fin_cases i <;> exact TTree.nil_mem_nodes _
    · rw [cons_mem_branching_node] at hp
      simp only [List.cons_append]
      rw [cons_mem_nodes_node]
      fin_cases j
      · exact ihl p hp i
      · exact ihm p hp i
      · exact ihr p hp i

/-- An address map commuting with extension of addresses. -/
def AddrHom {v w : ℕ} (φ : Fin v × Path → Fin w × Path) : Prop :=
  ∀ x q, φ (addrExt x q) = addrExt (φ x) q

theorem nodeRel_comp {v w : ℕ} {φ : Fin v × Path → Fin w × Path} (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (f : Fin w × Path → V) (x : Fin v × Path) : NodeRel (f ∘ φ) x ↔ NodeRel f (φ x) := by
  unfold NodeRel
  simp only [Function.comp, hφ]

mutual
theorem cplDec_comp {v w : ℕ} {φ : Fin v × Path → Fin w × Path} (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (f : Fin w × Path → V) : (Q : RegCpl) → (a b : Fin v × Path) →
    (CplDec (f ∘ φ) Q a b ↔ CplDec f Q (φ a) (φ b))
  | .triv, a, b => Iff.rfl
  | .type1 c Q₁ Q₂ Q₃, a, b => by
    simp only [CplDec, nodeRel_comp hφ, cplDec_comp hφ f Q₁, cplDec_comp hφ f Q₂,
      cplDec_comp hφ f Q₃, hφ]
  | .type2 Xp Xm Qlp, a, b => by
    simp only [CplDec, chainDec_comp hφ f Xp, chainDec_comp hφ f Xm, cplDec_comp hφ f Qlp, hφ]
termination_by structural Q => Q

theorem chainDec_comp {v w : ℕ} {φ : Fin v × Path → Fin w × Path} (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (f : Fin w × Path → V) : (X : RegChain) → (ζ : ℤˣ) → (a : Fin v × Path) →
    (ChainDec (f ∘ φ) X ζ a ↔ ChainDec f X ζ (φ a))
  | .nil, _, _ => Iff.rfl
  | .pair m Qr Qg inner rest, ζ, a => by
    simp only [ChainDec, nodeRel_comp hφ, cplDec_comp hφ f Qr, cplDec_comp hφ f Qg,
      chainDec_comp hφ f inner, chainDec_comp hφ f rest, hφ]
termination_by structural X => X
end

/-- **A decoration of an appended chain decorates both pieces.** -/
theorem chainDec_append {w : ℕ} (f : Fin w × Path → V) (X Y : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) :
    ChainDec f (appendChain X Y) ζ a ↔ ChainDec f X ζ a ∧ ChainDec f Y ζ (addrExt a X.lonePath) := by
  cases X with
  | nil =>
    have : addrExt a ([] : Path) = a := by simp [addrExt]
    simp [appendChain, ChainDec, RegChain.lonePath, this]
  | pair m r g i s =>
    simp only [appendChain, ChainDec, chainDec_append f s Y, slotSign_lone, RegChain.lonePath,
      addrExt_append, List.append_assoc]
    tauto
termination_by structural X

/-- **A chain decoration reads only the nodes of the placed chain.** -/
theorem chainDec_congr {w : ℕ} {f g : Fin w × Path → V} (X : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path)
    (h : ∀ q ∈ (X.plug ζ .leaf).nodes, f (addrExt a q) = g (addrExt a q)) :
    ChainDec f X ζ a ↔ ChainDec g X ζ a := by
  have hB : pairEndpoints (X.linksAt ζ a) = branchAddresses (X.plug ζ .leaf) a := by
    have := chain_branchAddresses X ζ .leaf a
    rw [this, branchAddresses_leaf, Finset.union_empty]
  have hL : ∀ x ∈ pairEndpoints (X.pairsAt ζ a), x ∈ leafAddresses (X.plug ζ .leaf) a := by
    intro x hx
    rw [chain_leafAddresses]
    exact Finset.mem_union_left _ hx
  have hnode : ∀ x ∈ pairEndpoints (X.linksAt ζ a), NodeRel f x ↔ NodeRel g x := by
    intro x hx
    rw [hB] at hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hqn : q ∈ (X.plug ζ .leaf).nodes := TTree.branching_subset_nodes _ hq
    unfold NodeRel
    rw [h q hqn, addrExt_append, addrExt_append, addrExt_append,
      h _ (append_child_mem_nodes _ q hq 0), h _ (append_child_mem_nodes _ q hq 1),
      h _ (append_child_mem_nodes _ q hq 2)]
  have hpair : ∀ x ∈ pairEndpoints (X.pairsAt ζ a), f x = g x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (hL x hx)
    exact h q (TTree.leaves_subset_nodes _ hq)
  constructor
  · intro hf
    refine chainDec_of_lists _ X ζ a (fun x hx => (hnode x hx).mp (chainDec_nodeRel f X ζ a hf x hx))
      fun p hp => ?_
    have e1 := hpair p.1 ((mem_pairEndpoints_iff _ _).2 ⟨p, hp, Or.inl rfl⟩)
    have e2 := hpair p.2 ((mem_pairEndpoints_iff _ _).2 ⟨p, hp, Or.inr rfl⟩)
    rw [← e1, ← e2]
    exact chainDec_pairs f X ζ a hf p hp
  · intro hg
    refine chainDec_of_lists _ X ζ a (fun x hx => (hnode x hx).mpr (chainDec_nodeRel g X ζ a hg x hx))
      fun p hp => ?_
    have e1 := hpair p.1 ((mem_pairEndpoints_iff _ _).2 ⟨p, hp, Or.inl rfl⟩)
    have e2 := hpair p.2 ((mem_pairEndpoints_iff _ _).2 ⟨p, hp, Or.inr rfl⟩)
    rw [e1, e2]
    exact chainDec_pairs g X ζ a hg p hp

/-- **Conversely, a chain decoration restricts to a decoration of a decoded paired tree.** -/
theorem isDecoration_of_chainDec {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {f : Fin 1 × Path → V} (h : ChainDec f X (G.sig 0) (0, [])) :
    IsDecoration G (fun a : GNode G.tree => f a.1) := by
  constructor
  · intro b
    have hx : b.1 ∈ pairEndpoints (X.treeLinks (G.sig 0)) :=
      (tree_mem_pairEndpoints_links_iff hX b.1).2 b.2
    exact chainDec_nodeRel f X _ _ h _ hx
  · intro ℓ
    by_cases hl : ℓ.1.2 = X.lonePath
    · have hm : G.mark ℓ ≠ none := by
        rw [hX.2.1 ℓ]
        simp [hl]
      have hpℓ : G.pair ℓ = ℓ := (G.pair_eq_iff ℓ).2 hm
      rw [hpℓ]
    · have hm := hX.2.2 ℓ hl
      have hp := chainDec_pairs f X _ _ h
      rcases List.mem_append.mp hm with hm | hm
      · exact hp _ hm
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
        have := hp q hq
        obtain ⟨q1, q2⟩ := q
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hqe
        obtain ⟨rfl, rfl⟩ := hqe
        exact this.symm

end WaveTurbulence.PL234
