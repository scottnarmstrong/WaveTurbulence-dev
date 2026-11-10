/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntClassSum
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCount
public import WaveTurbulence.Foundations.Stage1.Shared.SkelFacts3

/-! # B3s MK-SLOTS (integration, assembly 1): counting cap slots and protected nodes

* `skel_tree_leaf`, `shape_tree_leaf`: cap trees are single leaves in the skeleton and in `G_sb`;
* `no_capcap_of_irred`: in an irreducible garden of width `2R` with `|J| = R` single-leaf cap trees, no cap root is
  paired with a cap root;
* `card_capPairs`: there are exactly `|J|` cap pairs; `prod_capSlot`: a factor on every cap slot gives its `|J|`-th
  power;
* `card_le_protI`: the `R` roots of the non-cap trees are protected, so `R ≤ |Π|`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineB WaveTurbulence.RedSplice

namespace WaveTurbulence.Flower.MkSlots.IntAsm

variable {w : ℕ}

/-- A skeleton tree whose reconstruction is a single leaf is a single leaf. -/
theorem skel_tree_leaf {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) {j : Fin w}
    (hj : D.forest hS j = TTree.leaf) : S.tree j = TTree.leaf := by
  have hroot := IntGeo.root_mem_leaves (D := D) (hS := hS) hj
  cases ht : S.tree j with
  | leaf => rfl
  | node l m r =>
    rw [ht] at hroot
    simp [TTree.leaves, TTree.nil_notMem_pre] at hroot

/-- Through a splice shape, single-leaf trees stay single leaves. -/
theorem shape_tree_leaf {S : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
    {G : Garden w} (Φ : SpliceShape blk G) {j : Fin w} (hj : S.tree j = TTree.leaf) : G.tree j = TTree.leaf := by
  cases ht : G.tree j with
  | leaf => rfl
  | node l m r =>
    exfalso
    have hb : ([] : Path) ∈ (G.tree j).branching := by rw [ht]; simp [TTree.branching]
    let c : GBranch G.tree := ⟨(j, []), hb⟩
    have h1 : (Φ.br c).toNode = GNode.root S.tree j := by
      rw [Φ.br_node]
      exact Φ.root j
    have h2 := (Φ.br c).2
    have h3 : (Φ.br c).1 = (j, []) := congrArg Subtype.val h1
    rw [h3, hj] at h2
    simp [TTree.branching] at h2

/-- The leaf of a single-leaf tree. -/
theorem leaf_eq_root {G : Garden w} {j : Fin w} (hj : G.tree j = TTree.leaf) (ℓ : GLeaf G.tree)
    (hℓ : ℓ.1.1 = j) : ℓ = rootLeaf G j hj := eq_rootLeaf hj ℓ hℓ

/-- **No two cap roots are paired** in an irreducible garden of width `2R` with `R` single-leaf cap trees. -/
theorem no_capcap_of_irred {R : ℕ} (G : Garden (2 * R)) (hp : G.IsPlain) (hirr : G.Irreducible)
    (J : Finset (Fin (2 * R))) (hJ : J.card = R) (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) :
    ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J := by
  intro ℓ hℓ hp'
  have hne : G.pair ℓ ≠ ℓ := fun he => ((G.pair_eq_iff ℓ).mp he) (hp ℓ)
  have hjj : ℓ.1.1 ≠ (G.pair ℓ).1.1 := by
    intro he
    exact hne ((leaf_eq_root (hcap _ hℓ) (G.pair ℓ) he.symm).trans (leaf_eq_root (hcap _ hℓ) ℓ rfl).symm)
  set A : Finset (Fin (2 * R)) := {ℓ.1.1, (G.pair ℓ).1.1} with hA
  have hAcard : A.card = 2 := Finset.card_pair hjj
  have hR2 : 2 ≤ R := by
    have hsub : A ⊆ J := by
      intro x hx
      rw [hA, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hℓ
      · exact hp'
    have := Finset.card_le_card hsub
    omega
  refine hirr A ⟨ℓ.1.1, by simp [hA]⟩ ?_ ?_
  · intro hAu
    have h1 : A.card = 2 * R := by rw [hAu, Finset.card_univ, Fintype.card_fin]
    omega
  · intro m hm
    have hm1 : m.1.1 ∈ A := (Finset.mem_filter.mp hm).2
    have hmm : m = ℓ ∨ m = G.pair ℓ := by
      rw [hA, Finset.mem_insert, Finset.mem_singleton] at hm1
      rcases hm1 with h | h
      · exact Or.inl ((leaf_eq_root (hcap _ hℓ) m h).trans (leaf_eq_root (hcap _ hℓ) ℓ rfl).symm)
      · exact Or.inr ((leaf_eq_root (hcap _ hp') m h).trans (leaf_eq_root (hcap _ hp') (G.pair ℓ) rfl).symm)
    refine ⟨fun he => ((G.pair_eq_iff m).mp he) (hp m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rcases hmm with rfl | rfl
    · simp [hA]
    · rw [G.pair_pair]; simp [hA]

/-- **There are exactly `|J|` cap pairs.** -/
theorem card_capPairs (G : Garden w) (hG : G.IsPlain) (J : Finset (Fin w))
    (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) (hcc : ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J) :
    (univ.filter fun q : SourcePair G => IsCapPair G hG J q).card = J.card := by
  refine (Finset.card_bij' (fun j hj => pairOfLeaf G hG (rootLeaf G j (hcap j hj)))
    (fun q _ => capTreeOf G hG J q) (fun j hj => ?_) (fun q hq => ?_) (fun j hj => ?_) (fun q hq => ?_)).symm
  · refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    unfold IsCapPair
    rcases IntRest.pairOfLeaf_sides hG (rootLeaf G j (hcap j hj)) with ⟨e1, -⟩ | ⟨-, e2⟩
    · rw [e1]; exact Or.inl hj
    · rw [e2]; exact Or.inr hj
  · have hq' := (mem_filter.mp hq).2
    unfold capTreeOf
    split_ifs with h1
    · exact h1
    · exact hq'.resolve_left h1
  · unfold capTreeOf
    rcases IntRest.pairOfLeaf_sides hG (rootLeaf G j (hcap j hj)) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1]
      exact if_pos (c := (rootLeaf G j (hcap j hj)).1.1 ∈ J) hj
    · have hn : (G.pair (rootLeaf G j (hcap j hj))).1.1 ∉ J := hcc _ hj
      rw [e1, if_neg hn, e2]; rfl
  · have hq' := (mem_filter.mp hq).2
    have hpair : G.pair (q.firstLeaf hG) = q.secondLeaf hG := VineEstS4.pair_first_eq_second hG q
    unfold capTreeOf
    split_ifs with h1
    · rw [← leaf_eq_root (hcap _ h1) (q.firstLeaf hG) rfl]
      exact pairOfLeaf_firstLeaf G hG q
    · have h2 := hq'.resolve_left h1
      rw [← leaf_eq_root (hcap _ h2) (q.secondLeaf hG) rfl, ← hpair, pairOfLeaf_partner]
      exact pairOfLeaf_firstLeaf G hG q

/-- A factor on every cap slot gives its `|J|`-th power. -/
theorem prod_capSlot {M : Type*} [CommMonoid M] (G : Garden w) (hG : G.IsPlain) (J : Finset (Fin w))
    (hcap : ∀ j ∈ J, G.tree j = TTree.leaf) (hcc : ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ J → (G.pair ℓ).1.1 ∉ J) (x : M) :
    ∏ t : ReplacementSlot G, (if IntMember.IsCapSlot hG J t then x else 1) = x ^ J.card := by
  unfold ReplacementSlot
  rw [Fintype.prod_sum_type]
  have h2 : ∏ b : GBranch G.tree, (if IntMember.IsCapSlot hG J (Sum.inr b) then x else 1) = 1 :=
    Finset.prod_eq_one fun b _ => if_neg (by rintro ⟨q, hq, -⟩; cases hq)
  have h1 : ∀ q : SourcePair G, (if IntMember.IsCapSlot hG J (Sum.inl q) then x else 1) =
      if IsCapPair G hG J q then x else 1 := by
    intro q
    by_cases hq : IsCapPair G hG J q
    · rw [if_pos ⟨q, rfl, hq⟩, if_pos hq]
    · rw [if_neg (by rintro ⟨q', hq', hc⟩; cases hq'; exact hq hc), if_neg hq]
  rw [h2, mul_one, Finset.prod_congr rfl fun q _ => h1 q, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const, card_capPairs G hG J hcap hcc]

end WaveTurbulence.Flower.MkSlots.IntAsm
