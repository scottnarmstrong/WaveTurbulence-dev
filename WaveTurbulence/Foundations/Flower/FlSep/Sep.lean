/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Lemmas
public import WaveTurbulence.Foundations.Vine.B.Geom
/-! # FL-SEP: high-root separation (supplement Lemma 9.2, PLAN §2.3)

On a flower garden with all frontier momenta of size at most `r`, and `(2N+2) r ≤ ‖k_root‖/4`, every stem node
`v` and every off-stem top node `w` of the same tree satisfy `‖k_root‖/2 ≤ ‖k_v - k_w‖`.

Proof: an off-stem top node `a` has `‖k_a‖ ≤ (2 cnt a + 1) r` (`cnt a` = number of layer-`p` branching nodes below
`a`); along the stem the error `‖k_root - s k_a‖` is at most `2 (cnt root - cnt a) r`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FlSep
open Finset WaveTurbulence TTree

variable {w : ℕ}

/-- Top nodes of the initial flower trees: top leaves, and branching nodes of layer `p`. -/
def IsTopNode (LG : LayeredGarden w) (p : ℕ) (a : GNode LG.garden.tree) : Prop :=
  LG.IsTopLeaf p a ∨ ∃ b : GBranch LG.garden.tree, b.toNode = a ∧ LG.layer a = p

section Layers
variable (LG : LayeredGarden w)

theorem layer_le_aux (a : GNode LG.garden.tree) : ∀ (r : List (Fin 3)) (d : GNode LG.garden.tree),
    a.1.1 = d.1.1 → a.1.2 ++ r = d.1.2 → LG.layer d ≤ LG.layer a := by
  intro r
  induction r using List.reverseRecOn with
  | nil =>
    intro d hj hr
    have : d = a := Subtype.ext (Prod.ext hj.symm (by simpa using hr.symm))
    subst this; exact le_rfl
  | append_singleton r i ih =>
    intro d hj hr
    have hmem : a.1.2 ++ r ++ [i] ∈ (LG.garden.tree d.1.1).nodes := by
      rw [List.append_assoc, hr]; exact d.2
    have hb : a.1.2 ++ r ∈ (LG.garden.tree d.1.1).branching := TTree.branching_of_append_mem _ hmem
    let bm : GBranch LG.garden.tree := ⟨(d.1.1, a.1.2 ++ r), hb⟩
    have hd : bm.child i = d := Subtype.ext (Prod.ext rfl (by
      show a.1.2 ++ r ++ [i] = d.1.2
      rw [List.append_assoc]; exact hr))
    calc LG.layer d = LG.layer (bm.child i) := by rw [hd]
      _ ≤ LG.layer bm.toNode := LG.isLayering.1 bm i
      _ ≤ LG.layer a := ih bm.toNode hj rfl

theorem layer_le_of_isDesc {a d : GNode LG.garden.tree} (h : a.IsDesc d) : LG.layer d ≤ LG.layer a := by
  obtain ⟨hj, r, hr⟩ := h
  exact layer_le_aux LG a r d hj hr

end Layers

section Count
variable (LG : LayeredGarden w) (p : ℕ)

theorem cnt_le_topOrder (a : GNode LG.garden.tree) : LG.topCountBelow p a ≤ LG.topOrder p a.1.1 := by
  classical
  unfold LayeredGarden.topCountBelow LayeredGarden.topOrder
  apply Finset.card_le_card
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  exact ⟨hb.1.1.symm, hb.2⟩

theorem cnt_branch (b : GBranch LG.garden.tree) (hb : LG.layer b.toNode = p) :
    1 + ∑ i : Fin 3, LG.topCountBelow p (b.child i) ≤ LG.topCountBelow p b.toNode := by
  classical
  unfold LayeredGarden.topCountBelow
  set X : GNode LG.garden.tree → Finset (GBranch LG.garden.tree) := fun a =>
    Finset.univ.filter fun b' : GBranch LG.garden.tree => a.IsDesc b'.toNode ∧ LG.layer b'.toNode = p with hX
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ j ∈ (Finset.univ : Finset (Fin 3)), i ≠ j →
      Disjoint (X (b.child i)) (X (b.child j)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro b' h1 h2
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hij (GBranch.eq_of_isDesc_child b h1.1 h2.1)
  have hnot : b ∉ Finset.univ.biUnion fun i => X (b.child i) := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact WaveTurbulence.VineB.child_ne_toNode b i hi.1
  have hsub : insert b (Finset.univ.biUnion fun i => X (b.child i)) ⊆ X b.toNode := by
    intro x hx
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨GNode.isDesc_refl _, hb⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hx
      simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨(GBranch.isDesc_child b i).trans hi.1, hi.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_biUnion hdisj, Fin.sum_univ_three] at hc
  rw [Fin.sum_univ_three]
  simpa [hX, add_comm] using hc

end Count

section Top
variable (LG : LayeredGarden w) (p : ℕ)

theorem isTopNode_child (hlay : ∀ a, LG.layer a ≤ p) (b : GBranch LG.garden.tree)
    (hb : LG.layer b.toNode = p) (i : Fin 3) : IsTopNode LG p (b.child i) := by
  have hc : LG.layer (b.child i) ≤ p := hlay _
  have hne : (b.child i).1.2 ≠ [] := WaveTurbulence.VineB.child_nonroot b i
  have hpl : LG.parentLayer p (b.child i) = p := by
    unfold LayeredGarden.parentLayer
    simp only [hne, ↓reduceIte]
    have : (⟨((b.child i).1.1, (b.child i).1.2.dropLast), by
        exact (LG.garden.tree _).dropLast_mem_nodes (b.child i).2⟩ : GNode LG.garden.tree) = b.toNode :=
      Subtype.ext (Prod.ext rfl (by simp [GBranch.child, GBranch.toNode]))
    exact (congrArg LG.layer this).trans hb
  rcases hc.lt_or_eq with hlt | heq
  · exact Or.inl ⟨Or.inl hlt, hne, hpl⟩
  · by_cases hbr : ∃ b' : GBranch LG.garden.tree, b'.toNode = b.child i
    · obtain ⟨b', hb'⟩ := hbr
      exact Or.inr ⟨b', hb', heq⟩
    · simp only [not_exists] at hbr
      refine Or.inl ⟨Or.inr ?_, hne, hpl⟩
      have h2 := (TTree.mem_nodes_iff _ _).1 (b.child i).2
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd h2 (fun h => hbr ⟨_, h2⟩ rfl)

end Top

section Bounds
variable (LG : LayeredGarden w) (p : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d)

end Bounds

section Stem
variable (LG : LayeredGarden w) (p : ℕ)

end Stem

section StemError
variable (LG : LayeredGarden w) (p : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d)

end StemError

section Main
variable (LG : LayeredGarden w) (p N : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d)

end Main

end WaveTurbulence.Flower.FlSep
