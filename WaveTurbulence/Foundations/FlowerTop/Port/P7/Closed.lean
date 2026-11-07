/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueSurj
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Gardens
/-! FLOWER-P7: pairing-closed sets of trees of a plain garden have balanced signs. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

/-- A set `S` of tree indices is closed under the pairing if the leaves of its trees are completely paired
(the notion in `Garden.Irreducible`). -/
def ClosedTrees {w : ℕ} (G : Garden w) (S : Finset (Fin w)) : Prop := G.CompletelyPaired (G.leavesOf S)

theorem balanced_of_closed {w : ℕ} (G : Garden w) (S : Finset (Fin w)) (hS : ClosedTrees G S) :
    ∑ j ∈ S, ((G.sig j : ℤˣ) : ℤ) = 0 := by
  classical
  have hκ : IsDecoration G (fun _ => (1 : ℤ)) := ⟨fun _ => by norm_num, fun _ => rfl⟩
  have hz := Comb.sum_signed_completelyPaired hS (fun _ => (1 : ℤ)) hκ.2
  have hr : ∀ j, ((G.sig j : ℤˣ) : ℤ) =
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ : GLeaf G.tree => ℓ.1.1 = j), ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) := by
    intro j
    have h := sum_rule G.sig (fun _ => (1 : ℤ)) hκ.1 (GNode.root G.tree j)
    simpa [nodeSign, GNode.root, pathSign, GNode.leavesBelow, GNode.IsDesc, GLeaf.toNode, eq_comm] using h
  have hsum : ∑ ℓ ∈ G.leavesOf S, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) = ∑ j ∈ S, ((G.sig j : ℤˣ) : ℤ) := by
    rw [Finset.sum_congr rfl fun j _ => hr j]
    rw [← Finset.sum_fiberwise_of_maps_to (s := G.leavesOf S) (t := S) (g := fun ℓ => ℓ.1.1)
      (fun ℓ hℓ => by simpa [Garden.leavesOf] using hℓ)]
    refine Finset.sum_congr rfl fun j hj => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ℓ
    simp only [Finset.mem_filter, Garden.leavesOf, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨h ▸ hj, h⟩
  simpa [hsum] using hz

theorem mem_leavesOf {w : ℕ} (G : Garden w) (S : Finset (Fin w)) (ℓ : GLeaf G.tree) :
    ℓ ∈ G.leavesOf S ↔ ℓ.1.1 ∈ S := by
  simp [Garden.leavesOf]

theorem closedTrees_univ {w : ℕ} (G : Garden w) (hG : G.IsPlain) : ClosedTrees G Finset.univ := by
  intro ℓ _
  refine ⟨Comb.pair_ne_of_plain hG ℓ, ?_⟩
  rw [mem_leavesOf]; exact Finset.mem_univ _

theorem closedTrees_iff {w : ℕ} (G : Garden w) (hG : G.IsPlain) (S : Finset (Fin w)) :
    ClosedTrees G S ↔ ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ S → (G.pair ℓ).1.1 ∈ S := by
  unfold ClosedTrees Garden.CompletelyPaired
  simp only [mem_leavesOf]
  constructor
  · intro h ℓ hℓ; exact (h ℓ hℓ).2
  · intro h ℓ hℓ; exact ⟨Comb.pair_ne_of_plain hG ℓ, h ℓ hℓ⟩

theorem closedTrees_inter {w : ℕ} (G : Garden w) (hG : G.IsPlain) {S S' : Finset (Fin w)}
    (h : ClosedTrees G S) (h' : ClosedTrees G S') : ClosedTrees G (S ∩ S') := by
  rw [closedTrees_iff G hG] at h h' ⊢
  intro ℓ hℓ
  exact Finset.mem_inter.2 ⟨h ℓ (Finset.mem_inter.1 hℓ).1, h' ℓ (Finset.mem_inter.1 hℓ).2⟩

theorem closedTrees_compl {w : ℕ} (G : Garden w) (hG : G.IsPlain) {S : Finset (Fin w)}
    (h : ClosedTrees G S) : ClosedTrees G Sᶜ := by
  rw [closedTrees_iff G hG] at h ⊢
  intro ℓ hℓ
  rw [Finset.mem_compl] at hℓ ⊢
  intro hp
  exact hℓ (by simpa [G.pair_pair] using h (G.pair ℓ) hp)

theorem closedTrees_sdiff {w : ℕ} (G : Garden w) (hG : G.IsPlain) {S T : Finset (Fin w)}
    (h : ClosedTrees G S) (h' : ClosedTrees G T) : ClosedTrees G (S \ T) := by
  rw [Finset.sdiff_eq_inter_compl]
  exact closedTrees_inter G hG h (closedTrees_compl G hG h')

/-- Minimality of the closed set `S` containing `s₀`. -/
def MinimalAt {w : ℕ} (G : Garden w) (s₀ : Fin w) (S : Finset (Fin w)) : Prop :=
  s₀ ∈ S ∧ ClosedTrees G S ∧ ∀ T : Finset (Fin w), ClosedTrees G T → s₀ ∈ T → T ⊆ S → T = S

/-- A minimal closed set of trees containing `i₀`. -/
theorem exists_minimal_closed {w : ℕ} (G : Garden w) (hG : G.IsPlain) (i₀ : Fin w) :
    ∃ S : Finset (Fin w), MinimalAt G i₀ S := by
  classical
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset (Fin w))).filter fun S => i₀ ∈ S ∧ ClosedTrees G S) Finset.card
    ⟨Finset.univ, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact closedTrees_univ G hG⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
  refine ⟨m, hm.1, hm.2, fun T hT hi hsub => ?_⟩
  exact Finset.eq_of_subset_of_card_le hsub (hmin T ⟨hi, hT⟩)

theorem minimal_closed_unique {w : ℕ} (G : Garden w) (hG : G.IsPlain) (i₀ : Fin w) {S S' : Finset (Fin w)}
    (hS : MinimalAt G i₀ S) (hS' : MinimalAt G i₀ S') : S = S' := by
  have h1 := hS.2.2 (S ∩ S') (closedTrees_inter G hG hS.2.1 hS'.2.1) (Finset.mem_inter.2 ⟨hS.1, hS'.1⟩)
    Finset.inter_subset_left
  have h2 := hS'.2.2 (S ∩ S') (closedTrees_inter G hG hS.2.1 hS'.2.1) (Finset.mem_inter.2 ⟨hS.1, hS'.1⟩)
    Finset.inter_subset_right
  rw [h1] at h2
  exact h2

end WaveTurbulence.FlowerP7

