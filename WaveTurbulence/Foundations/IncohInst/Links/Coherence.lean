/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks

/-!
# Coherent layered regular objects and the incoherency index (packet C2)

TARGET Def `defcoh` (L885–L887): a layered regular couple or tree is coherent if `𝔏_𝔫 = 𝔏_{𝔫'}` for
every link `(𝔫, 𝔫')`; the incoherency index `g` is the number of links with `𝔏_𝔫 ≠ 𝔏_{𝔫'}`.

The B2 draft defines `LayeredGarden.incoherency` by counting pairs of branching nodes; here it is
the number of links with different layers (`incoherency_eq_count`, `tree_incoherency_eq_count`),
it is at most the number of links `n/2`, and it vanishes iff the object is coherent.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg Finset

variable {w : ℕ}

/-- The layer at a global address (`0` away from the nodes). -/
def layerAt (LG : LayeredGarden w) (x : Fin w × Path) : ℕ :=
  if h : x.2 ∈ (LG.garden.tree x.1).nodes then LG.layer ⟨x, h⟩ else 0

theorem layerAt_node (LG : LayeredGarden w) (a : GNode LG.garden.tree) : layerAt LG a.1 = LG.layer a := by
  unfold layerAt
  rw [dite_cond_eq_true (eq_true a.2)]
  rfl

/-- The incoherency index counts the links with different layers. -/
theorem incoherency_eq_count_of (LG : LayeredGarden w) (L : List ((Fin w × Path) × (Fin w × Path)))
    (hnd : L.Nodup) (hb : ∀ l ∈ L, l.1.2 ∈ (LG.garden.tree l.1.1).branching ∧
      l.2.2 ∈ (LG.garden.tree l.2.1).branching) :
    LG.incoherency L = (L.filter fun l => layerAt LG l.1 ≠ layerAt LG l.2).length := by
  unfold LayeredGarden.incoherency
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  refine Finset.card_bij (fun bb _ => (bb.1.1, bb.2.1)) ?_ ?_ ?_
  · intro bb hbb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbb
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    refine ⟨hbb.1, ?_⟩
    have e1 := layerAt_node LG bb.1.toNode
    have e2 := layerAt_node LG bb.2.toNode
    change layerAt LG bb.1.toNode.1 ≠ layerAt LG bb.2.toNode.1
    rw [e1, e2]
    exact hbb.2
  · intro bb₁ _ bb₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  · intro l hl
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hl
    obtain ⟨h1, h2⟩ := hb l hl.1
    refine ⟨(⟨l.1, h1⟩, ⟨l.2, h2⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hl.1, ?_⟩
    have e1 := layerAt_node LG (GBranch.toNode (⟨l.1, h1⟩ : GBranch LG.garden.tree))
    have e2 := layerAt_node LG (GBranch.toNode (⟨l.2, h2⟩ : GBranch LG.garden.tree))
    rw [← e1, ← e2]
    exact hl.2

theorem nodup_of_flat_nodup {α : Type*} {L : List (α × α)} (h : (flatPairs L).Nodup) : L.Nodup := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [flatPairs_cons, List.nodup_cons, List.nodup_cons] at h
    refine List.nodup_cons.2 ⟨fun hp => h.1 (List.mem_cons_of_mem _ (mem_flatPairs hp (Or.inl rfl))),
      ih h.2.2⟩

/-- **The incoherency index of a layered regular couple** (TARGET Def `defcoh`) is the number of
its links `(𝔫, 𝔫')` with `𝔏_𝔫 ≠ 𝔏_{𝔫'}`. -/
theorem incoherency_eq_count {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden) :
    LG.incoherency Q.links = (Q.links.filter fun l => layerAt LG l.1 ≠ layerAt LG l.2).length :=
  incoherency_eq_count_of LG _ (nodup_of_flat_nodup (couple_links_flat_nodup Q)) fun l hl =>
    ⟨(link_branching hQ hl).1, (link_branching hQ hl).2.1⟩

/-- The incoherency index of a layered regular tree. -/
theorem tree_incoherency_eq_count {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) :
    LG.incoherency (X.treeLinks (LG.garden.sig 0)) =
      ((X.treeLinks (LG.garden.sig 0)).filter fun l => layerAt LG l.1 ≠ layerAt LG l.2).length :=
  incoherency_eq_count_of LG _ (nodup_of_flat_nodup (tree_links_flat_nodup X _)) fun l hl =>
    ⟨(tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩),
      (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)⟩

/-- The incoherency index is at most the number of links, `n(𝒬)/2`. -/
theorem incoherency_le {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden) :
    LG.incoherency Q.links * 2 ≤ Q.size := by
  rw [incoherency_eq_count hQ, ← couple_linksAt_length Q ((0 : Fin 2), ([] : Path))
    ((1 : Fin 2), ([] : Path))]
  exact Nat.mul_le_mul_right 2 (List.length_filter_le _ _)

/-- **Coherence** (TARGET Def `defcoh`): index `0` iff the two nodes of every link lie in the same
layer. -/
theorem coherent_iff {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden) :
    LG.incoherency Q.links = 0 ↔ ∀ l ∈ Q.links, layerAt LG l.1 = layerAt LG l.2 := by
  rw [incoherency_eq_count hQ, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  simp

/-- Coherence of a layered regular tree. -/
theorem tree_coherent_iff {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden) :
    LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0 ↔
      ∀ l ∈ X.treeLinks (LG.garden.sig 0), layerAt LG l.1 = layerAt LG l.2 := by
  rw [tree_incoherency_eq_count hX, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  simp

end WaveTurbulence.Links
