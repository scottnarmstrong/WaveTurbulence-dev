/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationSubstitution
public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationSubtree
public import WaveTurbulence.Foundations.Molecule.LeafInsertion

/-! # Literal forest insertion commutes with raw reconstruction inflation -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist

@[expose] noncomputable def inflateForestAt {w : ℕ} (σ : Fin w → ℤˣ)
    (X : Address w → RegChain) (Y : Address w → TTree) (F : Fin w → TTree) : Fin w → TTree :=
  fun j => inflateTreeAt σ X Y (F j) (j,[])

/-- A source leaf with literal leaf replacement remains a literal actual leaf. -/
@[expose] noncomputable def inflatedLeaf {w : ℕ} (σ : Fin w → ℤˣ)
    (X : Address w → RegChain) (Y : Address w → TTree) (F : Fin w → TTree)
    (h : GLeaf F) (hY : Y h.1 = .leaf) : GLeaf (inflateForestAt σ X Y F) :=
  ⟨addrExt (h.1.1,[]) (inflationFrame X (h.1.1,[]) h.1.2), by
    have hs := inflateTreeAt_subtree σ X Y (F h.1.1) h.1.2 .leaf
      (Comb.subtree_of_mem_leaves h.2) (h.1.1,[])
    have ha : addrExt (h.1.1,[]) h.1.2 = h.1 := Prod.ext rfl (List.nil_append _)
    have hl : inflateTreeAt σ X Y .leaf (addrExt (h.1.1,[]) h.1.2) = .leaf := (congrArg Y ha).trans hY
    have hs' : Comb.subtree (inflateForestAt σ X Y F h.1.1)
        (inflationFrame X (h.1.1,[]) h.1.2) = some .leaf := hs.trans (congrArg some hl)
    have hm := (Comb.subtree_leaves_iff hs' []).mp (Finset.mem_singleton_self [])
    simpa only [List.nil_append, List.append_nil, addrExt] using hm⟩

theorem inflatedLeaf_index {w : ℕ} (σ : Fin w → ℤˣ) (X : Address w → RegChain)
    (Y : Address w → TTree) (F : Fin w → TTree) (h : GLeaf F) (hY : Y h.1 = .leaf) :
    (inflatedLeaf σ X Y F h hY).1.1 = h.1.1 := rfl

/-- Inflation of a leaf insertion is actual insertion at the inflated leaf. -/
theorem inflateForest_insertLeaf {w : ℕ} (σ : Fin w → ℤˣ)
    (X : Address w → RegChain) (Y : Address w → TTree) (F : Fin w → TTree)
    (h : GLeaf F) (hY : Y h.1 = .leaf) (t : TTree) :
    inflateForestAt σ X Y (insertLeaf F h t) =
      insertLeaf (inflateForestAt σ X Y F) (inflatedLeaf σ X Y F h hY) (inflateTreeAt σ X Y t h.1) := by
  funext j
  by_cases hj : j = h.1.1
  · subst j
    change inflateTreeAt σ X Y (insertLeaf F h t h.1.1) (h.1.1,[]) =
      insertLeaf (inflateForestAt σ X Y F) (inflatedLeaf σ X Y F h hY) (inflateTreeAt σ X Y t h.1) h.1.1
    rw [insertLeaf_at F h t]
    have hins : insertLeaf (inflateForestAt σ X Y F) (inflatedLeaf σ X Y F h hY)
        (inflateTreeAt σ X Y t h.1) h.1.1 =
      Comb.replaceAt (inflateTreeAt σ X Y (F h.1.1) (h.1.1,[]))
        (inflationFrame X (h.1.1,[]) h.1.2) (inflateTreeAt σ X Y t h.1) :=
      insertLeaf_at (inflateForestAt σ X Y F) (inflatedLeaf σ X Y F h hY) _
    have ha : addrExt (h.1.1,[]) h.1.2 = h.1 := Prod.ext rfl (List.nil_append _)
    have htree : inflateTreeAt σ X Y (Comb.replaceAt (F h.1.1) h.1.2 t) (h.1.1,[]) =
        Comb.replaceAt (inflateTreeAt σ X Y (F h.1.1) (h.1.1,[]))
          (inflationFrame X (h.1.1,[]) h.1.2) (inflateTreeAt σ X Y t h.1) :=
      (inflateTreeAt_replace σ X Y (F h.1.1) h.1.2 (TTree.leaves_subset_nodes _ h.2) t (h.1.1,[])).trans
        (congrArg (Comb.replaceAt (inflateTreeAt σ X Y (F h.1.1) (h.1.1,[]))
          (inflationFrame X (h.1.1,[]) h.1.2)) (congrArg (inflateTreeAt σ X Y t) ha))
    exact htree.trans hins.symm

  · change inflateTreeAt σ X Y (insertLeaf F h t j) (j,[]) =
      insertLeaf (inflateForestAt σ X Y F) (inflatedLeaf σ X Y F h hY) (inflateTreeAt σ X Y t h.1) j
    rw [insertLeaf_other F h t j hj,
      insertLeaf_other (inflateForestAt σ X Y F) (inflatedLeaf σ X Y F h hY) _ j hj]
    rfl

end WaveTurbulence.LFTwist
