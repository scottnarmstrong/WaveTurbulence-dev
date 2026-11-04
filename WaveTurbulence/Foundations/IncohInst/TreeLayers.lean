/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeLinkCoordinates

/-! # Exact source layer counts and bounds for the actual couple link family -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {LG : LayeredGarden 1} {X : RegChain}

/-- The analytic incoherence count is precisely B2's decoded source incoherence count. -/
theorem treeLayerLinks_incoherenceCount (d : ℕ) (hX : X.DecodesTree LG.garden) :
    incoherenceCount (treeLayerLinks (d := d) LG hX) = LG.incoherency (X.treeLinks (LG.garden.sig 0)) := by
  unfold incoherenceCount LayeredGarden.incoherency
  apply Finset.card_bij (fun j _ => (treeLinkBranch hX j 0, treeLinkBranch hX j 1))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨?_, ?_⟩
    · exact List.get_mem (X.treeLinks (LG.garden.sig 0)) j
    · change (LG.layer (treeLinkBranch hX j 0).toNode : ℤ) ≠
        LG.layer (treeLinkBranch hX j 1).toNode at hj
      exact_mod_cast hj
  · intro i _ j _ he
    have he' := congrArg (fun p => (p.1.1, p.2.1)) he
    exact (nodup_of_flat_nodup (tree_links_flat_nodup X (LG.garden.sig 0))).get_inj_iff.mp he'
  · intro bb hbb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbb
    obtain ⟨j, hj⟩ := List.get_of_mem hbb.1
    have he : (treeLinkBranch hX j 0, treeLinkBranch hX j 1) = bb := by
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hj)
      · exact Subtype.ext (congrArg Prod.snd hj)
    refine ⟨j, ?_, he⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (LG.layer (treeLinkBranch hX j 0).toNode : ℤ) ≠ LG.layer (treeLinkBranch hX j 1).toNode
    rw [show treeLinkBranch hX j 0 = bb.1 from congrArg Prod.fst he,
      show treeLinkBranch hX j 1 = bb.2 from congrArg Prod.snd he]
    exact_mod_cast hbb.2

/-- The total source layer bound supplies the analytic layer-span bound. -/
theorem treeLayerLinks_span (d : ℕ) (hX : X.DecodesTree LG.garden) {p : ℕ}
    (hp : ∀ a, LG.layer a ≤ p) (j : Fin (X.treeLinks (LG.garden.sig 0)).length) :
    |(((treeLayerLinks (d := d) LG hX j).leftLayer : ℝ)) -
      (treeLayerLinks (d := d) LG hX j).rightLayer| + 1 ≤ (p : ℝ) + 1 := by
  have h0 := hp (treeLinkBranch hX j 0).toNode
  have h1 := hp (treeLinkBranch hX j 1).toNode
  change |((LG.layer (treeLinkBranch hX j 0).toNode : ℤ) : ℝ) -
    ((LG.layer (treeLinkBranch hX j 1).toNode : ℤ) : ℝ)| + 1 ≤ _
  push_cast
  have ha : (0 : ℝ) ≤ LG.layer (treeLinkBranch hX j 0).toNode := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ LG.layer (treeLinkBranch hX j 1).toNode := Nat.cast_nonneg _
  have h0' : (LG.layer (treeLinkBranch hX j 0).toNode : ℝ) ≤ p := by exact_mod_cast h0
  have h1' : (LG.layer (treeLinkBranch hX j 1).toNode : ℝ) ≤ p := by exact_mod_cast h1
  have hab : |(LG.layer (treeLinkBranch hX j 0).toNode : ℝ) -
      LG.layer (treeLinkBranch hX j 1).toNode| ≤ p := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith only [hab]

end WaveTurbulence.IncohInst
