/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CoupleCollapseOutside
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Replace

/-! # Concrete outside agreement for layered couple collapse -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ} (LG : LayeredGarden w) {a b : GNode LG.garden.tree}
    (h : Comb.IsSubCouple LG.garden a b)

/-- The source descendant conventions differ only in orientation of the index equality. -/
theorem under_iff_below (x y : Address w) : Under x y ↔ Below x y :=
  and_congr eq_comm Iff.rfl

theorem coupleCollapse_node_layer (p : ℕ) (hc : LG.CanonCriterion p)
    (hplain : LG.garden.IsPlain) (n : GNode LG.garden.tree)
    (m : GNode (collapseCoupleGarden h).tree)
    (ha : ¬ Below a.1 n.1) (hb : ¬ Below b.1 n.1) (he : n.1 = m.1) :
    LG.layer n = (collapseCoupleLayered LG h p).layer m := by
  obtain ⟨q,hq⟩ := (Twist.nodePieceEquiv LG.garden.tree).surjective n
  cases q with
  | inl c =>
    change c.toNode = n at hq
    let d : GBranch (collapseCoupleGarden h).tree := ⟨m.1,
      (coupleCollapse_branch_outside LG h n.1 ha hb).mpr (by rw [← hq]; exact c.2) |>
        (fun ht => he ▸ ht)⟩
    have hd : d.toNode = m := Subtype.ext rfl
    have hc' : (collapseCoupleBranchEmbedding h d).toNode = n := Subtype.ext he.symm
    rw [← hd, collapseCoupleLayered_branch LG h p, hc']
  | inr l =>
    change l.toNode = n at hq
    let k : GLeaf (collapseCoupleGarden h).tree := ⟨m.1,
      (coupleCollapse_leaf_outside LG h n.1 ha hb).mpr (by rw [← hq]; exact l.2) |>
        (fun ht => he ▸ ht)⟩
    have hk : k.toNode = m := Subtype.ext rfl
    have hl : l.1 = n.1 := congrArg (fun v : GNode LG.garden.tree => v.1) hq
    have result := coupleCollapse_leaf_layer LG h p hc hplain l k
      (hl ▸ ha) (hl ▸ hb) (hl.trans he)
    exact (congrArg LG.layer hq).symm.trans (result.trans
      (congrArg (collapseCoupleLayered LG h p).layer hk))

/-- This is literal C4 outside agreement for the constructed garden, not an
assumption that the replacement is canonical. -/
theorem collapseCouple_outAgree (p : ℕ) (hc : LG.CanonCriterion p)
    (hplain : LG.garden.IsPlain) :
    OutAgree LG (collapseCoupleLayered LG h p) a.1 b.1 := by
  have ho (z : Address w) (hz : ¬ InRegion a.1 b.1 z) :
      ¬ Below a.1 z ∧ ¬ Below b.1 z := by
    exact ⟨fun ht => hz (Or.inl ((under_iff_below a.1 z).mpr ht)),
      fun ht => hz (Or.inr ((under_iff_below b.1 z).mpr ht))⟩
  constructor
  · intro z hz
    exact (coupleCollapse_node_outside LG h z (ho z hz).1 (ho z hz).2).symm
  · intro z hz
    exact (coupleCollapse_leaf_outside LG h z (ho z hz).1 (ho z hz).2).symm
  · intro z hz
    have hi := coupleCollapse_node_outside LG h z (ho z hz).1 (ho z hz).2
    by_cases hn : z.2 ∈ (LG.garden.tree z.1).nodes
    · have hm := hi.mpr hn
      rw [layerAt_of_mem LG hn, layerAt_of_mem (collapseCoupleLayered LG h p) hm]
      exact coupleCollapse_node_layer LG h p hc hplain ⟨z,hn⟩ ⟨z,hm⟩ (ho z hz).1 (ho z hz).2 rfl
    · have hm := mt hi.mp hn
      have hm' : z.2 ∉ ((collapseCoupleLayered LG h p).garden.tree z.1).nodes := hm
      unfold layerAt
      rw [dite_eq_right hn, dite_eq_right hm']
  · intro l m hz he
    exact coupleCollapse_pair_outside LG h l m (ho l.1 hz).1 (ho l.1 hz).2 he

end WaveTurbulence.LFTwist
