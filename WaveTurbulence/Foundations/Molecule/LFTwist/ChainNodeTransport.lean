/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ChainPairTransport
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainNodes

/-! # Every ordinary native tree node follows the literal physical exchange -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist RegRed
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S)

/-- Even the lone boundary node cannot enter any other nonancestor source slot. -/
theorem chain_context_not_below_source (b : GBranch S.tree) (n : GNode S.tree)
    (hn : ¬ Below n.1 b.1) (q : Path)
    (hq : q ∈ ((D.tree b).plug (nodeSign S.sig b.1) .leaf).nodes) :
    ¬ Below (inflatedPosition S D.tree n) (addrExt (inflatedPosition S D.tree b.toNode) q) := by
  by_cases hb : Below b.1 n.1
  · have hne : b.toNode ≠ n := fun he => hn (he ▸ ⟨rfl,List.prefix_refl _⟩)
    obtain ⟨i,hi⟩ := below_child_of_desc_ne b n hb hne
    have hc := inflatedPosition_below S D.tree (b.child i) n hi
    rw [D.core_child_position] at hc
    intro he
    have hh := below_trans hc he
    change Below (addrExt (addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath) [i])
      (addrExt (inflatedPosition S D.tree b.toNode) q) at hh
    rw [addrExt_append] at hh
    have hp := (below_frames_iff _ _ _).mp hh
    have hl := hp.length_le
    have hs : (D.tree b).lonePath <+: q := (List.prefix_append _ [i]).trans hp
    have heq := leaf_prefix_node_eq (chain_lone_mem_leaves (D.tree b) (nodeSign S.sig b.1)) hq hs
    rw [← heq] at hl
    simp only [List.length_append,List.length_singleton] at hl
    omega
  · have hi := inflatedPosition_incomp S D.tree n b.toNode ⟨hn,hb⟩
    exact (hi.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ q)).1

variable (S) (P : CorePlacement S) (hS : S.IsPlain)

/-- The full ordinary native context is fixed when its root is outside the crown. -/
theorem inflatedExchange_chain_node_fixed (b : GBranch S.tree) (hb : ¬ Below P.lower.1 b.1)
    (q : Path) (hq : q ∈ ((D.tree b).plug (nodeSign S.sig b.1) .leaf).nodes) :
    inflatedExchange S P D (addrExt (inflatedPosition S D.tree b.toNode) q) =
      addrExt (inflatedPosition S D.tree b.toNode) q := by
  have ha := chain_context_not_below_source D b P.lower.toNode hb q hq
  have hp : ¬ Below (S.pair P.retained).1 b.1 := by
    intro he
    exact leaf_not_prefix_branch (S.pair P.retained).2 (he.1 ▸ b.2) he.2
  have hd := chain_context_not_below_source D b (S.pair P.retained).toNode hp q hq
  have he : addrExt (inflatedPosition S D.tree b.toNode) q ≠
      inflatedPosition S D.tree (S.pair P.retained).toNode := by
    intro he
    exact hd (he ▸ ⟨rfl,List.prefix_refl _⟩)
  exact (ite_eq_right ha).trans (ite_eq_right he)

/-- Literal address transport for every node of an unchanged regular tree,
including the native distinguished lone leaf. -/
theorem ordinary_chain_node_address_twist (hnil : D.tree P.lower = .nil)
    (b : GBranch S.tree) (hb : b ≠ P.lower) (q : Path)
    (hq : q ∈ ((D.tree b).plug (nodeSign S.sig b.1) .leaf).nodes) :
    addrExt (inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
        (coreBranchEquiv S P b).toNode) q =
      inflatedExchange S P D (addrExt (inflatedPosition S D.tree b.toNode) q) := by
  have hr := inflatedPosition_branch_twist S P hS D hnil b
  apply (congrArg (fun z => addrExt z q) hr).trans
  by_cases hin : Below P.lower.1 b.1
  · exact ((inflatedExchange_branch_respectsAt_inside S P D b hin hb) q).symm
  · have hp : inflatedExchange S P D (inflatedPosition S D.tree b.toNode) =
        inflatedPosition S D.tree b.toNode  := by
      simpa only [Links.addrExt_nil] using
        inflatedExchange_chain_node_fixed S D P b hin [] (nil_mem_nodes _)
    exact (congrArg (fun z => addrExt z q) hp).trans
      (inflatedExchange_chain_node_fixed S D P b hin q hq).symm

end WaveTurbulence.LFTwist
