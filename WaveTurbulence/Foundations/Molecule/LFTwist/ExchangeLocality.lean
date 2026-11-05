/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.SourcePositionExchange

/-! # Locality of the physical exchange below unchanged attachment roots -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links

/-- Away from the destination and strict ancestors of the source, the exchange
respects every path below the given root. -/
theorem exchange_respectsAt_of_away {w : ℕ} (a b z : Address w) (keep : Fin 3)
    (hza : ¬ Below z a) (hbz : ¬ Below b z) (hzb : ¬ Below z b) :
    RespectsAt (exchangeAddress a b keep) z := by
  by_cases haz : Below a z
  · obtain ⟨q,hq⟩ := haz.2
    have hz : z = addrExt a q := Prod.ext haz.1 hq.symm
    cases q with
    | nil =>
      have he : z = a := hz.trans (addrExt_nil a)
      exact (hza (he ▸ ⟨rfl,List.prefix_refl _⟩)).elim
    | cons i q =>
      have he : z = addrExt (addrExt a [i]) q := hz.trans (addrExt_cons a i q)
      rw [he]
      exact (exchange_respectsAt_lower_child a b keep i).child q
  · intro q
    have haf : a.1 = z.1 → ¬ a.2 <+: z.2 ∧ ¬ z.2 <+: a.2 :=
      fun hi => ⟨fun hp => haz ⟨hi.symm,hp⟩,fun hp => hza ⟨hi,hp⟩⟩
    have hbf : b.1 = z.1 → ¬ b.2 <+: z.2 ∧ ¬ z.2 <+: b.2 :=
      fun hi => ⟨fun hp => hbz ⟨hi.symm,hp⟩,fun hp => hzb ⟨hi,hp⟩⟩
    have he := exchangeAddress_append_fixed a b z keep q haf hbf
    have hr := exchangeAddress_append_fixed a b z keep [] haf hbf
    have hr' : exchangeAddress a b keep z = z := by simpa only [appendAddress,List.append_nil] using hr
    exact he.trans (congrArg (fun x => addrExt x q) hr'.symm)

variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

@[expose] noncomputable def inflatedExchange : Address w → Address w :=
  exchangeAddress (inflatedPosition S D.tree P.lower.toNode)
    (inflatedPosition S D.tree (S.pair P.retained).toNode) P.keep

/-- A source leaf distinct from the exceptional destination has a whole local
replacement subtree on which the physical address map respects path extension. -/
theorem inflatedExchange_leaf_respectsAt (l : GLeaf S.tree) (hl : l ≠ S.pair P.retained) :
    RespectsAt (inflatedExchange S P D) (inflatedPosition S D.tree l.toNode) := by
  apply exchange_respectsAt_of_away
  · intro h
    have hh := (inflatedPosition_below_iff S D.tree l.toNode P.lower.toNode).mp h
    exact leaf_not_prefix_branch l.2 (hh.1 ▸ P.lower.2) hh.2
  · intro h
    have hh := (inflatedPosition_below_iff S D.tree (S.pair P.retained).toNode l.toNode).mp h
    exact hl (Comb.GLeaf.eq_of_isDesc ⟨hh.1.symm,hh.2⟩).symm
  · intro h
    have hh := (inflatedPosition_below_iff S D.tree l.toNode (S.pair P.retained).toNode).mp h
    exact hl (Comb.GLeaf.eq_of_isDesc ⟨hh.1.symm,hh.2⟩)

/-- The physical image of every ordinary couple endpoint is its actual new root. -/
theorem inflatedPosition_leaf_twist (hnil : D.tree P.lower = .nil) (l : GLeaf S.tree) :
    inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
      (coreLeafEquiv S P l).toNode = inflatedExchange S P D (inflatedPosition S D.tree l.toNode) := by
  apply (inflatedPosition_eq_rawSourcePosition (twistReconstruction S P hS D)
    (coreLeafEquiv S P l).toNode).trans
  have he := rawSourcePosition_exchange S P hS D hnil l.toNode
  change rawSourcePosition (twistReconstruction S P hS D)
    (exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep l.1) =
    exchangeAddress (rawSourcePosition D P.lower.1) (rawSourcePosition D (S.pair P.retained).1)
      P.keep (rawSourcePosition D l.1) at he
  rw [← coreLeafEquiv_address S P l] at he
  apply he.trans
  unfold inflatedExchange
  rw [inflatedPosition_eq_rawSourcePosition D P.lower.toNode,
    inflatedPosition_eq_rawSourcePosition D (S.pair P.retained).toNode,
    inflatedPosition_eq_rawSourcePosition D l.toNode]
  rfl

/-- Branch replacement roots follow the same physical address formula. -/
theorem inflatedPosition_branch_twist (hnil : D.tree P.lower = .nil) (b : GBranch S.tree) :
    inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
      (coreBranchEquiv S P b).toNode = inflatedExchange S P D (inflatedPosition S D.tree b.toNode) := by
  apply (inflatedPosition_eq_rawSourcePosition (twistReconstruction S P hS D)
    (coreBranchEquiv S P b).toNode).trans
  have he := rawSourcePosition_exchange S P hS D hnil b.toNode
  change rawSourcePosition (twistReconstruction S P hS D)
    (exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep b.1) =
    exchangeAddress (rawSourcePosition D P.lower.1) (rawSourcePosition D (S.pair P.retained).1)
      P.keep (rawSourcePosition D b.1) at he
  rw [← coreBranchEquiv_address S P b] at he
  apply he.trans
  unfold inflatedExchange
  rw [inflatedPosition_eq_rawSourcePosition D P.lower.toNode,
    inflatedPosition_eq_rawSourcePosition D (S.pair P.retained).toNode,
    inflatedPosition_eq_rawSourcePosition D b.toNode]
  rfl

end WaveTurbulence.LFTwist
