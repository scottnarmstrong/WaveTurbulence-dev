/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CrownLookup
public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationPositions
public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationFrameMap

/-! # Exact inflation-frame covariance inside the moved crown -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

/-- Inside a proper child subtree the entire inserted frame is unchanged. -/
theorem crown_child_frame_twist (i : Fin 3) (q : Path)
    (hq : i :: q ∈ (lowerCrown S P.lower).nodes) :
    inflationFrame (branchLookup (twistReconstruction S P hS D))
      (addrExt (S.pair P.retained).1 [freeSwap P.keep i]) q =
    inflationFrame (branchLookup D) (addrExt P.lower.1 [i]) q := by
  let f := exchangeAddress P.lower.1 (S.pair P.retained).1 P.keep
  cases ht : lowerCrown S P.lower with
  | leaf => simp only [ht, TTree.nodes, Finset.mem_singleton, List.cons_ne_nil] at hq
  | node l m r =>
    have hp : q ∈ (![l,m,r] i).nodes := (cons_mem_nodes_node l m r i q).mp (ht ▸ hq)
    have hx (r' : Path) (hr : r' ∈ (![l,m,r] i).branching) :
        branchLookup (twistReconstruction S P hS D) (f (addrExt (addrExt P.lower.1 [i]) r')) =
          branchLookup D (addrExt (addrExt P.lower.1 [i]) r') := by
      have hc : i :: r' ∈ (lowerCrown S P.lower).branching := by
        rw [ht]
        exact (cons_mem_branching_node l m r i r').mpr hr
      have he := branchLookup_exchange S P hS D
        ⟨addrExt P.lower.1 (i :: r'),crown_branch_mem S P (i :: r') hc⟩
      change branchLookup (twistReconstruction S P hS D) (f (addrExt P.lower.1 (i :: r'))) =
        branchLookup D (addrExt P.lower.1 (i :: r')) at he
      rw [addrExt_cons P.lower.1 i r'] at he
      exact he
    have he := inflationFrame_map (branchLookup D) (branchLookup (twistReconstruction S P hS D))
      f (![l,m,r] i) (addrExt P.lower.1 [i]) q hp
      (exchange_respectsAt_lower_child P.lower.1 (S.pair P.retained).1 P.keep i) hx
    exact (congrArg (fun a => inflationFrame (branchLookup (twistReconstruction S P hS D)) a q)
      (exchange_lower_child_root P.lower.1 (S.pair P.retained).1 P.keep i).symm).trans he

/-- Nil at the lower root makes the physical free-child switch exactly the
source free-child switch, including every inserted ordinary chain frame. -/
theorem crown_frame_twist (hnil : D.tree P.lower = .nil) (q : Path)
    (hq : q ∈ (lowerCrown S P.lower).nodes) :
    inflationFrame (branchLookup (twistReconstruction S P hS D)) (S.pair P.retained).1
      (switchPath P.keep q) =
    switchPath P.keep (inflationFrame (branchLookup D) P.lower.1 q) := by
  have hold : branchLookup D P.lower.1 = .nil := (branchLookup_branch D P.lower).trans hnil
  have hnew : branchLookup (twistReconstruction S P hS D) (S.pair P.retained).1 = .nil :=
    (congrArg (branchLookup (twistReconstruction S P hS D)) (coreBranchEquiv_lower_val S P).symm).trans
      ((branchLookup_twist S P hS D P.lower).trans hnil)
  cases q with
  | nil => rfl
  | cons i q =>
    simp only [switchPath, inflationFrame, hold, hnew, RegChain.lonePath, List.nil_append,
      List.singleton_append]
    exact congrArg (List.cons (freeSwap P.keep i)) (crown_child_frame_twist S P hS D i q hq)

/-- Frame concatenation gives literal inflation positions below any raw source prefix. -/
theorem rawSourcePosition_append (a : Address w) (q : Path) :
    rawSourcePosition D (addrExt a q) =
      addrExt (rawSourcePosition D a) (inflationFrame (branchLookup D) a q) := by
  change addrExt (a.1,[]) (inflationFrame (branchLookup D) (a.1,[]) (a.2 ++ q)) = _
  rw [inflationFrame_append]
  have ha : addrExt (a.1,[]) a.2 = a := Prod.ext rfl (List.nil_append _)
  rw [ha]
  exact (addrExt_append _ _ _).symm

end WaveTurbulence.LFTwist
