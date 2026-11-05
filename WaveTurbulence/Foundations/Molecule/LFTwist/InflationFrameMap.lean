/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.GenericInflation

/-! # Covariance of the inserted source-path frames -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

/-- Compatible local code transport preserves every frame along a valid source path. -/
theorem inflationFrame_map {w v : ℕ} (X : Address w → RegChain) (X' : Address v → RegChain)
    (f : Address w → Address v) (t : TTree) (a : Address w) (p : Path) (hp : p ∈ t.nodes)
    (hf : RespectsAt f a)
    (hX : ∀ q ∈ t.branching, X' (f (addrExt a q)) = X (addrExt a q)) :
    inflationFrame X' (f a) p = inflationFrame X a p := by
  induction p generalizing t a with
  | nil => rfl
  | cons i p ih =>
    cases t with
    | leaf => simp only [TTree.nodes, Finset.mem_singleton, List.cons_ne_nil] at hp
    | node l m r =>
      have hroot : X' (f a) = X a := by
        simpa only [addrExt_nil] using hX [] (by simp [TTree.branching])
      have hp' : p ∈ (![l,m,r] i).nodes := (cons_mem_nodes_node l m r i p).mp hp
      have hx (q : Path) (hq : q ∈ (![l,m,r] i).branching) :
          X' (f (addrExt (addrExt a [i]) q)) = X (addrExt (addrExt a [i]) q) := by
        have hh := hX (i :: q) ((cons_mem_branching_node l m r i q).mpr hq)
        rw [addrExt_cons a i q] at hh
        exact hh
      have hh := ih (![l,m,r] i) (addrExt a [i]) hp' (hf.child [i]) hx
      change (X' (f a)).lonePath ++ [i] ++ inflationFrame X' (addrExt (f a) [i]) p =
        (X a).lonePath ++ [i] ++ inflationFrame X (addrExt a [i]) p
      rw [hroot]
      exact congrArg (fun q => (X a).lonePath ++ [i] ++ q)
        ((congrArg (fun z => inflationFrame X' z p) (hf [i]).symm).trans hh)

end WaveTurbulence.LFTwist
