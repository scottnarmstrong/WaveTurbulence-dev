/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch

/-! # Exact branching-node set of valid ordered subtree replacement -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Branch addresses outside the removed subtree survive; all inserted branch
addresses are framed by the original replacement root. -/
theorem branching_replaceAt_eq : ∀ {t : TTree} {p : Path} {u : TTree},
    Comb.subtree t p = some u → ∀ s : TTree,
      (Comb.replaceAt t p s).branching =
        (t.branching.filter (fun q => ¬ p <+: q)) ∪ s.branching.image (fun q => p ++ q)
  | t, [], u, h, s => by simp [Comb.replaceAt]
  | .leaf, i :: p, u, h, s => by simp [Comb.subtree] at h
  | .node l m r, i :: p, u, h, s => by
    fin_cases i <;> simp [Comb.subtree] at h
    all_goals
      ext q
      cases q with
      | nil => simp [Comb.replaceAt,TTree.branching,nil_notMem_pre]
      | cons j q =>
        fin_cases j <;>
          simp [Comb.replaceAt,TTree.branching,cons_mem_pre,List.cons_prefix_cons,
            Finset.mem_image,List.cons_append,List.cons.injEq,branching_replaceAt_eq h]

end WaveTurbulence.Reg.Skeleton
