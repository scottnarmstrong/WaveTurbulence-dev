/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Replacement

/-! # Replacement at incomparable addresses (TARGET L846–L847) -/

public section

namespace WaveTurbulence.Comb
open TTree

/-- Replacing one subtree does not change a subtree at an incomparable address. -/
theorem subtree_replaceAt_disjoint : ∀ (t : TTree) (p q : Path),
    (¬ p <+: q) → (¬ q <+: p) → ∀ s, subtree (replaceAt t p s) q = subtree t q
  | t, [], q, h, _, s => (h List.nil_prefix).elim
  | t, p, [], _, h, s => (h List.nil_prefix).elim
  | .leaf, i :: p, j :: q, h, h', s => by simp [replaceAt, subtree]
  | .node l m r, i :: p, j :: q, h, h', s => by
    fin_cases i <;> fin_cases j <;>
      simp [List.cons_prefix_cons] at h h' <;>
      simp [replaceAt, subtree] <;>
      exact subtree_replaceAt_disjoint _ p q h h' s

end WaveTurbulence.Comb
