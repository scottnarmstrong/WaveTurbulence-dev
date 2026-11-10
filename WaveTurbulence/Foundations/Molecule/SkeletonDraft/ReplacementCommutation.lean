/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseCoupleGarden

/-! # Commutation of literal subtree replacements at incomparable roots -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Incomparable positions commute under replacement, including invalid positions. -/
theorem replaceAt_commute : ∀ (t : TTree) (p q : Path),
    (¬ p <+: q) → (¬ q <+: p) → ∀ s r,
    Comb.replaceAt (Comb.replaceAt t p s) q r = Comb.replaceAt (Comb.replaceAt t q r) p s
  | t, [], q, h, _, s, r => (h List.nil_prefix).elim
  | t, p, [], _, h, s, r => (h List.nil_prefix).elim
  | .leaf, i :: p, j :: q, h, h', s, r => by simp [Comb.replaceAt]
  | .node l m n, i :: p, j :: q, h, h', s, r => by
    fin_cases i <;> fin_cases j <;>
      simp [List.cons_prefix_cons] at h h' <;>
      simp [Comb.replaceAt] <;>
      exact replaceAt_commute _ p q h h' s r

end WaveTurbulence.Reg.Skeleton
