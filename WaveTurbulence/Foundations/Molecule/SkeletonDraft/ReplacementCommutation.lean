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

/-- Two replacements at incomparable actual forest roots commute exactly. -/
theorem replaceNodeForest_commute {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) (s r : TTree) :
    Function.update (Comb.replaceNodeForest tree a s) b.1.1
      (Comb.replaceAt (Comb.replaceNodeForest tree a s b.1.1) b.1.2 r) =
    Function.update (Comb.replaceNodeForest tree b r) a.1.1
      (Comb.replaceAt (Comb.replaceNodeForest tree b r a.1.1) a.1.2 s) := by
  funext j
  by_cases hi : a.1.1 = b.1.1
  · have hp : ¬ a.1.2 <+: b.1.2 := fun h => hab.1 ⟨hi,h⟩
    have hq : ¬ b.1.2 <+: a.1.2 := fun h => hab.2 ⟨hi.symm,h⟩
    by_cases hj : j = b.1.1
    · subst j
      simp only [Comb.replaceNodeForest,hi,Function.update_self]
      exact replaceAt_commute _ _ _ hp hq s r
    · have hja : j ≠ a.1.1 := by simpa only [hi] using hj
      simp only [Comb.replaceNodeForest,Function.update_of_ne hj,Function.update_of_ne hja]
  · by_cases hj : j = a.1.1
    · subst j
      simp only [Comb.replaceNodeForest,Function.update_self,Function.update_of_ne hi]
    · by_cases hk : j = b.1.1
      · subst j
        simp only [Comb.replaceNodeForest,Function.update_self,Function.update_of_ne (Ne.symm hi)]
      · simp only [Comb.replaceNodeForest,Function.update_of_ne hj,Function.update_of_ne hk]

end WaveTurbulence.Reg.Skeleton
