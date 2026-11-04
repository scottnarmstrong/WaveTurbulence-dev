/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ReplacementLeaves

/-! # Non-lone leaves after collapse (TARGET L846) -/

public section

namespace WaveTurbulence.Comb
open TTree

/-- The new lone leaf created by collapsing a valid subtree. -/
@[expose] def collapsedLone {t u : TTree} {p : Path} (h : subtree t p = some u) :
    GLeaf (fun _ : Fin 1 => collapseAt t p) := ⟨(0, p), mem_leaves_collapseAt h⟩

/-- Every non-lone collapsed leaf corresponds to an old leaf outside the lower subtree. -/
@[expose] def collapsedOtherEquiv {t u : TTree} {p : Path} (h : subtree t p = some u) :
    {ℓ : GLeaf (fun _ : Fin 1 => collapseAt t p) // ℓ ≠ collapsedLone h} ≃
      {q : Path // q ∈ t.leaves ∧ ¬ p <+: q} where
  toFun ℓ := ⟨ℓ.1.1.2, by
    have hn : ℓ.1.1.2 ≠ p := by
      intro he
      apply ℓ.2
      apply Subtype.ext
      exact Prod.ext (Subsingleton.elim _ _) he
    exact ((mem_leaves_collapseAt_iff h).mp ℓ.1.2).resolve_right hn⟩
  invFun q := ⟨⟨(0, q.1), (mem_leaves_collapseAt_iff h).mpr (Or.inl q.2)⟩, by
    intro he
    have hp := congrArg (fun ℓ : GLeaf (fun _ : Fin 1 => collapseAt t p) => ℓ.1.2) he
    change q.1 = p at hp
    apply q.2.2
    rw [hp]⟩
  left_inv ℓ := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv q := by apply Subtype.ext; rfl

end WaveTurbulence.Comb
