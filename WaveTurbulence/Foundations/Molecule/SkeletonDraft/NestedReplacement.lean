/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainIdentity

/-! # Exact nested tree replacement and total subtree extraction below a valid frame -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem replaceAt_descendant {t t₀ : TTree} {p : Path} (h : Comb.subtree t p = some t₀)
    (u v : TTree) (q : Path) :
    Comb.replaceAt (Comb.replaceAt t p u) (p ++ q) v =
      Comb.replaceAt t p (Comb.replaceAt u q v) := by
  induction p generalizing t with
  | nil => simp [Comb.replaceAt]
  | cons i p ih =>
    cases t with
    | leaf => simp [Comb.subtree] at h
    | node l m r =>
      fin_cases i <;> simp [Comb.subtree] at h <;> simp [Comb.replaceAt,ih h]

theorem subtreeAt_replaceAt_descendant {t t₀ : TTree} {p : Path}
    (h : Comb.subtree t p = some t₀) (u : TTree) (q : Path) :
    (Comb.replaceAt t p u).subtreeAt (p ++ q) = u.subtreeAt q := by
  induction p generalizing t with
  | nil => simp [Comb.replaceAt]
  | cons i p ih =>
    cases t with
    | leaf => simp [Comb.subtree] at h
    | node l m r =>
      fin_cases i <;> simp [Comb.subtree] at h <;> simp [Comb.replaceAt,TTree.subtreeAt,ih h]

end WaveTurbulence.Reg.Skeleton
