/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NEStep

/-! # P4-W2 (a): the exceptional records of an unrolled term and `rowFormNE_termsB`

Every term of `Lvl.termsB` has a native-except row form on its level's region: at the pairs `p₀` and the branches `b` of the operative
levels (the split levels and the bottom level) the weights are the exceptional factors, everywhere else the native rows.  The induction
over the levels (`Lvl.termsB_induction`) builds a list of `ExcRec`s, one per operative level:

* `ExcRec`: the pair `p₀`, the branch `bj` (the lower joint of the piece), the piece index `blk` and the exceptional factor `X` as a function
  of the decoration of the term's own region and the clock.  `ExcOf V r`: `r` comes from an operative member of a level `lv'`
  (`ExcOf` is a `Prop`; the data `lv', pstar, c, f` are recovered by `obtain`): `X x u = XE lv' pstar hk c (rA RS (f x)) u` (or `XB ..
  (f x) u` at the bottom level), where `f` is a composite of the restrictions `rB` and agrees with the identity on the realization nodes of
  `lv'`, which lie in those of `V`.
* `pexOf`, `bexOf`, `xqOf`: the exceptional pairs, branches and weights of a list of records.
* **`rowFormNE_termsB`**: for every term `ψ` of `Lvl.termsB lv` there are a list of records (`p₀`'s and `b`'s distinct, in the pairs and the interior
  branches of `lv`) and a time condition `Dm` (equal to `DomX` with the parent-clock condition dropped at the `b`'s) such that `ψ` has the
  native-except row form with `Pex = pexOf`, `Bex = bexOf`, `Xq = xqOf`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w}

/-- An exceptional record. -/
structure ExcRec (G : Garden w) (d : ℕ) where
  p0 : SourcePair G
  bj : GBranch G.tree
  blk : ℕ
  X : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ

/-- Precompose the exceptional factor with a map of decorations. -/
def ExcRec.comp (r : ExcRec G d) (g : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ))) : ExcRec G d :=
  { r with X := fun x u => r.X (g x) u }

/-- The exceptional pairs of a list of records. -/
def pexOf (recs : List (ExcRec G d)) : Finset (SourcePair G) := by
  classical
  exact (recs.map ExcRec.p0).toFinset

/-- The exceptional branches of a list of records. -/
def bexOf (recs : List (ExcRec G d)) : Finset (GBranch G.tree) := by
  classical
  exact (recs.map ExcRec.bj).toFinset

/-- The exceptional weight at a pair: the product of the factors of the records at that pair. -/
noncomputable def xqOf (recs : List (ExcRec G d)) :
    SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ := by
  classical
  exact fun p _ u x => ((recs.filter fun r => r.p0 = p).map fun r => r.X x u).prod

theorem pexOf_cons (r : ExcRec G d) (recs : List (ExcRec G d)) : pexOf (r :: recs) = insert r.p0 (pexOf recs) := by
  classical
  unfold pexOf
  simp [List.toFinset_cons]

theorem bexOf_cons (r : ExcRec G d) (recs : List (ExcRec G d)) : bexOf (r :: recs) = insert r.bj (bexOf recs) := by
  classical
  unfold bexOf
  simp [List.toFinset_cons]

theorem mem_pexOf {recs : List (ExcRec G d)} {p : SourcePair G} : p ∈ pexOf recs ↔ ∃ r ∈ recs, r.p0 = p := by
  classical
  unfold pexOf
  simp [List.mem_toFinset]

theorem mem_bexOf {recs : List (ExcRec G d)} {v : GBranch G.tree} : v ∈ bexOf recs ↔ ∃ r ∈ recs, r.bj = v := by
  classical
  unfold bexOf
  simp [List.mem_toFinset]

theorem pexOf_nil : pexOf ([] : List (ExcRec G d)) = ∅ := by
  classical
  unfold pexOf
  simp

theorem bexOf_nil : bexOf ([] : List (ExcRec G d)) = ∅ := by
  classical
  unfold bexOf
  simp

theorem xqOf_comp (recs : List (ExcRec G d)) (g : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ)))
    (p : SourcePair G) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) (x : GNode G.tree → (Fin d → ℤ)) :
    xqOf (recs.map fun r => r.comp g) p t u x = xqOf recs p t u (g x) := by
  classical
  unfold xqOf
  simp only [List.filter_map, List.map_map]
  rfl

theorem xqOf_cons_self (r : ExcRec G d) (recs : List (ExcRec G d)) (hr : ∀ r' ∈ recs, r'.p0 ≠ r.p0)
    (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) (x : GNode G.tree → (Fin d → ℤ)) :
    xqOf (r :: recs) r.p0 t u x = r.X x u := by
  classical
  unfold xqOf
  have h : recs.filter (fun r' => r'.p0 = r.p0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r' hr'
    simpa using hr r' hr'
  simp [List.filter_cons, h]

theorem xqOf_cons_ne (r : ExcRec G d) (recs : List (ExcRec G d)) {p : SourcePair G} (hp : p ≠ r.p0)
    (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) (x : GNode G.tree → (Fin d → ℤ)) :
    xqOf (r :: recs) p t u x = xqOf recs p t u x := by
  classical
  unfold xqOf
  simp [List.filter_cons, Ne.symm hp]

theorem pexOf_map_comp (recs : List (ExcRec G d)) (g : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ))) :
    pexOf (recs.map fun r => r.comp g) = pexOf recs := by
  classical
  ext p
  rw [mem_pexOf, mem_pexOf]
  simp [ExcRec.comp]

theorem bexOf_map_comp (recs : List (ExcRec G d)) (g : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ))) :
    bexOf (recs.map fun r => r.comp g) = bexOf recs := by
  classical
  ext p
  rw [mem_bexOf, mem_bexOf]
  simp [ExcRec.comp]

end WaveTurbulence.VineEstS5C.P4.W2
