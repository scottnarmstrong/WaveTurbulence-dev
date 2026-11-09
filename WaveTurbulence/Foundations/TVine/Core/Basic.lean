/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Defs

/-!
# The T-vine U-layer: undirected multigraphs, blocks, closures, T-vines, pieces

The undirected layer of research note M4 §2.1 over the pinned `TVine.UMultigraph` (ruling D11). Every
combinatorial fact about T-vines (pieces, cuts, rungs, sub-objects) depends only on the undirected
joint-marked multigraph (N3 §3.2), so it is stated here and transported to molecules through the bridge
`groupGraph` (module `Core.Bridge`).

* graph primitives: `deg`, `nbrs`, `cut`, `AdjIn`, `ConnOn`, `Connected`, `induce`, `eraseBond`, `splice`;
* `IsBlockU`, `IsClosureU`, `ReducesToT`, `IsTVineU` (the U-reading of the pinned `IsBlock`, `IsClosure`,
  `IsTVine`);
* `SamePieceU`, `piecesU`, `TwoCutSide` (the U-reading of the pinned `SamePiece`, `pieces`);
* `groupGraph M S`: the undirected multigraph of the atomic group `S` of a molecule.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-! ## Extensionality and support -/

theorem ext {G H : UMultigraph V} (hv : G.verts = H.verts) (hm : ∀ e, G.mult e = H.mult e) : G = H := by
  cases G; cases H; simp only at hv; subst hv; congr; funext e; exact hm e

theorem ext_iff' {G H : UMultigraph V} : G = H ↔ G.verts = H.verts ∧ ∀ e, G.mult e = H.mult e :=
  ⟨fun h => h ▸ ⟨rfl, fun _ => rfl⟩, fun h => ext h.1 h.2⟩

theorem mem_verts_of_mult (G : UMultigraph V) {e : Sym2 V} (h : G.mult e ≠ 0) {x : V} (hx : x ∈ e) :
    x ∈ G.verts := G.supp e h x hx

theorem mult_eq_zero_of_left (G : UMultigraph V) {u : V} (hu : u ∉ G.verts) (w : V) : G.mult s(u, w) = 0 := by
  by_contra h; exact hu (G.supp _ h u (Sym2.mem_mk_left u w))

theorem mult_eq_zero_of_right (G : UMultigraph V) {w : V} (hw : w ∉ G.verts) (u : V) : G.mult s(u, w) = 0 := by
  by_contra h; exact hw (G.supp _ h w (Sym2.mem_mk_right u w))

/-! ## Degrees, neighbours, cuts, connectivity -/

/-- The degree of `v`: the number of bond copies at `v`, a loop counted twice. -/
def deg (G : UMultigraph V) (v : V) : ℕ := ∑ w ∈ G.verts, G.mult s(v, w) + G.mult s(v, v)

/-- The multiset of far endpoints of the bond copies at `v` (a loop contributes `v` twice); the U-reading of
the pinned `Molecule.groupNbrs`. -/
def nbrs (G : UMultigraph V) (v : V) : Multiset V :=
  (∑ w ∈ G.verts, Multiset.replicate (G.mult s(v, w)) w) + Multiset.replicate (G.mult s(v, v)) v

/-- The number of bond copies with exactly one endpoint in `X ⊆ verts` (the size of the edge cut `δ(X)`). -/
def cut (G : UMultigraph V) (X : Finset V) : ℕ := ∑ u ∈ X, ∑ w ∈ G.verts \ X, G.mult s(u, w)

/-- Adjacency inside the atom set `X`. -/
def AdjIn (G : UMultigraph V) (X : Finset V) (a b : V) : Prop := a ∈ X ∧ b ∈ X ∧ G.mult s(a, b) ≠ 0

/-- The multigraph induced on `X` is connected: any two atoms of `X` are joined by a path inside `X`. -/
def ConnOn (G : UMultigraph V) (X : Finset V) : Prop :=
  ∀ u ∈ X, ∀ w ∈ X, Relation.ReflTransGen (AdjIn G X) u w

/-- `G` is connected. -/
def Connected (G : UMultigraph V) : Prop := ConnOn G G.verts

/-! ## Constructions -/

/-- The sub-multigraph induced on `S`: vertex set `S`, all bonds of `G` with both ends in `S`. -/
def induce (G : UMultigraph V) (S : Finset V) : UMultigraph V where
  verts := S
  mult e := if e ∈ S.sym2 then G.mult e else 0
  supp e he x hx := by
    by_cases h : e ∈ S.sym2
    · exact Finset.mem_sym2_iff.mp h x hx
    · simp [h] at he

/-- `G` with one copy of the bond `e` removed (nothing happens if `e` is not a bond). -/
def eraseBond (G : UMultigraph V) (e : Sym2 V) : UMultigraph V where
  verts := G.verts
  mult f := if f = e then G.mult f - 1 else G.mult f
  supp f hf x hx := by
    by_cases h : f = e
    · simp only [h, if_true] at hf; exact G.supp e (by omega) x (h ▸ hx)
    · simp only [h, if_false] at hf; exact G.supp f hf x hx

/-- **Splicing**: delete the atoms `a, b` with all their bonds, and add the bonds `adds` (those of them that
avoid `a, b`). The (Y2) move (`y2Move`) and rung deletion (`rungDel`) are splices. -/
def splice (G : UMultigraph V) (a b : V) (adds : Multiset (Sym2 V)) : UMultigraph V where
  verts := ((G.verts ∪ adds.toFinset.biUnion Sym2.toFinset).erase a).erase b
  mult e := if a ∈ e ∨ b ∈ e then 0 else G.mult e + adds.count e
  supp e he x hx := by
    by_cases h : a ∈ e ∨ b ∈ e
    · simp [h] at he
    · simp only [h, if_false] at he
      have hxa : x ≠ a := fun hh => h (Or.inl (hh ▸ hx))
      have hxb : x ≠ b := fun hh => h (Or.inr (hh ▸ hx))
      simp only [Finset.mem_erase, hxa, hxb, ne_eq, not_false_eq_true, true_and, Finset.mem_union,
        Finset.mem_biUnion, Multiset.mem_toFinset, Sym2.mem_toFinset]
      by_cases hG : G.mult e = 0
      · exact Or.inr ⟨e, Multiset.count_ne_zero.mp (by omega), hx⟩
      · exact Or.inl (G.supp e hG x hx)

theorem splice_mult (G : UMultigraph V) (a b : V) (adds : Multiset (Sym2 V)) (e : Sym2 V) :
    (splice G a b adds).mult e = if a ∈ e ∨ b ∈ e then 0 else G.mult e + adds.count e := rfl

theorem splice_verts_of_subset (G : UMultigraph V) (a b : V) {adds : Multiset (Sym2 V)}
    (h : ∀ e ∈ adds, ∀ x ∈ e, x ∈ G.verts) : (splice G a b adds).verts = (G.verts.erase a).erase b := by
  have : adds.toFinset.biUnion Sym2.toFinset ⊆ G.verts := by
    intro x hx
    simp only [Finset.mem_biUnion, Multiset.mem_toFinset, Sym2.mem_toFinset] at hx
    obtain ⟨e, he, hx⟩ := hx
    exact h e he x hx
  show ((G.verts ∪ adds.toFinset.biUnion Sym2.toFinset).erase a).erase b = _
  rw [Finset.union_eq_left.mpr this]

/-! ## Blocks, closures, T-vines (the U-reading of the pinned definitions) -/

/-- The interior `verts ∖ {j₁, j₂}`. -/
def interior (G : UMultigraph V) (j₁ j₂ : V) : Finset V := (G.verts.erase j₁).erase j₂

/-- **Block with joints `j₁ ≠ j₂`** (U-reading of `Molecule.IsBlock`): the joints have degree 2, every other
atom degree 4, and `G` is connected. -/
def IsBlockU (G : UMultigraph V) (j₁ j₂ : V) : Prop :=
  j₁ ∈ G.verts ∧ j₂ ∈ G.verts ∧ j₁ ≠ j₂ ∧ deg G j₁ = 2 ∧ deg G j₂ = 2 ∧
    (∀ v ∈ G.verts, v ≠ j₁ → v ≠ j₂ → deg G v = 4) ∧ Connected G

/-- **The closure** `cl(G; j₁, j₂)` as a relation: the pinned `Molecule.IsClosure` read in `G` (with
`σ = G.mult s(j₁, j₂)`, the bonds of `S` replaced by those of `G`, `groupNbrs` by `nbrs`). -/
def IsClosureU (G : UMultigraph V) (j₁ j₂ : V) (C : UMultigraph V) : Prop :=
  G.mult s(j₁, j₂) < 2 ∧ C.verts = (G.verts.erase j₁).erase j₂ ∧ C.Loopless ∧
    ∃ added : Multiset (Sym2 V),
      ((G.mult s(j₁, j₂) = 0 ∧ ∃ a b c d : V, nbrs G j₁ = {a, b} ∧ nbrs G j₂ = {c, d} ∧
          added = {s(a, b), s(c, d)}) ∨
       (G.mult s(j₁, j₂) = 1 ∧ ∃ x y : V, nbrs G j₁ = {j₂, x} ∧ nbrs G j₂ = {j₁, y} ∧
          added = {s(x, y)})) ∧
      ∀ e, C.mult e = (if j₁ ∈ e ∨ j₂ ∈ e then 0 else G.mult e) + added.count e

/-- `C` reduces by (Y2) moves to the doubled triangle `T` (`C →* T`). -/
def ReducesToT (C : UMultigraph V) : Prop :=
  ∃ C' : UMultigraph V, Relation.ReflTransGen Y2Step C C' ∧ IsDoubledTriangle C'

/-- **T-vine** (U-reading of the pinned `Molecule.IsTVine`; M4 §2.1 `IsTVineU`). -/
def IsTVineU (G : UMultigraph V) (j₁ j₂ : V) : Prop :=
  IsBlockU G j₁ j₂ ∧ (∀ u ∈ G.verts, ∀ v ∈ G.verts, u ≠ v → G.mult s(u, v) ≤ 2) ∧
    ∃ C : UMultigraph V, IsClosureU G j₁ j₂ C ∧ ReducesToT C

/-! ## Two-edge cuts and pieces -/

/-- `X` is a **2-cut side**: a nonempty proper atom set with exactly two bond copies leaving it (M4 §2.1). -/
def TwoCutSide (G : UMultigraph V) (X : Finset V) : Prop :=
  X ⊆ G.verts ∧ X.Nonempty ∧ X ≠ G.verts ∧ cut G X = 2

/-- **Same piece** (U-reading of the pinned `Molecule.SamePiece`): no atom set with at most two bond copies
leaving it separates `u` and `w`. An equivalence relation by definition. On a block (all degrees even,
connected) only 2-cut sides matter (`samePieceU_iff_twoCutSide`, module `Core.Cuts`). -/
def SamePieceU (G : UMultigraph V) (u w : V) : Prop :=
  ∀ X ⊆ G.verts, cut G X ≤ 2 → (u ∈ X ↔ w ∈ X)

/-- **The pieces** with joints `j₁, j₂` (U-reading of the pinned `Molecule.pieces`): the `SamePieceU`-classes
of the interior. -/
noncomputable def piecesU (G : UMultigraph V) (j₁ j₂ : V) : Finset (Finset V) := by
  classical
  exact (interior G j₁ j₂).image fun u => (interior G j₁ j₂).filter fun w => SamePieceU G u w

theorem samePieceU_refl (G : UMultigraph V) (u : V) : SamePieceU G u u := fun _ _ _ => Iff.rfl

theorem samePieceU_symm {G : UMultigraph V} {u w : V} (h : SamePieceU G u w) : SamePieceU G w u :=
  fun X hX hc => (h X hX hc).symm

theorem samePieceU_trans {G : UMultigraph V} {u v w : V} (h₁ : SamePieceU G u v) (h₂ : SamePieceU G v w) :
    SamePieceU G u w := fun X hX hc => (h₁ X hX hc).trans (h₂ X hX hc)

/-! ## The undirected multigraph of an atomic group -/

section Group

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **The undirected multigraph of the atomic group `S`** of a molecule: vertex set `S`, multiplicity of `e` the
number of bonds of `S` with ends `e` (`Molecule.groupBonds`). -/
def groupGraph (M : Molecule V D) (S : Finset V) : UMultigraph V where
  verts := S
  mult e := (M.groupBonds S).count e
  supp e he x hx := by
    have hm := Multiset.count_ne_zero.mp he
    simp only [Molecule.groupBonds, Multiset.mem_map, Finset.mem_val, Finset.mem_filter,
      Finset.mem_univ, true_and] at hm
    obtain ⟨y, ⟨_, hy₁, hy₂⟩, rfl⟩ := hm
    simp only [Molecule.ends, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact hy₁
    · exact hy₂

theorem groupGraph_verts (M : Molecule V D) (S : Finset V) : (groupGraph M S).verts = S := rfl

theorem groupGraph_mult (M : Molecule V D) (S : Finset V) (e : Sym2 V) :
    (groupGraph M S).mult e = (M.groupBonds S).count e := rfl

end Group

end WaveTurbulence.TVine.Core
