/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.VineLike

/-!
# The remaining L1 statements, U-level (exact statements; proofs in later modules)

Each `…Statement : Prop` is the U-level reading of a refereed statement (N2 = research-gamma-half-2 NOTES with
REF2; N3 = research-gamma-half-3 NOTES with REF3; M4 = research-m4 NOTES §2.2 with REF-M4). L1 proves each as a
theorem `…_holds : …Statement`; until then other packets may take a statement as a hypothesis.

Setting conventions (N2 §1.1): molecules are loopless, so every statement assumes `G.Loopless`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

/-- `Φ(U)` (N2 Lemma 1.14(b)): `U` with the rung atoms removed, same joints and kind. -/
def SubObj.phi {V : Type u} [DecidableEq V] (U : SubObj V) (a b : V) : SubObj V :=
  ⟨(U.atoms.erase a).erase b, U.k₁, U.k₂, U.hyper⟩

/-- **N2 Lemma 1.9(1)** (deletion; path-wise, M4 Lemma 5′): deleting a deletable rung of a T-vine, with either
matching, gives a T-vine. (Same binders as L3's `DeleteRungInput`.) Proved: `isTVineU_rungDel` (`Core.Lemma19Del`). -/
def DeleteRungStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V),
    IsTVineU G j₁ j₂ → IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp → ∀ μ : Bool,
      IsTVineU (rungDel G a b xm xp ym yp μ) j₁ j₂

/-- **N2 Lemma 1.9(2)** (insertion; applied undirected, REF2): inserting a rung at a 2-edge-cut `δ(X)` of a T-vine,
both sides of which contain an interior atom, gives a T-vine in which the new rung is deletable, and the crossed
deletion undoes the insertion. The crossing bond copies are `p–q` and `p'–q'` (`p, p' ∈ X`). -/
def RungInsertionStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V) (X : Finset V) (p q p' q' u v : V),
    IsTVineU G j₁ j₂ → X ⊆ G.verts → cut G X = 2 → p ∈ X → p' ∈ X → q ∈ G.verts \ X → q' ∈ G.verts \ X →
    G.mult s(p, q) ≠ 0 → G.mult s(p', q') ≠ 0 → (s(p, q) = s(p', q') → G.mult s(p, q) = 2) →
    (∃ i ∈ X, i ≠ j₁ ∧ i ≠ j₂) → (∃ i ∈ G.verts \ X, i ≠ j₁ ∧ i ≠ j₂) →
    u ∉ G.verts → v ∉ G.verts → u ≠ v →
    IsTVineU (insertRung G p q p' q' u v) j₁ j₂ ∧
      IsDeletableAt (insertRung G p q p' q' u v) j₁ j₂ u v p q p' q' X (G.verts \ X) ∧
      rungDel (insertRung G p q p' q' u v) u v p q p' q' false = G

/-- **N2 Lemma 1.10** (parity). For a sub-object `U` and an atom set `X`, the number of bonds of `E(U)` crossing `X`
is even if `U` is of block type, and odd iff exactly one joint of `U` lies in `X` if `U` is of hyper type. -/
def ParityStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (U : SubObj V) (X : Finset V),
    IsSubObjU G U →
      (U.hyper = false → Even (cut (U.edges G) (X ∩ U.atoms))) ∧
      (U.hyper = true → (Odd (cut (U.edges G) (X ∩ U.atoms)) ↔ (U.k₁ ∈ X ↔ U.k₂ ∉ X)))

/-- **N2 Lemma 1.11** (joints in rungs). If a sub-object `U` of a block has a joint in a 2-cut rung `R = {a, b}`,
then `U` is the double bond `a = b` (block type), or the side hyper-block `K ∪ R` with adjoint `a = b` for a side
`K` of `R` containing no joint of the block. In both cases the joints of `U` are `a, b`. -/
def JointsInRungsStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V)
    (U : SubObj V),
    IsBlockU G j₁ j₂ → G.Loopless → IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp → IsSubObjU G U →
    (U.k₁ = a ∨ U.k₁ = b ∨ U.k₂ = a ∨ U.k₂ = b) →
    s(U.k₁, U.k₂) = s(a, b) ∧
      ((U.hyper = false ∧ U.atoms = {a, b}) ∨
       (U.hyper = true ∧ ((U.atoms = insert a (insert b Km) ∧ j₁ ∉ Km ∧ j₂ ∉ Km) ∨
                          (U.atoms = insert a (insert b Kp) ∧ j₁ ∉ Kp ∧ j₂ ∉ Kp))))

/-- **N2 Lemma 1.12** (container joints). In a block whose interior is connected and which has no interior cut
atom, no (proper) sub-object contains a joint of the block. -/
def ContainerJointsStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V) (U : SubObj V),
    IsBlockU G j₁ j₂ → G.Loopless → ConnOn G (interior G j₁ j₂) →
    (∀ w ∈ interior G j₁ j₂, ConnOn G (G.verts.erase w)) → IsSubObjU G U →
    j₁ ∉ U.atoms ∧ j₂ ∉ U.atoms

/-- **N2 Lemma 1.14(a)** (all-in or all-out). For a 2-cut rung `R` and a sub-object `U` with no joint in `R`: either
`R ⊆ I(U)` and all four rails are bonds of `U`, or `S(U) ∩ R = ∅`. -/
def PhiAllInOutStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V)
    (U : SubObj V),
    IsBlockU G j₁ j₂ → G.Loopless → IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp → IsSubObjU G U →
    U.k₁ ≠ a → U.k₁ ≠ b → U.k₂ ≠ a → U.k₂ ≠ b →
    (a ∈ U.inner ∧ b ∈ U.inner ∧ xm ∈ U.atoms ∧ xp ∈ U.atoms ∧ ym ∈ U.atoms ∧ yp ∈ U.atoms) ∨
      (a ∉ U.atoms ∧ b ∉ U.atoms)

/-- **N2 Lemma 1.14(b)** (the image `Φ(U)`): `Φ(U)` is a sub-object of `G/[μ]R` of the same kind. -/
def PhiSubObjStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V)
    (U : SubObj V) (μ : Bool),
    IsBlockU G j₁ j₂ → G.Loopless → IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp → IsSubObjU G U →
    U.k₁ ≠ a → U.k₁ ≠ b → U.k₂ ≠ a → U.k₂ ≠ b →
    IsSubObjU (rungDel G a b xm xp ym yp μ) (U.phi a b)

/-- **N2 Lemma 1.14(c′)** (N3 §2.1, REF2 R1): for a non-cap 2-cut rung `R` and an all-in vine-like `U` (no joint in
`R`) with ingredient kinds `ks`: either `Φ(U)` is vine-like with the same kinds, or some ingredient is (II) (the
4-atom Q-block), `Φ(U)` is vine-like with that ingredient replaced by (I), and the gap of `Φ(U)` is constant (its two
bonds at `k₁` are a 2-edge-cut of `G/[μ]R`). -/
def PhiTypeStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V)
    (U : SubObj V) (ks : List EnlKind) (μ : Bool),
    IsBlockU G j₁ j₂ → G.Loopless → IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp → IsVineLikeU G U ks →
    U.k₁ ≠ a → U.k₁ ≠ b → U.k₂ ≠ a → U.k₂ ≠ b → a ∈ U.atoms →
    IsVineLikeU (rungDel G a b xm xp ym yp μ) (U.phi a b) ks ∨
      ∃ i : Fin ks.length, ks.get i = .II ∧
        IsVineLikeU (rungDel G a b xm xp ym yp μ) (U.phi a b) (ks.set i .I) ∧
        GapCutAt (rungDel G a b xm xp ym yp μ) (U.phi a b) U.k₁

/-- **N2 Lemma 1.14(d)** (gap): if `Φ(U)` is gap free in `G/[μ]R`, then `U` is gap free in `G`. -/
def PhiGapStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V)
    (U : SubObj V) (μ : Bool),
    IsBlockU G j₁ j₂ → G.Loopless → IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp → IsSubObjU G U →
    U.k₁ ≠ a → U.k₁ ≠ b → U.k₂ ≠ a → U.k₂ ≠ b →
    GapFree (rungDel G a b xm xp ym yp μ) (U.phi a b) → GapFree G U

/-- **N2 Lemma 1.14(e)** (removal connectivity, sources' removal semantics): for pairwise atom-disjoint sub-objects
`U_i` with no joint in `R`, if `(G/[μ]R) ∖ ⋃ Φ(U_i)` is connected then so is `G ∖ ⋃ U_i`. -/
def PhiRemovalStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V)
    (Us : List (SubObj V)) (μ : Bool),
    IsBlockU G j₁ j₂ → G.Loopless → IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp →
    (∀ U ∈ Us, IsSubObjU G U ∧ U.k₁ ≠ a ∧ U.k₁ ≠ b ∧ U.k₂ ≠ a ∧ U.k₂ ≠ b) →
    Us.Pairwise (fun U W => Disjoint U.atoms W.atoms) →
    Connected (removeAll (rungDel G a b xm xp ym yp μ) (Us.map fun U => U.phi a b)) →
    Connected (removeAll G Us)

/-- **N3 Lemma 6.2** (= N2 Lemma 1.6 for T-vines; pendant poles): a T-vine has no two disjoint nonempty sets of
interior atoms each joined to the rest by exactly two bond copies. -/
def PendantPolesStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V) (K₁ K₂ : Finset V),
    IsTVineU G j₁ j₂ → K₁ ⊆ interior G j₁ j₂ → K₂ ⊆ interior G j₁ j₂ → Disjoint K₁ K₂ →
    K₁.Nonempty → K₂.Nonempty → cut G K₁ = 2 → cut G K₂ = 2 → False

/-- **N3 Lemma 4.1** (the cut-atom clause is redundant): a T-vine has no interior cut atom. -/
def NoCutVertexStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V),
    IsTVineU G j₁ j₂ → ∀ w ∈ interior G j₁ j₂, ConnOn G (G.verts.erase w)

end WaveTurbulence.TVine.Core
