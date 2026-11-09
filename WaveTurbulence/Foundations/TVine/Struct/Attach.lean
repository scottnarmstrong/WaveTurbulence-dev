/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.MBridge
import Mathlib.Tactic

/-!
# M4 Lemma A (attachment) (packet L3)

M4 §2.2 L253–L266 (CONFIRMED by REF-M4 claim 3): for a non-joint piece `P` of a T-vine and a cycle `C` of `Γ` through
`P`, the two `C`-edges at `P` are incident to two distinct atoms of `P`. The two `C`-edges form a 2-edge-cut, so the
statement follows from its atom form: **no interior atom carries two bond copies of a 2-edge-cut** (`attachU`,
`attachU_compl`). M4's proof: if both are at `w ∈ X`, then `X ∖ {w}` has cut `≤ 2` and separates `w` from the other
atoms of its piece; pieces of T-vines have at least two atoms (N2 Prop 1.17(b)).

* `attachU`, `attachU_compl` (U level, from "every piece has `≥ 2` atoms");
* `attach_of_pieceShape : PieceShapeStatement → AttachStatement` (molecule level).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

section U

variable {V : Type*} [DecidableEq V] {G : UMultigraph V}

theorem eW_singleton_left (w : V) (Z : Finset V) : eW (wG G) {w} Z = ∑ v ∈ Z, G.mult s(w, v) := by
  unfold eW; rw [Finset.sum_singleton]; rfl

/-- The degree of `w ∈ X` splits into the bonds to `X ∖ {w}` and to `verts ∖ X`. -/
theorem deg_split (hC : CutCtx G) {X : Finset V} (hX : X ⊆ G.verts) {w : V} (hwX : w ∈ X) :
    eW (wG G) {w} (X.erase w) + eW (wG G) {w} (G.verts \ X) = deg G w := by
  rw [← degW_eq_deg hC.loopless, eW_singleton_left, eW_singleton_left]
  unfold degW
  rw [← Finset.sum_sdiff hX]
  rw [← Finset.sum_erase_add X _ hwX]
  have := hC.loopless w
  simp only [wG] at this ⊢
  rw [this, add_zero, add_comm]

/-- **Lemma A, atom form (side of the atom).** In a cut context where the interior atoms have degree 4 and every piece
has at least two atoms, an interior atom `w ∈ X` of a 2-edge-cut side `X` carries at most one bond copy of `δ(X)`. -/
theorem attachU (hC : CutCtx G) {j₁ j₂ : V} (hdeg4 : ∀ v ∈ Core.interior G j₁ j₂, deg G v = 4)
    (hbig : ∀ P ∈ piecesU G j₁ j₂, 2 ≤ P.card) {X : Finset V} (hX : X ⊆ G.verts) (h2 : cut G X = 2) {w : V}
    (hw : w ∈ Core.interior G j₁ j₂) (hwX : w ∈ X) : eW (wG G) {w} (G.verts \ X) ≤ 1 := by
  classical
  by_contra hlt
  have hwV : w ∈ G.verts := interior_subset_verts j₁ j₂ hw
  have hYV : X.erase w ⊆ G.verts := (Finset.erase_subset _ _).trans hX
  have hdisj : Disjoint ({w} : Finset V) (X.erase w) := by
    rw [Finset.disjoint_singleton_left]; exact Finset.notMem_erase w X
  have hunion : {w} ∪ X.erase w = X := by
    rw [← Finset.insert_eq, Finset.insert_erase hwX]
  have hcu := cut_union_disjoint (G := G) (Finset.singleton_subset_iff.mpr hwV) hYV hdisj
  rw [hunion, h2, cut_singleton hC hwV, hdeg4 w hw] at hcu
  have hsplit := deg_split hC hX hwX
  rw [hdeg4 w hw] at hsplit
  have hcutY : cut G (X.erase w) ≤ 2 := by omega
  -- the piece of `w`
  set P := (Core.interior G j₁ j₂).filter fun v => SamePieceU G w v with hPdef
  have hP : P ∈ piecesU G j₁ j₂ := by
    rw [mem_piecesU_iff]; exact ⟨w, hw, fun v => by rw [hPdef, Finset.mem_filter]⟩
  have hPc : 1 < P.card := by have := hbig P hP; omega
  obtain ⟨w', hw'P, hw'w⟩ := Finset.exists_mem_ne hPc w
  have hs : SamePieceU G w w' := (Finset.mem_filter.mp hw'P).2
  have h1 : w' ∈ X := (hs X hX h2.le).mp hwX
  have h2' : w' ∉ X.erase w := fun h => (Finset.notMem_erase w X) ((hs (X.erase w) hYV hcutY).mpr h)
  exact h2' (Finset.mem_erase.mpr ⟨hw'w, h1⟩)

/-- **Lemma A, atom form (other side).** -/
theorem attachU_compl (hC : CutCtx G) {j₁ j₂ : V} (hdeg4 : ∀ v ∈ Core.interior G j₁ j₂, deg G v = 4)
    (hbig : ∀ P ∈ piecesU G j₁ j₂, 2 ≤ P.card) {X : Finset V} (hX : X ⊆ G.verts) (h2 : cut G X = 2) {w : V}
    (hw : w ∈ Core.interior G j₁ j₂) (hwX : w ∉ X) : eW (wG G) {w} X ≤ 1 := by
  have hwV : w ∈ G.verts := interior_subset_verts j₁ j₂ hw
  have h := attachU hC hdeg4 hbig (X := G.verts \ X) Finset.sdiff_subset (by rw [cut_compl hX]; exact h2) hw
    (Finset.mem_sdiff.mpr ⟨hwV, hwX⟩)
  rwa [Finset.sdiff_sdiff_eq_self hX] at h

end U

section M

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The pieces of a T-vine with the piece shape have at least two atoms. -/
theorem card_pieces_ge_two {M : Molecule V D} {S : Finset V} {j₁ j₂ : V}
    (hPS : ∃ core ∈ M.pieces S j₁ j₂, CoreShape M core ∧ (∀ P ∈ M.pieces S j₁ j₂, P ≠ core → TwoAtomPiece M P) ∧
      S.card = 2 * ((M.pieces S j₁ j₂).card - 1) + 5) :
    ∀ P ∈ piecesU (groupGraph M S) j₁ j₂, 2 ≤ P.card := by
  obtain ⟨core, -, ⟨x, y, z, hxy, hyz, hxz, rfl, -⟩, hrest, -⟩ := hPS
  intro P hP
  rw [← pieces_eq] at hP
  by_cases hc : P = {x, y, z}
  · rw [hc, Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩]; omega
  · obtain ⟨a, b, hab, rfl, -⟩ := hrest P hP hc
    rw [Finset.card_pair hab]

/-- A crossing bond at `w ∈ X` is a bond from `{w}` to `S ∖ X`. -/
private theorem cross_mem {M : Molecule V D} {S X : Finset V} {x : D} (hx : CrossesIn M S X x) {w : V}
    (hwx : w ∈ M.ends x) (hwX : w ∈ X) :
    (M.atom x ∈ ({w} : Finset V) ∧ M.atom (M.mate x) ∈ S \ X) ∨
      (M.atom x ∈ S \ X ∧ M.atom (M.mate x) ∈ ({w} : Finset V)) := by
  obtain ⟨⟨h1, h2⟩, hc⟩ := hx
  simp only [Molecule.ends, Sym2.mem_iff] at hwx
  rcases hwx with rfl | rfl
  · exact Or.inl ⟨Finset.mem_singleton_self _, Finset.mem_sdiff.mpr ⟨h2, hc.mp hwX⟩⟩
  · refine Or.inr ⟨Finset.mem_sdiff.mpr ⟨h1, fun h => (hc.mp h) hwX⟩, Finset.mem_singleton_self _⟩

private theorem cross_mem' {M : Molecule V D} {S X : Finset V} {x : D} (hx : CrossesIn M S X x) {w : V}
    (hwx : w ∈ M.ends x) (hwX : w ∉ X) :
    (M.atom x ∈ ({w} : Finset V) ∧ M.atom (M.mate x) ∈ X) ∨
      (M.atom x ∈ X ∧ M.atom (M.mate x) ∈ ({w} : Finset V)) := by
  obtain ⟨⟨h1, h2⟩, hc⟩ := hx
  simp only [Molecule.ends, Sym2.mem_iff] at hwx
  rcases hwx with rfl | rfl
  · refine Or.inl ⟨Finset.mem_singleton_self _, ?_⟩
    by_contra h; exact hwX (hc.mpr h)
  · refine Or.inr ⟨?_, Finset.mem_singleton_self _⟩
    by_contra h; exact hwX ((not_not.mp (mt hc.mpr h)))

/-- **M4 Lemma A** (molecule level, atom form), from the piece-shape theorem. -/
theorem attach_of_pieceShape (hPS : PieceShapeStatement.{u, v}) : AttachStatement.{u, v} := by
  intro V D _ _ _ M S j₁ j₂ hT X hX e he f hf hef hce hcf honly w hw₁ hw₂ ⟨hwe, hwf⟩
  obtain ⟨hB, hTU⟩ := (isTVine_iff M).mp hT
  have hC := cutCtx_of_isTVineU hTU
  have hdeg4 : ∀ v ∈ Core.interior (groupGraph M S) j₁ j₂, deg (groupGraph M S) v = 4 := fun v hv => by
    rw [mem_interior] at hv; exact hTU.1.2.2.2.2.2.1 v hv.1 hv.2.1 hv.2.2
  have hbig := card_pieces_ge_two (hPS M S j₁ j₂ hT)
  have h2 : cut (groupGraph M S) X = 2 := cut_eq_two_of_pair M hX he hf hef hce hcf honly
  have hwS : w ∈ S := by
    obtain ⟨⟨h1, h2⟩, -⟩ := hce
    simp only [Molecule.ends, Sym2.mem_iff] at hwe
    rcases hwe with rfl | rfl <;> assumption
  have hwI : w ∈ Core.interior (groupGraph M S) j₁ j₂ := mem_interior.mpr ⟨hwS, hw₁, hw₂⟩
  have hGX : X ⊆ (groupGraph M S).verts := hX
  by_cases hwX : w ∈ X
  · have hle := attachU hC hdeg4 hbig hGX h2 hwI hwX
    have hdisj : Disjoint ({w} : Finset V) (S \ X) := by
      rw [Finset.disjoint_singleton_left]; exact fun h => (Finset.mem_sdiff.mp h).2 hwX
    have hcb := crossBonds_eq_eW M (Finset.singleton_subset_iff.mpr hwS) Finset.sdiff_subset hdisj
    have hge : 2 ≤ crossBonds M {w} (S \ X) := by
      unfold crossBonds
      have hsub : ({e, f} : Finset D) ⊆ M.bonds.filter fun x =>
          (M.atom x ∈ ({w} : Finset V) ∧ M.atom (M.mate x) ∈ S \ X) ∨
            (M.atom x ∈ S \ X ∧ M.atom (M.mate x) ∈ ({w} : Finset V)) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨he, cross_mem hce hwe hwX⟩
        · exact Finset.mem_filter.mpr ⟨hf, cross_mem hcf hwf hwX⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hef] at this
    rw [hcb] at hge
    exact absurd hle (by simp only [groupGraph_verts]; omega)
  · have hle := attachU_compl hC hdeg4 hbig hGX h2 hwI hwX
    have hdisj : Disjoint ({w} : Finset V) X := Finset.disjoint_singleton_left.mpr hwX
    have hcb := crossBonds_eq_eW M (Finset.singleton_subset_iff.mpr hwS) hX hdisj
    have hge : 2 ≤ crossBonds M {w} X := by
      unfold crossBonds
      have hsub : ({e, f} : Finset D) ⊆ M.bonds.filter fun x =>
          (M.atom x ∈ ({w} : Finset V) ∧ M.atom (M.mate x) ∈ X) ∨
            (M.atom x ∈ X ∧ M.atom (M.mate x) ∈ ({w} : Finset V)) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨he, cross_mem' hce hwe hwX⟩
        · exact Finset.mem_filter.mpr ⟨hf, cross_mem' hcf hwf hwX⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hef] at this
    rw [hcb] at hge
    omega

end M

end WaveTurbulence.TVine.Struct
