/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Ladders.Basic
public import WaveTurbulence.Foundations.TVine.Struct.Attach
import Mathlib.Tactic

/-!
# Two-edge cuts between rung pieces are ladder steps (packet L3-LAD)

For a T-vine `(S, j₁, j₂)` of a molecule (`TV`: the T-vine, balance `outIn = inIn` on `S` from `IsMolecule`, and
M4 Lemma A from the piece-shape theorem, `attach_of_pieceShape`):

* `balance`: as many bonds of `S` leave a set `X ⊆ S` as enter it (N1 Lemma D, "balance");
* `matchStep_of_cut` (N3 L295–L296): if `X ⊆ S` has exactly two crossing bonds, and these are the two bonds between
  a 2-atom set `R` outside `X` and a set `R'` inside `X` (all atoms interior), then `R → R'` is a ladder step: by
  Lemma A the two bonds have distinct ends on both sides (so they are single), and by balance one enters `X`, the
  other leaves it (so they are anti-parallel);
* piece facts (`piece_facts`, `piece_disj`, `exists_piece`) and the cut of a 2-atom piece (`TV.pair_cut`:
  `8 - 2 · mult`, so `4` for a rung piece and `6` for a junction piece).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Ladders

open Finset TVine WaveTurbulence.TVine.Core CutAlg

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-! ## Bond sets -/

/-- The bonds between `A` and `B` (each named by its outgoing dart); `crossBonds M A B` is its size. -/
def bondSet (M : Molecule V D) (A B : Finset V) : Finset D :=
  M.bonds.filter fun x => (M.atom x ∈ A ∧ M.atom (M.mate x) ∈ B) ∨ (M.atom x ∈ B ∧ M.atom (M.mate x) ∈ A)

theorem card_bondSet (M : Molecule V D) (A B : Finset V) : (bondSet M A B).card = crossBonds M A B := rfl

theorem mem_bondSet {M : Molecule V D} {A B : Finset V} {x : D} :
    x ∈ bondSet M A B ↔
      x ∈ M.bonds ∧ ((M.atom x ∈ A ∧ M.atom (M.mate x) ∈ B) ∨ (M.atom x ∈ B ∧ M.atom (M.mate x) ∈ A)) :=
  Finset.mem_filter

theorem bondSet_comm (M : Molecule V D) (A B : Finset V) : bondSet M A B = bondSet M B A := by
  ext x; simp only [mem_bondSet]; tauto

theorem crossBonds_comm' (M : Molecule V D) (A B : Finset V) : crossBonds M A B = crossBonds M B A := by
  rw [← card_bondSet, bondSet_comm, card_bondSet]

theorem bondSet_mono {M : Molecule V D} {A A' B B' : Finset V} (hA : A ⊆ A') (hB : B ⊆ B') :
    bondSet M A B ⊆ bondSet M A' B' := by
  intro x hx
  rw [mem_bondSet] at hx ⊢
  rcases hx with ⟨hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact ⟨hx, Or.inl ⟨hA h1, hB h2⟩⟩
  · exact ⟨hx, Or.inr ⟨hB h1, hA h2⟩⟩

theorem crossBonds_le_of_subset {M : Molecule V D} {A A' B B' : Finset V} (hA : A ⊆ A') (hB : B ⊆ B') :
    crossBonds M A B ≤ crossBonds M A' B' :=
  Finset.card_le_card (bondSet_mono hA hB)

theorem not_mem_bondSet_of_zero {M : Molecule V D} {A B : Finset V} (h : crossBonds M A B = 0) {x : D} :
    x ∉ bondSet M A B := by
  intro hx
  rw [← card_bondSet, Finset.card_eq_zero] at h
  rw [h] at hx
  exact Finset.notMem_empty x hx

theorem crossBonds_empty_right (M : Molecule V D) (A : Finset V) : crossBonds M A ∅ = 0 := by
  rw [← card_bondSet, Finset.card_eq_zero]
  ext x
  simp [mem_bondSet]

/-- A bond between `R` and `R'` has one end in each. -/
theorem ends_of_mem_bondSet {M : Molecule V D} {R R' : Finset V} {g : D} (hg : g ∈ bondSet M R R') :
    ∃ p ∈ R, ∃ p' ∈ R', M.ends g = s(p, p') := by
  rw [mem_bondSet] at hg
  rcases hg.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, h1, _, h2, rfl⟩
  · exact ⟨_, h2, _, h1, Sym2.eq_swap⟩

/-- Crossing `X` inside `S` is membership in the bonds between `X` and `S ∖ X`. -/
theorem crossesIn_iff {M : Molecule V D} {S X : Finset V} (hX : X ⊆ S) {g : D} (hg : g ∈ M.bonds) :
    CrossesIn M S X g ↔ g ∈ bondSet M X (S \ X) := by
  rw [mem_bondSet]
  unfold CrossesIn Molecule.InGroup
  constructor
  · rintro ⟨⟨h1, h2⟩, h⟩
    refine ⟨hg, ?_⟩
    by_cases hx : M.atom g ∈ X
    · exact Or.inl ⟨hx, Finset.mem_sdiff.mpr ⟨h2, h.mp hx⟩⟩
    · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨h1, hx⟩, by by_contra hm; exact hx (h.mpr hm)⟩
  · rintro ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · rw [Finset.mem_sdiff] at h2
      exact ⟨⟨hX h1, h2.1⟩, ⟨fun _ => h2.2, fun _ => h1⟩⟩
    · rw [Finset.mem_sdiff] at h1
      exact ⟨⟨h1.1, hX h2⟩, ⟨fun hh => absurd hh h1.2, fun hh => absurd h2 hh⟩⟩

/-! ## The T-vine context -/

/-- Balance on a block of a molecule: every atom of `S` has as many outgoing as incoming bonds in `S`. -/
theorem outIn_eq_inIn {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (hM : M.IsMolecule)
    (hB : M.IsBlock S j₁ j₂) : ∀ w ∈ S, M.outIn S w = M.inIn S w := by
  intro w hw
  obtain ⟨hSA, -, -, -, ho₁, hi₁, ho₂, hi₂, hdeg, -⟩ := hB
  by_cases hw₁ : w = j₁
  · rw [hw₁, ho₁, hi₁]
  by_cases hw₂ : w = j₂
  · rw [hw₂, ho₂, hi₂]
  have h4 := hdeg w hw hw₁ hw₂
  rw [degIn_eq_outIn_add_inIn M S w] at h4
  obtain ⟨hout, hin⟩ := hM.1 w (hSA hw)
  have h1 : M.outIn S w ≤ M.outdeg w := Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩)
  have h2 : M.inIn S w ≤ M.indeg w := Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩)
  omega

/-- **The T-vine context**: a T-vine of a molecule, with balance and M4 Lemma A. -/
structure TV (M : Molecule V D) (S : Finset V) (j₁ j₂ : V) : Prop where
  tv : M.IsTVine S j₁ j₂
  bal : ∀ w ∈ S, M.outIn S w = M.inIn S w
  attach : ∀ X ⊆ S, ∀ e ∈ M.bonds, ∀ f ∈ M.bonds, e ≠ f → CrossesIn M S X e → CrossesIn M S X f →
    (∀ g ∈ M.bonds, CrossesIn M S X g → g = e ∨ g = f) →
    ∀ w : V, w ≠ j₁ → w ≠ j₂ → ¬ (w ∈ M.ends e ∧ w ∈ M.ends f)

theorem TV.of (hP : PieceShapeStatement.{u, v}) {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V}
    {j₁ j₂ : V} (hT : M.IsTVine S j₁ j₂) : TV M S j₁ j₂ :=
  ⟨hT, outIn_eq_inIn hM hT.1, attach_of_pieceShape hP M S j₁ j₂ hT⟩

section TV

variable {M : Molecule V D} {S : Finset V} {j₁ j₂ : V}

theorem TV.j₁_mem (h : TV M S j₁ j₂) : j₁ ∈ S := h.tv.1.2.1

theorem TV.j₂_mem (h : TV M S j₁ j₂) : j₂ ∈ S := h.tv.1.2.2.1

theorem TV.ne (h : TV M S j₁ j₂) : j₁ ≠ j₂ := h.tv.1.2.2.2.1

theorem TV.degIn (h : TV M S j₁ j₂) {w : V} (hw : w ∈ S) (hw₁ : w ≠ j₁) (hw₂ : w ≠ j₂) : M.degIn S w = 4 :=
  h.tv.1.2.2.2.2.2.2.2.2.1 w hw hw₁ hw₂

theorem TV.cutCtx (h : TV M S j₁ j₂) : CutCtx (groupGraph M S) :=
  cutCtx_of_isTVineU (isTVineU_of_isTVine M h.tv)

theorem crossBonds_compl_eq_cut (M : Molecule V D) {S X : Finset V} (hX : X ⊆ S) :
    crossBonds M X (S \ X) = cut (groupGraph M S) X := by
  rw [crossBonds_eq_eW M hX Finset.sdiff_subset Finset.disjoint_sdiff, cut_eq_eW, groupGraph_verts]

/-- No nonempty proper subset of a T-vine has fewer than two crossing bonds. -/
theorem TV.two_le (h : TV M S j₁ j₂) {X : Finset V} (hX : X ⊆ S) {a b : V} (ha : a ∈ X) (hb : b ∈ S)
    (hbX : b ∉ X) : 2 ≤ crossBonds M X (S \ X) := by
  rw [crossBonds_compl_eq_cut M hX]
  exact two_le_cut h.cutCtx hX ha hb hbX

/-- The cut of two interior atoms `a ≠ b` is `8 - 2 · mult(a, b)`. -/
theorem TV.pair_cut (h : TV M S j₁ j₂) {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (ha₁ : a ≠ j₁) (ha₂ : a ≠ j₂) (hb₁ : b ≠ j₁) (hb₂ : b ≠ j₂) :
    crossBonds M {a, b} (S \ {a, b}) + 2 * M.bondsBetween a b = 8 := by
  have hC := h.cutCtx
  have hsub : ({a, b} : Finset V) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  rw [crossBonds_compl_eq_cut M hsub]
  have hu := cut_union_disjoint (G := groupGraph M S) (X := {a}) (Y := {b})
    (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_subset_iff.mpr hb) (Finset.disjoint_singleton.mpr hab)
  rw [cut_singleton hC ha, cut_singleton hC hb, ← Finset.insert_eq] at hu
  have heW : eW (wG (groupGraph M S)) {a} {b} = M.bondsBetween a b := by
    unfold eW wG
    rw [Finset.sum_singleton, Finset.sum_singleton]
    exact (bondsBetween_eq M ha hb).symm
  have hda : deg (groupGraph M S) a = 4 := by rw [← degIn_eq M ha]; exact h.degIn ha ha₁ ha₂
  have hdb : deg (groupGraph M S) b = 4 := by rw [← degIn_eq M hb]; exact h.degIn hb hb₁ hb₂
  omega

/-! ## Pieces -/

theorem piece_facts {P : Finset V} (hP : P ∈ M.pieces S j₁ j₂) : P ⊆ S ∧ j₁ ∉ P ∧ j₂ ∉ P ∧ P.Nonempty := by
  rw [pieces_eq] at hP
  obtain ⟨hI, hne, -⟩ := piece_props hP
  exact ⟨fun w hw => (mem_interior.mp (hI hw)).1, fun hh => (mem_interior.mp (hI hh)).2.1 rfl,
    fun hh => (mem_interior.mp (hI hh)).2.2 rfl, hne⟩

theorem piece_disj {P Q : Finset V} (hP : P ∈ M.pieces S j₁ j₂) (hQ : Q ∈ M.pieces S j₁ j₂) (hPQ : P ≠ Q) :
    Disjoint P Q := by
  rw [pieces_eq] at hP hQ
  rw [Finset.disjoint_left]
  intro w hwP hwQ
  apply hPQ
  obtain ⟨hPI, -, hPs⟩ := piece_props hP
  obtain ⟨hQI, -, hQs⟩ := piece_props hQ
  ext x
  constructor
  · intro hx; exact (hQs w hwQ x (hPI hx)).mpr ((hPs w hwP x (hPI hx)).mp hx)
  · intro hx; exact (hPs w hwP x (hQI hx)).mpr ((hQs w hwQ x (hQI hx)).mp hx)

theorem exists_piece {w : V} (hw : w ∈ S) (hw₁ : w ≠ j₁) (hw₂ : w ≠ j₂) :
    ∃ P ∈ M.pieces S j₁ j₂, w ∈ P := by
  classical
  rw [pieces_eq]
  have hwI : w ∈ Core.interior (groupGraph M S) j₁ j₂ := mem_interior.mpr ⟨hw, hw₁, hw₂⟩
  exact ⟨(Core.interior (groupGraph M S) j₁ j₂).filter fun x => SamePieceU (groupGraph M S) w x,
    mem_piecesU_iff.mpr ⟨w, hwI, fun x => Finset.mem_filter⟩,
    Finset.mem_filter.mpr ⟨hwI, samePieceU_refl _ w⟩⟩

theorem two_cases {P : Finset V} (h : TwoAtomPiece M P) : IsRungPiece M P ∨ IsJunctionPiece M P := by
  obtain ⟨a, b, hab, rfl, h1 | h2⟩ := h
  · exact Or.inr ⟨a, b, hab, rfl, h1⟩
  · exact Or.inl ⟨a, b, hab, rfl, h2⟩

theorem TV.rung_cut (h : TV M S j₁ j₂) {P : Finset V} (hP : P ∈ M.pieces S j₁ j₂) (hr : IsRungPiece M P) :
    crossBonds M P (S \ P) = 4 := by
  obtain ⟨hPS, hP₁, hP₂, -⟩ := piece_facts hP
  obtain ⟨a, b, hab, rfl, h2⟩ := hr
  have ha : a ∈ ({a, b} : Finset V) := by simp
  have hb : b ∈ ({a, b} : Finset V) := by simp
  have := h.pair_cut (hPS ha) (hPS hb) hab (fun e => hP₁ (e ▸ ha)) (fun e => hP₂ (e ▸ ha))
    (fun e => hP₁ (e ▸ hb)) (fun e => hP₂ (e ▸ hb))
  omega

theorem TV.junction_cut (h : TV M S j₁ j₂) {P : Finset V} (hP : P ∈ M.pieces S j₁ j₂)
    (hj : IsJunctionPiece M P) : crossBonds M P (S \ P) = 6 := by
  obtain ⟨hPS, hP₁, hP₂, -⟩ := piece_facts hP
  obtain ⟨a, b, hab, rfl, h1⟩ := hj
  have ha : a ∈ ({a, b} : Finset V) := by simp
  have hb : b ∈ ({a, b} : Finset V) := by simp
  have := h.pair_cut (hPS ha) (hPS hb) hab (fun e => hP₁ (e ▸ ha)) (fun e => hP₂ (e ▸ ha))
    (fun e => hP₁ (e ▸ hb)) (fun e => hP₂ (e ▸ hb))
  omega

/-! ## Balance -/

/-- The bonds of the atomic group `S`. -/
def grpBonds (M : Molecule V D) (S : Finset V) : Finset D := M.bonds.filter fun x => M.InGroup S x

theorem mem_bonds' {M : Molecule V D} {x : D} : x ∈ M.bonds ↔ M.out x = true := by
  simp [Molecule.bonds]

theorem mem_grpBonds {M : Molecule V D} {S : Finset V} {x : D} :
    x ∈ grpBonds M S ↔ x ∈ M.bonds ∧ M.InGroup S x :=
  Finset.mem_filter

theorem sum_outIn (M : Molecule V D) (S X : Finset V) :
    ∑ w ∈ X, M.outIn S w = ((grpBonds M S).filter fun x => M.atom x ∈ X).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := M.atom) (s := (grpBonds M S).filter fun x => M.atom x ∈ X) (t := X)
    (fun x hx => (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2)]
  refine Finset.sum_congr rfl fun w hw => ?_
  unfold Molecule.outIn Molecule.dartsAt
  congr 1
  ext x
  by_cases hxw : M.atom x = w <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_grpBonds, mem_bonds', hxw, hw] <;> tauto

theorem sum_inIn (M : Molecule V D) (S X : Finset V) :
    ∑ w ∈ X, M.inIn S w = ((grpBonds M S).filter fun x => M.atom (M.mate x) ∈ X).card := by
  have h1 : ∑ w ∈ X, M.inIn S w =
      ((Finset.univ.filter fun x => M.out x = false ∧ M.InGroup S x).filter fun x => M.atom x ∈ X).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := M.atom)
      (s := (Finset.univ.filter fun x => M.out x = false ∧ M.InGroup S x).filter fun x => M.atom x ∈ X) (t := X)
      (fun x hx => (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2)]
    refine Finset.sum_congr rfl fun w hw => ?_
    unfold Molecule.inIn Molecule.dartsAt
    congr 1
    ext x
    by_cases hxw : M.atom x = w <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hxw, hw] <;> tauto
  rw [h1]
  refine Finset.card_nbij' M.mate M.mate ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe] at hx ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_grpBonds, mem_bonds', M.mate_mate,
      M.out_mate] at hx ⊢
    obtain ⟨⟨ho, h1, h2⟩, h3⟩ := hx
    exact ⟨⟨by simp [ho], And.intro h2 (by rw [M.mate_mate]; exact h1)⟩, h3⟩
  · intro x hx
    rw [Finset.mem_coe] at hx ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_grpBonds, mem_bonds', M.out_mate] at hx ⊢
    obtain ⟨⟨ho, h1, h2⟩, h3⟩ := hx
    exact ⟨⟨by simp [ho], And.intro h2 (by rw [M.mate_mate]; exact h1)⟩, h3⟩
  · intro x _; exact M.mate_mate x
  · intro x _; exact M.mate_mate x

/-- **Balance** (N1 Lemma D): as many bonds of `S` leave `X ⊆ S` as enter it. -/
theorem TV.balance {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (h : TV M S j₁ j₂) {X : Finset V}
    (hX : X ⊆ S) :
    (M.bonds.filter fun x => M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X).card =
      (M.bonds.filter fun x => M.atom x ∈ S \ X ∧ M.atom (M.mate x) ∈ X).card := by
  have hsum : ∑ w ∈ X, M.outIn S w = ∑ w ∈ X, M.inIn S w :=
    Finset.sum_congr rfl fun w hw => h.bal w (hX hw)
  rw [sum_outIn, sum_inIn] at hsum
  have e1 := Finset.card_filter_add_card_filter_not
    (s := (grpBonds M S).filter fun x => M.atom x ∈ X) (fun x => M.atom (M.mate x) ∈ X)
  have e2 := Finset.card_filter_add_card_filter_not
    (s := (grpBonds M S).filter fun x => M.atom (M.mate x) ∈ X) (fun x => M.atom x ∈ X)
  simp only [Finset.filter_filter] at e1 e2
  have e3 : ((grpBonds M S).filter fun x => M.atom (M.mate x) ∈ X ∧ M.atom x ∈ X) =
      (grpBonds M S).filter fun x => M.atom x ∈ X ∧ M.atom (M.mate x) ∈ X :=
    Finset.filter_congr (fun x _ => and_comm)
  have e4 : (M.bonds.filter fun x => M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X) =
      (grpBonds M S).filter fun x => M.atom x ∈ X ∧ ¬ M.atom (M.mate x) ∈ X := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, mem_grpBonds]
    constructor
    · rintro ⟨hx, h1, h2, h3⟩; exact ⟨⟨hx, And.intro (hX h1) h2⟩, h1, h3⟩
    · rintro ⟨⟨hx, -, h2⟩, h1, h3⟩; exact ⟨hx, h1, h2, h3⟩
  have e5 : (M.bonds.filter fun x => M.atom x ∈ S \ X ∧ M.atom (M.mate x) ∈ X) =
      (grpBonds M S).filter fun x => M.atom (M.mate x) ∈ X ∧ ¬ M.atom x ∈ X := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, mem_grpBonds]
    constructor
    · rintro ⟨hx, ⟨h1, h2⟩, h3⟩; exact ⟨⟨hx, And.intro h1 (hX h3)⟩, h3, h2⟩
    · rintro ⟨⟨hx, h1, -⟩, h3, h2⟩; exact ⟨hx, ⟨h1, h2⟩, h3⟩
  rw [e4, e5]
  rw [e3] at e2
  omega

/-- On a 2-edge-cut `{e, f}` of `X`, one bond leaves `X` and the other enters it. -/
theorem TV.balance_pair {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (h : TV M S j₁ j₂) {X : Finset V}
    (hX : X ⊆ S) {e f : D} (hef : e ≠ f) (hK : bondSet M X (S \ X) = {e, f}) :
    (M.atom e ∈ X ↔ M.atom f ∉ X) := by
  have hbal := h.balance hX
  have hKm : ∀ x, x ∈ bondSet M X (S \ X) ↔ x = e ∨ x = f := by
    intro x; rw [hK]; simp
  have heK := (hKm e).mpr (Or.inl rfl)
  have hfK := (hKm f).mpr (Or.inr rfl)
  have hOut : ∀ x, x ∈ bondSet M X (S \ X) → M.atom x ∈ X →
      x ∈ M.bonds.filter fun x => M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X := by
    intro x hx hxX
    rw [mem_bondSet] at hx
    rcases hx with ⟨hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Finset.mem_filter.mpr ⟨hx, h1, h2⟩
    · exact absurd hxX (Finset.mem_sdiff.mp h1).2
  have hIn : ∀ x, x ∈ bondSet M X (S \ X) → M.atom x ∉ X →
      x ∈ M.bonds.filter fun x => M.atom x ∈ S \ X ∧ M.atom (M.mate x) ∈ X := by
    intro x hx hxX
    rw [mem_bondSet] at hx
    rcases hx with ⟨hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact absurd h1 hxX
    · exact Finset.mem_filter.mpr ⟨hx, h1, h2⟩
  have hOutK : ∀ x ∈ M.bonds.filter (fun x => M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X),
      x = e ∨ x = f := by
    intro x hx
    obtain ⟨hx, h1, h2⟩ := Finset.mem_filter.mp hx
    exact (hKm x).mp (mem_bondSet.mpr ⟨hx, Or.inl ⟨h1, h2⟩⟩)
  have hInK : ∀ x ∈ M.bonds.filter (fun x => M.atom x ∈ S \ X ∧ M.atom (M.mate x) ∈ X),
      x = e ∨ x = f := by
    intro x hx
    obtain ⟨hx, h1, h2⟩ := Finset.mem_filter.mp hx
    exact (hKm x).mp (mem_bondSet.mpr ⟨hx, Or.inr ⟨h1, h2⟩⟩)
  by_cases he : M.atom e ∈ X <;> by_cases hf : M.atom f ∈ X
  · exfalso
    have h1 : ({e, f} : Finset D) ⊆ M.bonds.filter fun x => M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hOut _ heK he
      · exact hOut _ hfK hf
    have h2 : (M.bonds.filter fun x => M.atom x ∈ S \ X ∧ M.atom (M.mate x) ∈ X).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hxX := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).2.1).2
      rcases hInK x hx with rfl | rfl
      · exact hxX he
      · exact hxX hf
    have := Finset.card_le_card h1
    rw [Finset.card_pair hef] at this
    omega
  · simp [he, hf]
  · simp [he, hf]
  · exfalso
    have h1 : ({e, f} : Finset D) ⊆ M.bonds.filter fun x => M.atom x ∈ S \ X ∧ M.atom (M.mate x) ∈ X := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hIn _ heK he
      · exact hIn _ hfK hf
    have h2 : (M.bonds.filter fun x => M.atom x ∈ X ∧ M.atom (M.mate x) ∈ S \ X).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hxX := (Finset.mem_filter.mp hx).2.1
      rcases hOutK x hx with rfl | rfl
      · exact he hxX
      · exact hf hxX
    have := Finset.card_le_card h1
    rw [Finset.card_pair hef] at this
    omega

/-! ## Two-edge cuts give ladder steps -/

/-- The oriented core of `matchStep_of_cut`. -/
theorem TV.gml_oriented (h : TV M S j₁ j₂) {X R R' : Finset V} (hX : X ⊆ S) (hR : R ⊆ S \ X) (hR' : R' ⊆ X)
    (hRc : R.card = 2) {e f : D} (hef : e ≠ f) (hK : bondSet M X (S \ X) = {e, f}) {a b a' b' : V}
    (ha : a ∈ R) (hb : b ∈ R) (hab : a ≠ b) (ha' : a' ∈ R') (hb' : b' ∈ R') (he : M.ends e = s(a, a'))
    (hf : M.ends f = s(b, b')) :
    R = {a, b} ∧ M.bondsBetween a a' = 1 ∧ M.bondsBetween b b' = 1 ∧ (M.Directed a a' ↔ M.Directed b' b) := by
  have haX := (Finset.mem_sdiff.mp (hR ha)).2
  have hbX := (Finset.mem_sdiff.mp (hR hb)).2
  have ha'X := hR' ha'
  have hb'X := hR' hb'
  have hKmem : ∀ x ∈ M.bonds, ∀ p q, M.ends x = s(p, q) → p ∈ S \ X → q ∈ X → x = e ∨ x = f := by
    intro x hx p q hxe hp hq
    have hm : x ∈ bondSet M X (S \ X) := by
      rw [mem_bondSet]
      refine ⟨hx, ?_⟩
      simp only [Molecule.ends, Sym2.eq_iff] at hxe
      rcases hxe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; rw [h1, h2]; exact ⟨hp, hq⟩
      · left; rw [h1, h2]; exact ⟨hq, hp⟩
    rw [hK] at hm
    simpa using hm
  have heB : e ∈ M.bonds := (mem_bondSet.mp (show e ∈ bondSet M X (S \ X) by rw [hK]; simp)).1
  have hfB : f ∈ M.bonds := (mem_bondSet.mp (show f ∈ bondSet M X (S \ X) by rw [hK]; simp)).1
  have uniq_e : ∀ x ∈ M.bonds, M.ends x = s(a, a') → x = e := by
    intro x hx hxe
    rcases hKmem x hx a a' hxe (hR ha) ha'X with h1 | h1
    · exact h1
    · exfalso
      rw [h1, hf, Sym2.eq_iff] at hxe
      rcases hxe with ⟨h2, -⟩ | ⟨h2, -⟩
      · exact hab h2.symm
      · exact hbX (h2 ▸ ha'X)
  have uniq_f : ∀ x ∈ M.bonds, M.ends x = s(b, b') → x = f := by
    intro x hx hxe
    rcases hKmem x hx b b' hxe (hR hb) hb'X with h1 | h1
    · exfalso
      rw [h1, he, Sym2.eq_iff] at hxe
      rcases hxe with ⟨h2, -⟩ | ⟨h2, -⟩
      · exact hab h2
      · exact haX (h2 ▸ hb'X)
    · exact h1
  have hbb : ∀ (x : D) (p q : V), x ∈ M.bonds → M.ends x = s(p, q) →
      (∀ y ∈ M.bonds, M.ends y = s(p, q) → y = x) → M.bondsBetween p q = 1 := by
    intro x p q hx hxe hu
    unfold Molecule.bondsBetween
    rw [Finset.card_eq_one]
    refine ⟨x, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨hy, hye⟩ => hu y hy hye, fun hy => hy ▸ ⟨hx, hxe⟩⟩
  have hdir : ∀ (x : D) (p q : V), x ∈ M.bonds → M.ends x = s(p, q) → p ≠ q →
      (∀ y ∈ M.bonds, M.ends y = s(p, q) → y = x) → (M.Directed p q ↔ M.atom x = p) := by
    intro x p q hx hxe hpq hu
    constructor
    · rintro ⟨y, hyo, hyp, hyq⟩
      have hyB : y ∈ M.bonds := by simp [Molecule.bonds, hyo]
      have := hu y hyB (by simp [Molecule.ends, hyp, hyq])
      rw [← this]; exact hyp
    · intro hxp
      have hxo : M.out x = true := by simpa [Molecule.bonds] using hx
      refine ⟨x, hxo, hxp, ?_⟩
      have h2 := hxe
      simp only [Molecule.ends, Sym2.eq_iff] at h2
      rcases h2 with ⟨-, h3⟩ | ⟨h3, -⟩
      · exact h3
      · exact absurd (hxp.symm.trans h3) hpq
  have haa' : a ≠ a' := fun hh => haX (hh ▸ ha'X)
  have hbb' : b' ≠ b := fun hh => hbX (hh ▸ hb'X)
  have hdirE : M.Directed a a' ↔ M.atom e = a := hdir e a a' heB he haa' uniq_e
  have hdirF : M.Directed b' b ↔ M.atom f = b' :=
    hdir f b' b hfB (by rw [hf, Sym2.eq_swap]) hbb' (fun y hy hye => uniq_f y hy (by rw [hye, Sym2.eq_swap]))
  have hbp := h.balance_pair hX hef hK
  have hea : M.atom e = a ↔ M.atom e ∉ X := by
    have h2 := he
    simp only [Molecule.ends, Sym2.eq_iff] at h2
    constructor
    · intro hh; rw [hh]; exact haX
    · intro hh
      rcases h2 with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact h3
      · exact absurd (h3 ▸ ha'X) hh
  have hfb : M.atom f = b' ↔ M.atom f ∈ X := by
    have h2 := hf
    simp only [Molecule.ends, Sym2.eq_iff] at h2
    constructor
    · intro hh; rw [hh]; exact hb'X
    · intro hh
      rcases h2 with ⟨h3, -⟩ | ⟨h3, -⟩
      · exact absurd (h3 ▸ hh) hbX
      · exact h3
  refine ⟨?_, hbb e a a' heB he uniq_e, hbb f b b' hfB hf uniq_f, ?_⟩
  · refine (Finset.eq_of_subset_of_card_le ?_ (by rw [hRc, Finset.card_pair hab])).symm
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [hdirE, hdirF, hea, hfb]
    tauto

/-- **A two-edge cut between two pieces is a ladder step** (N3 L295–L296). -/
theorem TV.matchStep_of_cut (h : TV M S j₁ j₂) {X R R' : Finset V} (hX : X ⊆ S)
    (hcut : crossBonds M X (S \ X) = 2) (hR : R ⊆ S \ X) (hR' : R' ⊆ X)
    (hRj : ∀ w ∈ R, w ≠ j₁ ∧ w ≠ j₂) (hR'j : ∀ w ∈ R', w ≠ j₁ ∧ w ≠ j₂) (hRc : R.card = 2)
    (h2 : crossBonds M R R' = 2) : MatchStep M R R' := by
  intro a' b' hab' hR'eq
  obtain ⟨e, f, hef, hF⟩ := Finset.card_eq_two.mp (show (bondSet M R R').card = 2 from h2)
  have hsub : bondSet M R R' ⊆ bondSet M X (S \ X) := by
    intro x hx
    rw [mem_bondSet] at hx ⊢
    rcases hx with ⟨hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨hx, Or.inr ⟨hR h1, hR' h2⟩⟩
    · exact ⟨hx, Or.inl ⟨hR' h1, hR h2⟩⟩
  have hK : bondSet M X (S \ X) = {e, f} := by
    rw [← hF]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [card_bondSet, card_bondSet, hcut, h2])).symm
  have heK : e ∈ bondSet M X (S \ X) := by rw [hK]; simp
  have hfK : f ∈ bondSet M X (S \ X) := by rw [hK]; simp
  have heB : e ∈ M.bonds := (mem_bondSet.mp heK).1
  have hfB : f ∈ M.bonds := (mem_bondSet.mp hfK).1
  have hA := h.attach X hX e heB f hfB hef ((crossesIn_iff hX heB).mpr heK) ((crossesIn_iff hX hfB).mpr hfK)
    (fun g hg hc => by
      have hm := (crossesIn_iff hX hg).mp hc
      rw [hK] at hm
      simpa using hm)
  obtain ⟨pe, hpe, qe, hqe, hee⟩ := ends_of_mem_bondSet (show e ∈ bondSet M R R' by rw [hF]; simp)
  obtain ⟨pf, hpf, qf, hqf, hfe⟩ := ends_of_mem_bondSet (show f ∈ bondSet M R R' by rw [hF]; simp)
  have hp : pe ≠ pf := fun hh => hA pe (hRj pe hpe).1 (hRj pe hpe).2
    ⟨by rw [hee]; exact Sym2.mem_mk_left _ _, by rw [hfe, ← hh]; exact Sym2.mem_mk_left _ _⟩
  have hq : qe ≠ qf := fun hh => hA qe (hR'j qe hqe).1 (hR'j qe hqe).2
    ⟨by rw [hee]; exact Sym2.mem_mk_right _ _, by rw [hfe, ← hh]; exact Sym2.mem_mk_right _ _⟩
  have ha'R' : a' ∈ R' := by rw [hR'eq]; simp
  have hb'R' : b' ∈ R' := by rw [hR'eq]; simp
  have hqe' := hqe
  have hqf' := hqf
  rw [hR'eq, Finset.mem_insert, Finset.mem_singleton] at hqe' hqf'
  have hcases : (qe = a' ∧ qf = b') ∨ (qe = b' ∧ qf = a') := by
    rcases hqe' with h1 | h1 <;> rcases hqf' with h2 | h2
    · exact absurd (h1.trans h2.symm) hq
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hq
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at hee; rw [h2] at hfe
    obtain ⟨hReq, hb1, hb2, hd⟩ := h.gml_oriented hX hR hR' hRc hef hK hpe hpf hp ha'R' hb'R' hee hfe
    exact ⟨pe, pf, hp, hReq, hb1, hb2, hd⟩
  · rw [h1] at hee; rw [h2] at hfe
    obtain ⟨hReq, hb1, hb2, hd⟩ := h.gml_oriented hX hR hR' hRc hef.symm
      (by rw [hK, Finset.pair_comm]) hpf hpe hp.symm ha'R' hb'R' hfe hee
    exact ⟨pf, pe, hp.symm, hReq, hb1, hb2, hd⟩

end TV

end WaveTurbulence.TVine.Struct.Ladders
