/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.PiecesB
public import WaveTurbulence.Foundations.TVine.Checker.Statement
public import WaveTurbulence.Foundations.TVine.Core.Statements
import Mathlib.Tactic

/-!
# N2 Proposition 1.17: pieces under deletion and the piece-shape theorem (packet L3)

* (a) `rung_piece`, `piece_of_del`, `piece_cases_del`, `mult_del_piece`: for a deletable rung `R`,
  `pieces(G/R) = pieces(G) ∖ {R}` with unchanged internal multiplicities (N2 L484–L503);
* `pieceShapeU_of_del`: the piece shape lifts from `G/R` to `G`;
* NAMED INPUT `DeleteRungInput` (N2 Lemma 1.9(1), owner L1); the base is L2's published
  `Checker.PieceShapeBaseStatement` (≤ 13 atoms) with `Checker.SizeBoundStatement` (N2 Lemma 1.8);
* (b) **`pieceShapeU_of_isTVineU`** (induction on size) and **`pieceShape : PieceShapeStatement`**.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

universe u v

section rung

variable {V : Type*} [DecidableEq V] {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp : V} {Km Kp : Finset V}

namespace RungFacts

variable (hR : IsRungAt G a b xm xp ym yp Km Kp)
include hR

theorem interior_del : Core.interior (rungDel G a b xm xp ym yp true) j₁ j₂ = Core.interior G j₁ j₂ \ {a, b} := by
  ext x
  rw [mem_interior, Finset.mem_sdiff, mem_interior, hR.verts_rungDel true]
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **The rung is a piece** (N2 L500: "R itself is a piece of B"). -/
theorem rung_piece (haI : a ∈ Core.interior G j₁ j₂) (hbI : b ∈ Core.interior G j₁ j₂) :
    ({a, b} : Finset V) ∈ piecesU G j₁ j₂ := by
  refine mem_piecesU_of_class (u := a) (Finset.insert_subset haI (Finset.singleton_subset_iff.mpr hbI))
    (Finset.mem_insert_self a _) (fun w hw => ?_) (fun w hw hwab => ?_)
  · rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact samePieceU_refl G w
    · exact fun X hX hc => ab_together hR hX hc
  · have hwV := interior_subset_verts j₁ j₂ hw
    have hwK : w ∈ Km ∨ w ∈ Kp := by
      have := (verts_eq hR) ▸ hwV
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this hwab
      tauto
    intro hs
    rcases hwK with hwK | hwK
    · have hKmV : Km ⊆ G.verts := fun x hx => (pole_mem hR (Or.inl hx)).1
      exact (a_not_pole hR).1 ((hs Km hKmV (cut_Km hR).le).mpr hwK)
    · have hKpV : Kp ⊆ G.verts := fun x hx => (pole_mem hR (Or.inr hx)).1
      exact (a_not_pole hR).2 ((hs Kp hKpV (cut_Kp hR).le).mpr hwK)

theorem interior_del_pole {x : V} (hx : x ∈ Core.interior (rungDel G a b xm xp ym yp true) j₁ j₂) :
    x ∈ Km ∪ Kp := by
  have := interior_subset_verts j₁ j₂ hx
  rwa [verts_del hR] at this

/-- **A piece of `G/R` is a piece of `G`.** -/
theorem piece_of_del (hC : CutCtx G) (haI : a ∈ Core.interior G j₁ j₂) (hbI : b ∈ Core.interior G j₁ j₂)
    {P : Finset V} (hP : P ∈ piecesU (rungDel G a b xm xp ym yp true) j₁ j₂) : P ∈ piecesU G j₁ j₂ := by
  obtain ⟨u, huI', hPu⟩ := mem_piecesU_iff.mp hP
  have huI : u ∈ Core.interior G j₁ j₂ := by
    rw [interior_del hR] at huI'; exact (Finset.mem_sdiff.mp huI').1
  have huab : u ∉ ({a, b} : Finset V) := by rw [interior_del hR] at huI'; exact (Finset.mem_sdiff.mp huI').2
  have huK := interior_del_pole hR huI'
  rw [mem_piecesU_iff]
  refine ⟨u, huI, fun w => ⟨fun hw => ?_, fun ⟨hwI, hs⟩ => ?_⟩⟩
  · obtain ⟨hwI', hs'⟩ := (hPu w).mp hw
    have hwK := interior_del_pole hR hwI'
    refine ⟨by rw [interior_del hR] at hwI'; exact (Finset.mem_sdiff.mp hwI').1, ?_⟩
    exact (samePieceU_del_iff hR hC huK hwK).mpr hs'
  · by_cases hwab : w ∈ ({a, b} : Finset V)
    · exfalso
      have hrp := rung_piece hR haI hbI
      have := ((piece_props hrp).2.2 w hwab u huI).mpr (samePieceU_symm hs)
      exact huab this
    · have hwI' : w ∈ Core.interior (rungDel G a b xm xp ym yp true) j₁ j₂ := by
        rw [interior_del hR]; exact Finset.mem_sdiff.mpr ⟨hwI, hwab⟩
      exact (hPu w).mpr ⟨hwI', (samePieceU_del_iff hR hC huK (interior_del_pole hR hwI')).mp hs⟩

/-- **A piece of `G` is the rung or a piece of `G/R`.** -/
theorem piece_cases_del (hC : CutCtx G) (haI : a ∈ Core.interior G j₁ j₂) (hbI : b ∈ Core.interior G j₁ j₂)
    {P : Finset V} (hP : P ∈ piecesU G j₁ j₂) :
    P = {a, b} ∨ P ∈ piecesU (rungDel G a b xm xp ym yp true) j₁ j₂ := by
  classical
  obtain ⟨hPI, ⟨u, hu⟩, -⟩ := piece_props hP
  by_cases huab : u ∈ ({a, b} : Finset V)
  · exact Or.inl (piece_eq_of_mem hP (rung_piece hR haI hbI) hu huab)
  · right
    have huI' : u ∈ Core.interior (rungDel G a b xm xp ym yp true) j₁ j₂ := by
      rw [interior_del hR]; exact Finset.mem_sdiff.mpr ⟨hPI hu, huab⟩
    set P' := (Core.interior (rungDel G a b xm xp ym yp true) j₁ j₂).filter
      fun w => SamePieceU (rungDel G a b xm xp ym yp true) u w with hP'def
    have hP' : P' ∈ piecesU (rungDel G a b xm xp ym yp true) j₁ j₂ := by
      rw [mem_piecesU_iff]; exact ⟨u, huI', fun w => by rw [hP'def, Finset.mem_filter]⟩
    have huP' : u ∈ P' := Finset.mem_filter.mpr ⟨huI', samePieceU_refl _ u⟩
    rw [piece_eq_of_mem hP (piece_of_del hR hC haI hbI hP') hu huP']
    exact hP'

/-- **Internal multiplicities of the pieces of `G/R` are those of `G`.** -/
theorem mult_del_piece {P : Finset V} (hP : P ∈ piecesU (rungDel G a b xm xp ym yp true) j₁ j₂) {x y : V}
    (hx : x ∈ P) (hy : y ∈ P) : (rungDel G a b xm xp ym yp true).mult s(x, y) = G.mult s(x, y) := by
  obtain ⟨hPI, -, hPs⟩ := piece_props hP
  have hxK := interior_del_pole hR (hPI hx)
  have hyK := interior_del_pole hR (hPI hy)
  have hs := (hPs x hx y (hPI hy)).mp hy
  have hKmsub : Km ⊆ (rungDel G a b xm xp ym yp true).verts := by rw [verts_del hR]; exact Finset.subset_union_left
  have hcut : cut (rungDel G a b xm xp ym yp true) Km ≤ 2 := by
    rw [cut_del_decomp hR Finset.subset_union_left, Finset.inter_self, Finset.sdiff_self, eW_empty_right,
      Finset.disjoint_iff_inter_eq_empty.mp hR.disj, eW_empty_left]
    have h1 := ind_le_one (xm ∈ Km ∧ yp ∈ Kp \ Km)
    have h2 := ind_le_one (ym ∈ Km ∧ xp ∈ Kp \ Km)
    have h3 : ind (xm ∈ (∅ : Finset V) ∧ yp ∈ (∅ : Finset V)) = 0 := ind_false (by simp)
    have h4 : ind (ym ∈ (∅ : Finset V) ∧ xp ∈ (∅ : Finset V)) = 0 := ind_false (by simp)
    omega
  have hiff := hs Km hKmsub hcut
  rw [mult_del hR (Finset.mem_union.mp hxK) (Finset.mem_union.mp hyK)]
  have hsame : (x ∈ Km ∧ y ∈ Km) ∨ (x ∈ Kp ∧ y ∈ Kp) := by
    rcases Finset.mem_union.mp hxK with h | h
    · exact Or.inl ⟨h, hiff.mp h⟩
    · have hy' : y ∉ Km := fun h' => not_mem_both hR (hiff.mpr h') h
      exact Or.inr ⟨h, (Finset.mem_union.mp hyK).resolve_left hy'⟩
  rw [adds_count_same hR hsame, add_zero]

/-- **The piece shape lifts from `G/R` to `G`.** -/
theorem pieceShapeU_of_del (hC : CutCtx G) (haI : a ∈ Core.interior G j₁ j₂) (hbI : b ∈ Core.interior G j₁ j₂)
    (h : PieceShapeU (rungDel G a b xm xp ym yp true) j₁ j₂) : PieceShapeU G j₁ j₂ := by
  obtain ⟨core, hcore, hcs, hrest⟩ := h
  refine ⟨core, piece_of_del hR hC haI hbI hcore, ?_, fun P hP hne => ?_⟩
  · obtain ⟨x, y, z, hxy, hyz, hxz, hP3, hm, hcase⟩ := hcs
    have hx : x ∈ core := by rw [hP3]; simp
    have hy : y ∈ core := by rw [hP3]; simp
    have hz : z ∈ core := by rw [hP3]; simp
    rw [mult_del_piece hR hcore hx hy] at hm
    rw [mult_del_piece hR hcore hy hz, mult_del_piece hR hcore hx hz] at hcase
    exact ⟨x, y, z, hxy, hyz, hxz, hP3, hm, hcase⟩
  · rcases piece_cases_del hR hC haI hbI hP with rfl | hP'
    · exact ⟨a, b, hR.ne, rfl, Or.inr hR.mult_ab⟩
    · obtain ⟨p, q, hpq, he, hm⟩ := hrest P hP' hne
      have hp : p ∈ P := by rw [he]; simp
      have hq : q ∈ P := by rw [he]; simp
      rw [mult_del_piece hR hP' hp hq] at hm
      exact ⟨p, q, hpq, he, hm⟩

end RungFacts

end rung

/-! ## Named inputs and the induction -/

/-- **NAMED INPUT (N2 Lemma 1.9(1), rung deletion keeps the class; owner L1).** If `B` is a T-vine and `R` a deletable
rung, then `B/R` is a T-vine, for either matching (`research-gamma-half-2/NOTES.md` L231–L232; M4 §2.2 L152–L153;
REFEREED REF2; path-wise via M4 Lemma 5′). Stated in L1's vocabulary (`IsTVineU`, `IsDeletableAt`, `rungDel`). -/
def DeleteRungInput : Prop := Core.DeleteRungStatement.{u}

/-- **N2 Proposition 1.17(b) at U level**, by induction on the size (N2 L505–L511): delete rungs down to `D = 0`. -/
theorem pieceShapeU_of_isTVineU (hdel : DeleteRungInput.{u}) (hsize : Checker.SizeBoundStatement.{u})
    (hbase : Checker.PieceShapeBaseStatement.{u}) {V : Type u}
    [DecidableEq V] : ∀ (n : ℕ) (G : UMultigraph V) (j₁ j₂ : V), G.verts.card = n → IsTVineU G j₁ j₂ →
      PieceShapeU G j₁ j₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G j₁ j₂ hn hT
    by_cases hD : deletableCount G j₁ j₂ = 0
    · have := hsize G j₁ j₂ hT
      exact hbase G j₁ j₂ hT (by omega)
    · classical
      unfold deletableCount at hD
      obtain ⟨z, hz⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hD)
      obtain ⟨-, a, b, -, xm, xp, ym, yp, Km, Kp, hDel⟩ := Finset.mem_filter.mp hz
      obtain ⟨⟨hR, ha1, ha2, hb1, hb2⟩, hcap⟩ := hDel
      have hT' := hdel G j₁ j₂ a b xm xp ym yp Km Kp hT ⟨⟨hR, ha1, ha2, hb1, hb2⟩, hcap⟩ true
      have hcard : (rungDel G a b xm xp ym yp true).verts.card = n - 2 := by
        rw [hR.verts_rungDel true, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hR.ne, hR.b_mem⟩),
          Finset.card_erase_of_mem hR.a_mem, hn]
        try omega
      have hn2 : 2 ≤ n := by
        rw [← hn]
        exact Finset.card_le_card (Finset.insert_subset hR.a_mem (Finset.singleton_subset_iff.mpr hR.b_mem)) |>.trans'
          (by rw [Finset.card_pair hR.ne])
      have hPS' := ih (n - 2) (by omega) _ j₁ j₂ hcard hT'
      exact RungFacts.pieceShapeU_of_del hR (cutCtx_of_isTVineU hT)
        (mem_interior.mpr ⟨hR.a_mem, ha1, ha2⟩) (mem_interior.mpr ⟨hR.b_mem, hb1, hb2⟩) hPS'

/-! ## The molecule statement -/

section mol

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The pieces partition the interior. -/
theorem sum_card_pieces (G : UMultigraph V) (j₁ j₂ : V) :
    ∑ P ∈ piecesU G j₁ j₂, P.card = (Core.interior G j₁ j₂).card := by
  classical
  have hdisj : ∀ P ∈ piecesU G j₁ j₂, ∀ Q ∈ piecesU G j₁ j₂, P ≠ Q → Disjoint P Q := by
    intro P hP Q hQ hne
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    exact hne (piece_eq_of_mem hP hQ hxP hxQ)
  have hU : (piecesU G j₁ j₂).biUnion id = Core.interior G j₁ j₂ := by
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨P, hP, hx⟩; exact (piece_props hP).1 hx
    · intro hx
      refine ⟨(Core.interior G j₁ j₂).filter fun w => SamePieceU G x w, ?_, ?_⟩
      · rw [mem_piecesU_iff]; exact ⟨x, hx, fun w => by rw [Finset.mem_filter]⟩
      · exact Finset.mem_filter.mpr ⟨hx, samePieceU_refl G x⟩
  rw [← hU, Finset.card_biUnion (t := id) hdisj]
  rfl

/-- **N2 Proposition 1.17(b) (the piece-shape theorem)**, given L1's rung deletion and L2's base and size bound. -/
theorem pieceShape (hdel : DeleteRungInput.{u}) (hsize : Checker.SizeBoundStatement.{u})
    (hbase : Checker.PieceShapeBaseStatement.{u}) : PieceShapeStatement.{u, v} := by
  intro V D _ _ _ M S j₁ j₂ hT
  obtain ⟨hB, hTU⟩ := (isTVine_iff M).mp hT
  obtain ⟨core, hcore, hcs, hrest⟩ := pieceShapeU_of_isTVineU hdel hsize hbase _ (groupGraph M S) j₁ j₂ rfl hTU
  have hS : ∀ {P : Finset V}, P ∈ piecesU (groupGraph M S) j₁ j₂ → ∀ x ∈ P, x ∈ S := fun hP x hx =>
    interior_subset_verts j₁ j₂ ((piece_props hP).1 hx)
  refine ⟨core, by rw [pieces_eq]; exact hcore, ?_, fun P hP hne => ?_, ?_⟩
  · obtain ⟨x, y, z, hxy, hyz, hxz, hP3, hm, hcase⟩ := hcs
    have hx := hS hcore x (by rw [hP3]; simp)
    have hy := hS hcore y (by rw [hP3]; simp)
    have hz := hS hcore z (by rw [hP3]; simp)
    refine ⟨x, y, z, hxy, hyz, hxz, hP3, by rw [bondsBetween_eq M hx hy]; exact hm, ?_⟩
    rw [bondsBetween_eq M hy hz, bondsBetween_eq M hx hz]; exact hcase
  · rw [pieces_eq] at hP
    obtain ⟨a, b, hab, he, hm⟩ := hrest P hP hne
    have ha := hS hP a (by rw [he]; simp)
    have hb := hS hP b (by rw [he]; simp)
    exact ⟨a, b, hab, he, by rw [bondsBetween_eq M ha hb]; exact hm⟩
  · rw [pieces_eq]
    have hsum := sum_card_pieces (groupGraph M S) j₁ j₂
    rw [← Finset.add_sum_erase _ _ hcore] at hsum
    have hc3 : core.card = 3 := by
      obtain ⟨x, y, z, hxy, hyz, hxz, hP3, -⟩ := hcs
      rw [hP3, Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩]
    have hc2 : ∀ P ∈ (piecesU (groupGraph M S) j₁ j₂).erase core, P.card = 2 := by
      intro P hP
      obtain ⟨hne, hP⟩ := Finset.mem_erase.mp hP
      obtain ⟨a, b, hab, rfl, -⟩ := hrest P hP hne
      exact Finset.card_pair hab
    rw [Finset.sum_congr rfl hc2, Finset.sum_const, smul_eq_mul, hc3,
      Finset.card_erase_of_mem hcore] at hsum
    have hint : (Core.interior (groupGraph M S) j₁ j₂).card = S.card - 2 := by
      unfold Core.interior
      rw [groupGraph_verts, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hB.2.2.2.1.symm, hB.2.2.1⟩),
        Finset.card_erase_of_mem hB.2.1]
      omega
    have hS2 : 2 ≤ S.card := by
      have := Finset.card_le_card (Finset.insert_subset hB.2.1 (Finset.singleton_subset_iff.mpr hB.2.2.1))
      rw [Finset.card_pair hB.2.2.2.1] at this; exact this
    have hpos : 1 ≤ (piecesU (groupGraph M S) j₁ j₂).card := Finset.card_pos.mpr ⟨core, hcore⟩
    omega

end mol

end WaveTurbulence.TVine.Struct
