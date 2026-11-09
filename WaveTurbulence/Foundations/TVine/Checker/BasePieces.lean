/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.PieceSides

/-!
# The piece-shape base statement (M4 §8 F2)

* `mem_piecesU_iff`: L1's pieces as `SamePieceU`-classes of the interior;
* `piece_iff`: the piece of an interior atom is the image of its checker piece `pieceOf`;
* `coreShape_of_ok`: `coreShapeOK` gives L1's `CoreShapeU`;
* `pieceShape_sound`: `pieceShapeB = true` on the instance gives the F2 conclusion for `G`;
* `pieceShapeBase : PieceShapeBaseStatement`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine WaveTurbulence.TVine.Core

universe u

theorem bool_beq_iff (a b : Bool) : a.beq b = true ↔ a = b := by cases a <;> cases b <;> decide

theorem mem_pieceOf {sides : List ℕ} {W u w : ℕ} :
    w ∈ pieceOf sides W u ↔ w ∈ elems W ∧ ∀ X ∈ sides, mem u X = mem w X := by
  unfold pieceOf
  rw [List.mem_filter, List.all_eq_true]
  simp only [bool_beq_iff]

theorem nodup_pieceOf (sides : List ℕ) (W u : ℕ) : (pieceOf sides W u).Nodup := (nodup_elems W).filter _

theorem pieceOK_cases {es : Edges} {l : List ℕ} (h : pieceOK es l = true) :
    (∃ x y, l = [x, y] ∧ (mult es x y = 1 ∨ mult es x y = 2)) ∨
      (∃ x y z, l = [x, y, z] ∧ coreShapeOK es x y z = true) :=
  match l, h with
  | [x, y], h => Or.inl ⟨x, y, rfl, by simpa [pieceOK] using h⟩
  | [x, y, z], h => Or.inr ⟨x, y, z, rfl, h⟩
  | [], h => by simp [pieceOK] at h
  | [_], h => by simp [pieceOK] at h
  | _ :: _ :: _ :: _ :: _, h => by simp [pieceOK] at h

variable {V : Type*} [DecidableEq V]

theorem mem_piecesU_iff {G : UMultigraph V} {j₁ j₂ : V} {P : Finset V} :
    P ∈ piecesU G j₁ j₂ ↔ ∃ v ∈ interior G j₁ j₂, ∀ x, x ∈ P ↔ x ∈ interior G j₁ j₂ ∧ SamePieceU G v x := by
  classical
  unfold piecesU
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, fun x => Finset.mem_filter⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, Finset.ext fun x => by rw [Finset.mem_filter, h]⟩

theorem coreShape_of_shapeAt {G : UMultigraph V} {es : Edges} (φ : Iso G es) {a b c : ℕ} (ha : InEnds es a)
    (hb : InEnds es b) (hc : InEnds es c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h : shapeAt es a b c = true) : CoreShapeU G {φ.g a, φ.g b, φ.g c} := by
  have inj : ∀ {x y}, InEnds es x → InEnds es y → x ≠ y → φ.g x ≠ φ.g y := fun hx hy hxy h' =>
    hxy (by rw [← φ.fg _ hx, h', φ.fg _ hy])
  refine ⟨φ.g a, φ.g b, φ.g c, inj ha hb hab, inj hb hc hbc, inj ha hc hac, rfl, ?_⟩
  rw [φ.mult_g ha hb, φ.mult_g hb hc, φ.mult_g ha hc]
  unfold shapeAt at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  tauto

theorem coreShape_of_ok {G : UMultigraph V} {es : Edges} (φ : Iso G es) {a b c : ℕ} (ha : InEnds es a)
    (hb : InEnds es b) (hc : InEnds es c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h : coreShapeOK es a b c = true) : CoreShapeU G {φ.g a, φ.g b, φ.g c} := by
  unfold coreShapeOK at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  · exact coreShape_of_shapeAt φ ha hb hc hab hbc hac h
  · have := coreShape_of_shapeAt φ hb hc ha (by omega) (by omega) (by omega) h
    rwa [show ({φ.g b, φ.g c, φ.g a} : Finset V) = {φ.g a, φ.g b, φ.g c} by ext; simp; tauto] at this
  · have := coreShape_of_shapeAt φ hc ha hb (by omega) (by omega) (by omega) h
    rwa [show ({φ.g c, φ.g a, φ.g b} : Finset V) = {φ.g a, φ.g b, φ.g c} by ext; simp; tauto] at this
  · have := coreShape_of_shapeAt φ ha hc hb (by omega) (by omega) (by omega) h
    rwa [show ({φ.g a, φ.g c, φ.g b} : Finset V) = {φ.g a, φ.g b, φ.g c} by ext; simp; tauto] at this
  · have := coreShape_of_shapeAt φ hc hb ha (by omega) (by omega) (by omega) h
    rwa [show ({φ.g c, φ.g b, φ.g a} : Finset V) = {φ.g a, φ.g b, φ.g c} by ext; simp; tauto] at this
  · have := coreShape_of_shapeAt φ hb ha hc (by omega) (by omega) (by omega) h
    rwa [show ({φ.g b, φ.g a, φ.g c} : Finset V) = {φ.g a, φ.g b, φ.g c} by ext; simp; tauto] at this

/-- The piece of an interior atom is the image of its checker piece. -/
theorem piece_iff {G : UMultigraph V} {es : Edges} (φ : Iso G es) {j₁ j₂ : V} {J : ℕ}
    (hJ : JointsAt φ j₁ j₂ J) (hj₁ : j₁ ∈ G.verts) (hj₂ : j₂ ∈ G.verts) (hlt : ∀ z, InEnds es z → z < 32)
    {sides : List ℕ} (hs : allSides (maskOf es) es = some sides) {v : V} (hv : v ∈ interior G j₁ j₂) (x : V) :
    (x ∈ interior G j₁ j₂ ∧ SamePieceU G v x) ↔
      x ∈ (pieceOf sides (sdiff (maskOf es) (bit J ||| bit (J + 1))) (φ.f v)).toFinset.image φ.g := by
  obtain ⟨hI1, hI2⟩ := mem_interior_iff φ hJ hj₁ hj₂
  have hintG : ∀ y ∈ interior G j₁ j₂, y ∈ G.verts := fun y hy => by
    simp only [Core.interior, Finset.mem_erase] at hy; exact hy.2.2
  have hvG := hintG v hv
  have hfv := φ.fv v hvG
  rw [Finset.mem_image]
  constructor
  · rintro ⟨hx, hsp⟩
    have hxG := hintG x hx
    have hfx := φ.fv x hxG
    refine ⟨φ.f x, List.mem_toFinset.mpr (mem_pieceOf.mpr ⟨mem_elems.mpr ⟨hlt _ hfx, hI1 x hx⟩, ?_⟩),
      φ.gf x hxG⟩
    intro X hX
    by_contra hne
    have := not_samePiece_of_side φ hs hfv hfx (hlt _ hfv) (hlt _ hfx) hX hne
    rw [φ.gf v hvG, φ.gf x hxG] at this
    exact this hsp
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzW, hsame⟩ := mem_pieceOf.mp (List.mem_toFinset.mp hz)
    obtain ⟨hz32, hzm⟩ := mem_elems.mp hzW
    have hzV : mem z (maskOf es) = true := by
      rw [mem_sdiff, Bool.and_eq_true] at hzm; exact hzm.1
    have hze := mem_maskOf.mp hzV
    refine ⟨hI2 z hze hzm, ?_⟩
    have := samePiece_of_sides φ hs hfv hze (hlt _ hfv) hz32 hsame
    rwa [φ.gf v hvG] at this

/-- **F2 soundness.** -/
theorem pieceShape_sound {G : UMultigraph V} {es : Edges} (φ : Iso G es) {j₁ j₂ : V} {J : ℕ}
    (hJ : JointsAt φ j₁ j₂ J) (hj₁ : j₁ ∈ G.verts) (hj₂ : j₂ ∈ G.verts) (hlt : ∀ z, InEnds es z → z < 32)
    (hb : pieceShapeB (maskOf es) es J (J + 1) = true) :
    ∃ core ∈ piecesU G j₁ j₂, CoreShapeU G core ∧ ∀ P ∈ piecesU G j₁ j₂, P ≠ core → TwoAtomPieceU G P := by
  obtain ⟨hI1, hI2⟩ := mem_interior_iff φ hJ hj₁ hj₂
  unfold pieceShapeB at hb
  split at hb
  next => simp at hb
  next sides hs =>
  simp only at hb
  split at hb
  next => simp at hb
  next c hc =>
  set Wm := sdiff (maskOf es) (bit J ||| bit (J + 1)) with hWm
  have hall : ∀ l ∈ (elems Wm).map (pieceOf sides Wm), pieceOK es l = true ∧ (l.length ≠ 3 ∨ l = c) := by
    intro l hl
    have := List.all_eq_true.mp hb l hl
    simpa only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] using this
  have hclen : c.length = 3 := by simpa using List.find?_some hc
  obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hc)
  -- atoms of checker pieces
  have hatom : ∀ z ∈ elems Wm, InEnds es z ∧ φ.g z ∈ interior G j₁ j₂ := by
    intro z hz
    obtain ⟨-, hzm⟩ := mem_elems.mp hz
    have hzV : mem z (maskOf es) = true := by
      rw [mem_sdiff, Bool.and_eq_true] at hzm; exact hzm.1
    exact ⟨mem_maskOf.mp hzV, hI2 z (mem_maskOf.mp hzV) hzm⟩
  -- every piece is the image of a checker piece
  have hpiece : ∀ P ∈ piecesU G j₁ j₂, ∃ z ∈ elems Wm, P = (pieceOf sides Wm z).toFinset.image φ.g := by
    intro P hP
    obtain ⟨v, hv, hPv⟩ := mem_piecesU_iff.mp hP
    have hvG : v ∈ G.verts := by simp only [Core.interior, Finset.mem_erase] at hv; exact hv.2.2
    refine ⟨φ.f v, mem_elems.mpr ⟨hlt _ (φ.fv v hvG), hI1 v hv⟩, Finset.ext fun x => ?_⟩
    rw [hPv, piece_iff φ hJ hj₁ hj₂ hlt hs hv x]
  have hcore_mem : (pieceOf sides Wm u₀).toFinset.image φ.g ∈ piecesU G j₁ j₂ := by
    obtain ⟨hu₀e, hu₀I⟩ := hatom u₀ hu₀
    refine mem_piecesU_iff.mpr ⟨φ.g u₀, hu₀I, fun x => ?_⟩
    rw [piece_iff φ hJ hj₁ hj₂ hlt hs hu₀I x, φ.fg u₀ hu₀e]
  refine ⟨_, hcore_mem, ?_, ?_⟩
  · -- the core shape
    obtain ⟨hok, -⟩ := hall _ (List.mem_map_of_mem hu₀)
    rcases pieceOK_cases hok with ⟨x, y, hl, -⟩ | ⟨x, y, z, hl, hsh⟩
    · rw [hl] at hclen; simp at hclen
    · have hnd := nodup_pieceOf sides Wm u₀
      rw [hl] at hnd
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true] at hnd
      have hmem : ∀ w ∈ pieceOf sides Wm u₀, InEnds es w := fun w hw =>
        (hatom w (mem_pieceOf.mp hw).1).1
      rw [hl] at hmem ⊢
      have hx := hmem x (by simp)
      have hy := hmem y (by simp)
      have hz := hmem z (by simp)
      have := coreShape_of_ok φ hx hy hz (fun h => hnd.1 (Or.inl h)) (fun h => hnd.2.1 h)
        (fun h => hnd.1 (Or.inr h)) hsh
      simpa using this
  · -- the other pieces
    intro P hP hne
    obtain ⟨w, hw, rfl⟩ := hpiece P hP
    obtain ⟨hok, hlen⟩ := hall _ (List.mem_map_of_mem hw)
    rcases hlen with hlen | heq
    · rcases pieceOK_cases hok with ⟨x, y, hl, hm⟩ | ⟨x, y, z, hl, -⟩
      · have hnd := nodup_pieceOf sides Wm w
        rw [hl] at hnd
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true] at hnd
        have hmem : ∀ v ∈ pieceOf sides Wm w, InEnds es v := fun v hv =>
          (hatom v (mem_pieceOf.mp hv).1).1
        rw [hl] at hmem ⊢
        have hx := hmem x (by simp)
        have hy := hmem y (by simp)
        refine ⟨φ.g x, φ.g y, fun h => hnd.1 (by rw [← φ.fg x hx, h, φ.fg y hy]), by simp, ?_⟩
        rw [φ.mult_g hx hy]
        exact hm
      · rw [hl] at hlen; simp at hlen
    · exact absurd (by rw [heq]) hne

/-- **F2 (base of N2 Prop 1.17(b)).** -/
theorem pieceShapeBase : PieceShapeBaseStatement.{u} := by
  intro V _ G j₁ j₂ hT hcard
  obtain ⟨q, hq, φ, hJ⟩ := exists_inst_of_card hT hcard
  obtain ⟨-, hends, hpieces, -, -, -⟩ := checkInst_facts (checkInst_of_mem hq)
  exact pieceShape_sound φ hJ hT.1.1 hT.1.2.1 (fun z hz => lt_of_endsLt hends hz) hpieces

end WaveTurbulence.TVine.Checker
