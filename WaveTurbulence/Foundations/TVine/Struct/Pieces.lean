/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.RungDel
public import WaveTurbulence.Foundations.TVine.Struct.Thm6
import Mathlib.Tactic

/-!
# N2 Proposition 1.17 (pieces under deletion; the piece-shape theorem) (packet L3)

* `sep_drop`, `sep_lift`, `samePieceU_del_iff`: deleting a 2-cut rung `R` does not change which pole atoms lie in one
  piece (N2 Prop 1.17(a), proof by cuts: N2 L484–L503);
* `rung_piece`, `mem_piecesU_del`, `piece_del_cases`, `mult_del_piece`: `pieces(G/R) = pieces(G) ∖ {R}` with the same
  internal bonds;
* `pieceShapeU_of_del`: the piece shape lifts from `G/R` to `G`;
* named input `DeleteRungInput` (N2 Lemma 1.9(1), owner L1); the base is L2's `Checker.PieceShapeBaseStatement`;
* **`pieceShapeU_of_isTVineU`** (induction on size) and **`pieceShape : PieceShapeStatement`** (given the two inputs).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

universe u v

section split

variable {V : Type*} [DecidableEq V] {w : V → V → ℕ}

theorem eW_split2_left {X A B : Finset V} (hX : X ⊆ A ∪ B) (hAB : Disjoint A B) (Z : Finset V) :
    eW w X Z = eW w (X ∩ A) Z + eW w (X ∩ B) Z := by
  have h : X = (X ∩ A) ∪ (X ∩ B) := by rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hX]
  have hd : Disjoint (X ∩ A) (X ∩ B) := hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  calc eW w X Z = eW w ((X ∩ A) ∪ (X ∩ B)) Z := congrArg (fun T => eW w T Z) h
    _ = _ := eW_union_left Z hd

theorem eW_split3_left {X A B C : Finset V} (hX : X ⊆ A ∪ B ∪ C) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (Z : Finset V) :
    eW w X Z = eW w (X ∩ A) Z + eW w (X ∩ B) Z + eW w (X ∩ C) Z := by
  rw [eW_split2_left hX (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩) Z,
    eW_split2_left (X := X ∩ (A ∪ B)) Finset.inter_subset_right hAB Z]
  rw [Finset.inter_assoc, Finset.inter_assoc, Finset.inter_eq_right.mpr Finset.subset_union_left,
    Finset.inter_eq_right.mpr Finset.subset_union_right]

theorem ind_and_le_left (p q : Prop) [Decidable p] [Decidable q] : ind (p ∧ q) ≤ ind p := by
  unfold ind; split_ifs <;> simp_all

theorem ind_and_le_right (p q : Prop) [Decidable p] [Decidable q] : ind (p ∧ q) ≤ ind q := by
  unfold ind; split_ifs <;> simp_all

end split

section rung

variable {V : Type*} [DecidableEq V] {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

namespace RungFacts

variable (hR : IsRungAt G a b xm xp ym yp Km Kp)
include hR

/-- The weight between a subset of a pole and the rest of that pole is positive when both are nonempty. -/
theorem eW_pole_pos {K A : Finset V} (hK : ConnOn G K) (hA : A ⊆ K) {x y : V} (hx : x ∈ A) (hy : y ∈ K)
    (hyA : y ∉ A) : 1 ≤ eW (wG G) A (K \ A) := by
  have h := cutW_pos (w := wG G) hA ((connOn_iff_connW G K).mp hK) hx hy hyA
  rw [cutW_eq_eW _ hA] at h
  exact h

/-- The decomposition of a `G'`-cut of a set of pole atoms. -/
theorem cut_del_decomp {X : Finset V} (hX : X ⊆ Km ∪ Kp) :
    cut (rungDel G a b xm xp ym yp true) X =
      eW (wG G) (X ∩ Km) (Km \ X) + eW (wG G) (X ∩ Kp) (Kp \ X) +
        (ind (xm ∈ X ∩ Km ∧ yp ∈ Kp \ X) + ind (ym ∈ X ∩ Km ∧ xp ∈ Kp \ X)) +
        (ind (xm ∈ Km \ X ∧ yp ∈ X ∩ Kp) + ind (ym ∈ Km \ X ∧ xp ∈ X ∩ Kp)) := by
  rw [cut_eq_eW, verts_del hR]
  have hd0 : Disjoint Km Kp := hR.disj
  have hd2 : Disjoint (Km \ X) (Kp \ X) :=
    Finset.disjoint_left.mpr fun x h1 h2 => not_mem_both hR (Finset.mem_sdiff.mp h1).1 (Finset.mem_sdiff.mp h2).1
  rw [Finset.union_sdiff_distrib, eW_split2_left hX hd0, eW_union_right _ hd2, eW_union_right _ hd2]
  rw [eW_del_same hR (Or.inl ⟨Finset.inter_subset_right, Finset.sdiff_subset⟩),
    eW_del_same hR (Or.inr ⟨Finset.inter_subset_right, Finset.sdiff_subset⟩),
    eW_del_cross hR Finset.inter_subset_right Finset.sdiff_subset,
    eW_comm (symm_wG _) (X ∩ Kp) (Km \ X), eW_del_cross hR Finset.sdiff_subset Finset.inter_subset_right]
  ring

/-- The decomposition of a `G`-cut of a set containing the rung. -/
theorem cut_in_decomp {X : Finset V} (hX : X ⊆ G.verts) (ha : a ∈ X) (hb : b ∈ X) :
    cut G X = eW (wG G) (X ∩ Km) (Km \ X) + eW (wG G) (X ∩ Kp) (Kp \ X) +
      (ind (xm ∈ Km \ X) + ind (ym ∈ Km \ X)) + (ind (xp ∈ Kp \ X) + ind (yp ∈ Kp \ X)) := by
  rw [cut_eq_eW]
  have hXsub : X ⊆ Km ∪ Kp ∪ {a, b} := fun x hx => (verts_eq hR) ▸ hX hx
  have hab : X ∩ {a, b} = {a, b} := Finset.inter_eq_right.mpr (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb))
  have hCs : G.verts \ X = (Km \ X) ∪ (Kp \ X) := by
    rw [verts_eq hR]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(h | h) | h | h, hx⟩
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
      · exact absurd (h ▸ ha) hx
      · exact absurd (h ▸ hb) hx
    · rintro (⟨h, hx⟩ | ⟨h, hx⟩)
      · exact ⟨Or.inl (Or.inl h), hx⟩
      · exact ⟨Or.inl (Or.inr h), hx⟩
  have hKmab : Disjoint Km {a, b} := by
    rw [Finset.disjoint_left]; intro x hx h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact (a_not_pole hR).1 hx
    · exact (b_not_pole hR).1 hx
  have hKpab : Disjoint Kp {a, b} := by
    rw [Finset.disjoint_left]; intro x hx h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact (a_not_pole hR).2 hx
    · exact (b_not_pole hR).2 hx
  have hd3 : Disjoint (Km \ X) (Kp \ X) :=
    Finset.disjoint_left.mpr fun x h1 h2 => not_mem_both hR (Finset.mem_sdiff.mp h1).1 (Finset.mem_sdiff.mp h2).1
  rw [hCs, eW_split3_left hXsub hR.disj hKmab hKpab, hab, eW_union_right _ hd3, eW_union_right _ hd3,
    eW_union_right _ hd3,
    eW_zero_cross hR Finset.inter_subset_right Finset.sdiff_subset,
    eW_comm (symm_wG G) (X ∩ Kp) (Km \ X), eW_zero_cross hR Finset.sdiff_subset Finset.inter_subset_right,
    eW_comm (symm_wG G) {a, b} (Km \ X), eW_comm (symm_wG G) {a, b} (Kp \ X),
    eW_rails_m hR Finset.sdiff_subset, eW_rails_p hR Finset.sdiff_subset]
  ring

/-- The decomposition of a `G`-cut of a set avoiding the rung. -/
theorem cut_out_decomp {X : Finset V} (hX : X ⊆ Km ∪ Kp) :
    cut G X = eW (wG G) (X ∩ Km) (Km \ X) + eW (wG G) (X ∩ Kp) (Kp \ X) +
      (ind (xm ∈ X ∩ Km) + ind (ym ∈ X ∩ Km)) + (ind (xp ∈ X ∩ Kp) + ind (yp ∈ X ∩ Kp)) := by
  rw [cut_eq_eW]
  have hCs : G.verts \ X = (Km \ X) ∪ ((Kp \ X) ∪ {a, b}) := by
    rw [verts_eq hR]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(h | h) | h | h, hx⟩
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (Or.inl ⟨h, hx⟩)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rintro (⟨h, hx⟩ | ⟨h, hx⟩ | rfl | rfl)
      · exact ⟨Or.inl (Or.inl h), hx⟩
      · exact ⟨Or.inl (Or.inr h), hx⟩
      · exact ⟨Or.inr (Or.inl rfl), fun h => (Finset.mem_union.mp (hX h)).elim (a_not_pole hR).1 (a_not_pole hR).2⟩
      · exact ⟨Or.inr (Or.inr rfl), fun h => (Finset.mem_union.mp (hX h)).elim (b_not_pole hR).1 (b_not_pole hR).2⟩
  have hd1 : Disjoint (X ∩ Km) (X ∩ Kp) :=
    Finset.disjoint_left.mpr fun x h1 h2 => not_mem_both hR (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
  have hd2 : Disjoint (Km \ X) ((Kp \ X) ∪ {a, b}) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h2 with h | rfl | rfl
    · exact not_mem_both hR h1.1 h.1
    · exact (a_not_pole hR).1 h1.1
    · exact (b_not_pole hR).1 h1.1
  have hd3 : Disjoint (Kp \ X) {a, b} := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h2 with rfl | rfl
    · exact (a_not_pole hR).2 h1.1
    · exact (b_not_pole hR).2 h1.1
  rw [hCs, eW_split2_left hX hR.disj, eW_union_right _ hd2, eW_union_right _ hd3, eW_union_right _ hd2,
    eW_union_right _ hd3,
    eW_zero_cross hR Finset.inter_subset_right Finset.sdiff_subset,
    eW_comm (symm_wG G) (X ∩ Kp) (Km \ X), eW_zero_cross hR Finset.sdiff_subset Finset.inter_subset_right,
    eW_rails_m hR Finset.inter_subset_right, eW_rails_p hR Finset.inter_subset_right]
  ring

/-- **The rung atoms are on one side of every side with cut `≤ 2`.** -/
theorem ab_together {X : Finset V} (hX : X ⊆ G.verts) (hcut : cut G X ≤ 2) : (a ∈ X ↔ b ∈ X) := by
  -- if exactly one rung atom lies in `X`, the two rung bonds already exhaust the cut; then a pole is inside `X`, and
  -- the other rung atom's rail into it crosses
  have key : ∀ {c d xc yd : V}, c ∈ X → d ∉ X → G.mult s(c, d) = 2 → G.mult s(c, xc) = 1 → xc ∈ Km →
      G.mult s(d, yd) = 1 → yd ∈ Km → c ∉ Km → False := by
    intro c d xc yd hc hd hcd hcx hxc hdy hyd hcK
    have hdV : d ∈ G.verts := by
      by_contra h; have := mult_eq_zero_of_right G h c; omega
    have hsplit : cut G X = eW (wG G) {c} (G.verts \ X) + eW (wG G) (X.erase c) (G.verts \ X) := by
      rw [cut_eq_eW, ← eW_union_left _ (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase c X)),
        ← Finset.insert_eq, Finset.insert_erase hc]
    have hdc : 2 ≤ eW (wG G) {c} (G.verts \ X) := by
      have := le_eW_of_mem (w := wG G) (Finset.mem_singleton_self c) (Finset.mem_sdiff.mpr ⟨hdV, hd⟩)
      simp only [wG] at this; omega
    have hrest : eW (wG G) (X.erase c) (G.verts \ X) = 0 := by omega
    -- `xc ∈ X`
    have hxcX : xc ∈ X := by
      by_contra hxX
      have hxd : xc ≠ d := fun h => by rw [h] at hcx; omega
      have hsub : ({d, xc} : Finset V) ⊆ G.verts \ X := Finset.insert_subset (Finset.mem_sdiff.mpr ⟨hdV, hd⟩)
        (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨(pole_mem hR (Or.inl hxc)).1, hxX⟩))
      have h3 : eW (wG G) {c} {d, xc} ≤ eW (wG G) {c} (G.verts \ X) := eW_mono_right _ hsub
      have h4 : eW (wG G) {c} {d, xc} = G.mult s(c, d) + G.mult s(c, xc) := by
        unfold eW; rw [Finset.sum_singleton, Finset.sum_pair (Ne.symm hxd)]; rfl
      omega
    -- `Km ⊆ X`
    have hKmX : Km ⊆ X := by
      intro z hz
      by_contra hzX
      have h1 := eW_pole_pos hR hR.connm (A := Km ∩ X) Finset.inter_subset_left
        (Finset.mem_inter.mpr ⟨hxc, hxcX⟩) hz (fun h => hzX (Finset.mem_inter.mp h).2)
      have h2 : eW (wG G) (Km ∩ X) (Km \ (Km ∩ X)) ≤ eW (wG G) (X.erase c) (G.verts \ X) := by
        refine (eW_mono_left _ fun y hy => Finset.mem_erase.mpr ⟨fun h => hcK (by rw [← h]; exact (Finset.mem_inter.mp hy).1),
          (Finset.mem_inter.mp hy).2⟩).trans (eW_mono_right _ fun y hy => ?_)
        obtain ⟨hyK, hyn⟩ := Finset.mem_sdiff.mp hy
        exact Finset.mem_sdiff.mpr ⟨(pole_mem hR (Or.inl hyK)).1, fun h => hyn (Finset.mem_inter.mpr ⟨hyK, h⟩)⟩
      omega
    -- the rail `d – yd` crosses
    have hyX : yd ∈ X.erase c := Finset.mem_erase.mpr ⟨fun h => hcK (h ▸ hyd), hKmX hyd⟩
    have h1 := le_eW_of_mem (w := wG G) hyX (Finset.mem_sdiff.mpr ⟨hdV, hd⟩)
    simp only [wG] at h1
    rw [Sym2.eq_swap] at h1
    omega
  constructor
  · intro ha
    by_contra hb
    exact key ha hb hR.mult_ab hR.a_xm hR.xm_mem hR.b_ym hR.ym_mem (a_not_pole hR).1
  · intro hb
    by_contra ha
    exact key hb ha (by rw [Sym2.eq_swap]; exact hR.mult_ab) hR.b_ym hR.ym_mem hR.a_xm hR.xm_mem (b_not_pole hR).1

/-- **Dropping the rung from a side of `G`** keeps the cut `≤` in `G'`. -/
theorem sep_drop {X : Finset V} (hX : X ⊆ G.verts) (hcut : cut G X ≤ 2) :
    cut (rungDel G a b xm xp ym yp true) (X \ {a, b}) ≤ cut G X := by
  have hX' : X \ {a, b} ⊆ Km ∪ Kp := by
    intro x hx
    obtain ⟨hxX, hxab⟩ := Finset.mem_sdiff.mp hx
    have := (verts_eq hR) ▸ hX hxX
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this hxab ⊢
    tauto
  rw [cut_del_decomp hR hX']
  have hm : ∀ Y : Finset V, Y ⊆ Km → (X \ {a, b}) ∩ Y = X ∩ Y := fun Y hY => by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨h, fun h'' => h''.elim (fun e => (a_not_pole hR).1 (e ▸ hY h')) (fun e => (b_not_pole hR).1 (e ▸ hY h'))⟩, h'⟩
  have hp : ∀ Y : Finset V, Y ⊆ Kp → (X \ {a, b}) ∩ Y = X ∩ Y := fun Y hY => by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨h, fun h'' => h''.elim (fun e => (a_not_pole hR).2 (e ▸ hY h')) (fun e => (b_not_pole hR).2 (e ▸ hY h'))⟩, h'⟩
  have hm' : Km \ (X \ {a, b}) = Km \ X := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, fun hx => h' ⟨hx, fun e => e.elim (fun e => (a_not_pole hR).1 (e ▸ h))
        (fun e => (b_not_pole hR).1 (e ▸ h))⟩⟩
    · rintro ⟨h, h'⟩; exact ⟨h, fun hx => h' hx.1⟩
  have hp' : Kp \ (X \ {a, b}) = Kp \ X := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, fun hx => h' ⟨hx, fun e => e.elim (fun e => (a_not_pole hR).2 (e ▸ h))
        (fun e => (b_not_pole hR).2 (e ▸ h))⟩⟩
    · rintro ⟨h, h'⟩; exact ⟨h, fun hx => h' hx.1⟩
  rw [hm Km subset_rfl, hp Kp subset_rfl, hm', hp']
  by_cases ha : a ∈ X
  · have hb := (ab_together hR hX hcut).mp ha
    rw [cut_in_decomp hR hX ha hb]
    have h1 := ind_and_le_right (xm ∈ X ∩ Km) (yp ∈ Kp \ X)
    have h2 := ind_and_le_right (ym ∈ X ∩ Km) (xp ∈ Kp \ X)
    have h3 := ind_and_le_left (xm ∈ Km \ X) (yp ∈ X ∩ Kp)
    have h4 := ind_and_le_left (ym ∈ Km \ X) (xp ∈ X ∩ Kp)
    omega
  · have hb : b ∉ X := fun h => ha ((ab_together hR hX hcut).mpr h)
    have hXp : X ⊆ Km ∪ Kp := by
      intro x hx
      have := (verts_eq hR) ▸ hX hx
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with h | rfl | rfl
      · exact h
      · exact absurd hx ha
      · exact absurd hx hb
    rw [cut_out_decomp hR hXp]
    have h1 := ind_and_le_left (xm ∈ X ∩ Km) (yp ∈ Kp \ X)
    have h2 := ind_and_le_left (ym ∈ X ∩ Km) (xp ∈ Kp \ X)
    have h3 := ind_and_le_right (xm ∈ Km \ X) (yp ∈ X ∩ Kp)
    have h4 := ind_and_le_right (ym ∈ Km \ X) (xp ∈ X ∩ Kp)
    omega

end RungFacts

end rung

end WaveTurbulence.TVine.Struct
