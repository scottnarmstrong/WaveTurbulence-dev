/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Pieces
import Mathlib.Tactic

/-!
# N2 Proposition 1.17 (continued): the lift of separating sides, pieces under deletion, the piece-shape theorem

* `sep_lift` (N2 L489–L499 in cut form): a side of `G/R` with cut `≤ 2` separating two pole atoms gives one of `G`;
* `samePieceU_del_iff`, `rung_piece`, `mem_piecesU_of_del`, `piece_del_cases`, `mult_del_piece` (N2 Prop 1.17(a));
* `pieceShapeU_of_del`; named input `DeleteRungInput` (L1); base from L2 (`Checker.PieceShapeBaseStatement`, `Checker.SizeBoundStatement`);
* **`pieceShapeU_of_isTVineU`**, **`pieceShape : PieceShapeStatement`** (N2 Prop 1.17(b)).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

universe u v

section helpers

variable {V : Type*} [DecidableEq V]

theorem sdiff_inter_self (K X : Finset V) : K \ (X ∩ K) = K \ X := by
  ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto

theorem ind_true {p : Prop} [Decidable p] (h : p) : ind p = 1 := by unfold ind; simp [h]

theorem ind_false {p : Prop} [Decidable p] (h : ¬ p) : ind p = 0 := by unfold ind; simp [h]

theorem ind_le_one (p : Prop) [Decidable p] : ind p ≤ 1 := by unfold ind; split_ifs <;> omega

end helpers

section rung

variable {V : Type*} [DecidableEq V] {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

namespace RungFacts

variable (hR : IsRungAt G a b xm xp ym yp Km Kp)
include hR

theorem cut_Km : cut G Km = 2 := by
  rw [cut_sub_m hR subset_rfl, Finset.sdiff_self, eW_empty_right, ind_true hR.xm_mem, ind_true hR.ym_mem]

theorem cut_Kp : cut G Kp = 2 := by
  rw [cut_sub_p hR subset_rfl, Finset.sdiff_self, eW_empty_right, ind_true hR.xp_mem, ind_true hR.yp_mem]

/-- **The lift of a separating side of `G/R`** (N2 Prop 1.17(a), "Conversely"). -/
theorem sep_lift (hC : CutCtx G) {X : Finset V} (hX : X ⊆ Km ∪ Kp)
    (hcut : cut (rungDel G a b xm xp ym yp true) X ≤ 2) {u w : V} (hu : u ∈ X) (hw : w ∈ Km ∪ Kp) (hwX : w ∉ X) :
    ∃ Y ⊆ G.verts, cut G Y ≤ 2 ∧ (u ∈ Y ↔ w ∉ Y) := by
  rw [cut_del_decomp hR hX] at hcut
  have hKmV : Km ⊆ G.verts := fun x hx => (pole_mem hR (Or.inl hx)).1
  have hKpV : Kp ⊆ G.verts := fun x hx => (pole_mem hR (Or.inr hx)).1
  have hAm : X ∩ Km ⊆ Km := Finset.inter_subset_right
  have hCp : X ∩ Kp ⊆ Kp := Finset.inter_subset_right
  have hcA := cut_sub_m hR hAm
  have hcC := cut_sub_p hR hCp
  rw [sdiff_inter_self] at hcA hcC
  have hpar : ∀ Y ⊆ G.verts, Even (cut G Y) := fun Y hY => cut_even hC hY
  have huKK : u ∈ Km ∨ u ∈ Kp := Finset.mem_union.mp (hX hu)
  have hwKK : w ∈ Km ∨ w ∈ Kp := Finset.mem_union.mp hw
  by_cases hKm : (X ∩ Km).Nonempty ∧ (Km \ X).Nonempty
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hKm
    have hAB : 1 ≤ eW (wG G) (X ∩ Km) (Km \ X) := by
      have := eW_pole_pos hR hR.connm hAm hx (Finset.mem_sdiff.mp hy).1
        (fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp h).1)
      rwa [sdiff_inter_self] at this
    by_cases hKp : (X ∩ Kp).Nonempty ∧ (Kp \ X).Nonempty
    · -- both poles split: every part has cut 2 (parity)
      obtain ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ := hKp
      have hCE : 1 ≤ eW (wG G) (X ∩ Kp) (Kp \ X) := by
        have := eW_pole_pos hR hR.connp hCp hx' (Finset.mem_sdiff.mp hy').1
          (fun h => (Finset.mem_sdiff.mp hy').2 (Finset.mem_inter.mp h).1)
        rwa [sdiff_inter_self] at this
      have h1 := ind_le_one (xm ∈ X ∩ Km); have h2 := ind_le_one (ym ∈ X ∩ Km)
      have h3 := ind_le_one (xp ∈ X ∩ Kp); have h4 := ind_le_one (yp ∈ X ∩ Kp)
      have hpA := hpar _ (hAm.trans hKmV)
      have hpC := hpar _ (hCp.trans hKpV)
      have hA2 : cut G (X ∩ Km) ≤ 2 := by obtain ⟨k, hk⟩ := hpA; omega
      have hC2 : cut G (X ∩ Kp) ≤ 2 := by obtain ⟨k, hk⟩ := hpC; omega
      rcases huKK with hum | hup
      · refine ⟨X ∩ Km, hAm.trans hKmV, hA2, ⟨fun _ h => hwX (Finset.mem_inter.mp h).1, fun _ => ?_⟩⟩
        exact Finset.mem_inter.mpr ⟨hu, hum⟩
      · refine ⟨X ∩ Kp, hCp.trans hKpV, hC2, ⟨fun _ h => hwX (Finset.mem_inter.mp h).1, fun _ => ?_⟩⟩
        exact Finset.mem_inter.mpr ⟨hu, hup⟩
    · -- only `Km` split
      have hCE : X ∩ Kp = ∅ ∨ Kp \ X = ∅ := by
        rw [not_and_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at hKp; exact hKp
      rcases hCE with hC0 | hE0
      · -- `Y = X ∩ Km = X`
        have hyp : yp ∈ Kp \ X := Finset.mem_sdiff.mpr ⟨hR.yp_mem, fun h =>
          (Finset.eq_empty_iff_forall_notMem.mp hC0) yp (Finset.mem_inter.mpr ⟨h, hR.yp_mem⟩)⟩
        have hxp : xp ∈ Kp \ X := Finset.mem_sdiff.mpr ⟨hR.xp_mem, fun h =>
          (Finset.eq_empty_iff_forall_notMem.mp hC0) xp (Finset.mem_inter.mpr ⟨h, hR.xp_mem⟩)⟩
        have e1 : ind (xm ∈ X ∩ Km ∧ yp ∈ Kp \ X) = ind (xm ∈ X ∩ Km) := by unfold ind; simp [hyp]
        have e2 : ind (ym ∈ X ∩ Km ∧ xp ∈ Kp \ X) = ind (ym ∈ X ∩ Km) := by unfold ind; simp [hxp]
        refine ⟨X ∩ Km, hAm.trans hKmV, by omega, ⟨fun _ h => hwX (Finset.mem_inter.mp h).1, fun _ => ?_⟩⟩
        rcases huKK with hum | hup
        · exact Finset.mem_inter.mpr ⟨hu, hum⟩
        · exact absurd (Finset.mem_inter.mpr ⟨hu, hup⟩) (by rw [hC0]; exact Finset.notMem_empty _)
      · -- `Y = Km ∖ X`
        have hKpX : Kp ⊆ X := Finset.sdiff_eq_empty_iff_subset.mp hE0
        have hcB := cut_sub_m hR (A := Km \ X) Finset.sdiff_subset
        have hset : Km \ (Km \ X) = X ∩ Km := by ext z; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
        rw [hset, eW_comm (symm_wG G)] at hcB
        have e1 : ind (xm ∈ Km \ X ∧ yp ∈ X ∩ Kp) = ind (xm ∈ Km \ X) := by
          unfold ind; simp [Finset.mem_inter.mpr ⟨hKpX hR.yp_mem, hR.yp_mem⟩]
        have e2 : ind (ym ∈ Km \ X ∧ xp ∈ X ∩ Kp) = ind (ym ∈ Km \ X) := by
          unfold ind; simp [Finset.mem_inter.mpr ⟨hKpX hR.xp_mem, hR.xp_mem⟩]
        refine ⟨Km \ X, Finset.sdiff_subset.trans hKmV, by omega, ⟨fun h => absurd hu (Finset.mem_sdiff.mp h).2,
          fun h => absurd ?_ h⟩⟩
        rcases hwKK with hwm | hwp
        · exact Finset.mem_sdiff.mpr ⟨hwm, hwX⟩
        · exact absurd (hKpX hwp) hwX
  · by_cases hKp : (X ∩ Kp).Nonempty ∧ (Kp \ X).Nonempty
    · -- only `Kp` split
      obtain ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ := hKp
      have hAB : X ∩ Km = ∅ ∨ Km \ X = ∅ := by
        rw [not_and_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at hKm; exact hKm
      rcases hAB with hA0 | hB0
      · have hxm : xm ∈ Km \ X := Finset.mem_sdiff.mpr ⟨hR.xm_mem, fun h =>
          (Finset.eq_empty_iff_forall_notMem.mp hA0) xm (Finset.mem_inter.mpr ⟨h, hR.xm_mem⟩)⟩
        have hym : ym ∈ Km \ X := Finset.mem_sdiff.mpr ⟨hR.ym_mem, fun h =>
          (Finset.eq_empty_iff_forall_notMem.mp hA0) ym (Finset.mem_inter.mpr ⟨h, hR.ym_mem⟩)⟩
        have e1 : ind (xm ∈ Km \ X ∧ yp ∈ X ∩ Kp) = ind (yp ∈ X ∩ Kp) := by unfold ind; simp [hxm]
        have e2 : ind (ym ∈ Km \ X ∧ xp ∈ X ∩ Kp) = ind (xp ∈ X ∩ Kp) := by unfold ind; simp [hym]
        refine ⟨X ∩ Kp, hCp.trans hKpV, by omega, ⟨fun _ h => hwX (Finset.mem_inter.mp h).1, fun _ => ?_⟩⟩
        rcases huKK with hum | hup
        · exact absurd (Finset.mem_inter.mpr ⟨hu, hum⟩) (by rw [hA0]; exact Finset.notMem_empty _)
        · exact Finset.mem_inter.mpr ⟨hu, hup⟩
      · have hKmX : Km ⊆ X := Finset.sdiff_eq_empty_iff_subset.mp hB0
        have hcE := cut_sub_p hR (A := Kp \ X) Finset.sdiff_subset
        have hset : Kp \ (Kp \ X) = X ∩ Kp := by ext z; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
        rw [hset, eW_comm (symm_wG G)] at hcE
        have e1 : ind (xm ∈ X ∩ Km ∧ yp ∈ Kp \ X) = ind (yp ∈ Kp \ X) := by
          unfold ind; simp [Finset.mem_inter.mpr ⟨hKmX hR.xm_mem, hR.xm_mem⟩]
        have e2 : ind (ym ∈ X ∩ Km ∧ xp ∈ Kp \ X) = ind (xp ∈ Kp \ X) := by
          unfold ind; simp [Finset.mem_inter.mpr ⟨hKmX hR.ym_mem, hR.ym_mem⟩]
        refine ⟨Kp \ X, Finset.sdiff_subset.trans hKpV, by omega, ⟨fun h => absurd hu (Finset.mem_sdiff.mp h).2,
          fun h => absurd ?_ h⟩⟩
        rcases hwKK with hwm | hwp
        · exact absurd (hKmX hwm) hwX
        · exact Finset.mem_sdiff.mpr ⟨hwp, hwX⟩
    · -- no pole split: `X` is a pole
      have hAB : X ∩ Km = ∅ ∨ Km \ X = ∅ := by
        rw [not_and_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at hKm; exact hKm
      have hCE : X ∩ Kp = ∅ ∨ Kp \ X = ∅ := by
        rw [not_and_or, Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty] at hKp; exact hKp
      have hmem0 : ∀ {Y : Finset V} {z : V}, Y = ∅ → z ∉ Y := fun h => by rw [h]; exact Finset.notMem_empty _
      rcases huKK with hum | hup
      · -- `Km ⊆ X`, hence `X ∩ Kp = ∅`
        have hKmX : Km ⊆ X := by
          rcases hAB with h | h
          · exact absurd (Finset.mem_inter.mpr ⟨hu, hum⟩) (hmem0 h)
          · exact Finset.sdiff_eq_empty_iff_subset.mp h
        have hXKp : ∀ z ∈ Kp, z ∉ X := by
          rcases hCE with h | h
          · exact fun z hz hzX => hmem0 h (Finset.mem_inter.mpr ⟨hzX, hz⟩)
          · have hKpX := Finset.sdiff_eq_empty_iff_subset.mp h
            exfalso
            rcases hwKK with hwm | hwp
            · exact hwX (hKmX hwm)
            · exact hwX (hKpX hwp)
        refine ⟨Km, hKmV, (cut_Km hR).le, ⟨fun _ h => ?_, fun _ => hum⟩⟩
        exact hwX (hKmX h)
      · have hKpX : Kp ⊆ X := by
          rcases hCE with h | h
          · exact absurd (Finset.mem_inter.mpr ⟨hu, hup⟩) (hmem0 h)
          · exact Finset.sdiff_eq_empty_iff_subset.mp h
        refine ⟨Kp, hKpV, (cut_Kp hR).le, ⟨fun _ h => hwX (hKpX h), fun _ => hup⟩⟩

/-- **Pole atoms lie in one piece of `G` iff they lie in one piece of `G/R`.** -/
theorem samePieceU_del_iff (hC : CutCtx G) {u w : V} (hu : u ∈ Km ∪ Kp) (hw : w ∈ Km ∪ Kp) :
    SamePieceU G u w ↔ SamePieceU (rungDel G a b xm xp ym yp true) u w := by
  have hab : ∀ {z : V}, z ∈ Km ∪ Kp → z ≠ a ∧ z ≠ b := fun hz =>
    ⟨(pole_mem hR (Finset.mem_union.mp hz)).2.1, (pole_mem hR (Finset.mem_union.mp hz)).2.2⟩
  constructor
  · intro h X hX hcut
    rw [verts_del hR] at hX
    by_contra hne
    by_cases huX : u ∈ X
    · have hwX : w ∉ X := fun h' => hne ⟨fun _ => h', fun _ => huX⟩
      obtain ⟨Y, hY, hYc, hYs⟩ := sep_lift hR hC hX hcut huX hw hwX
      have := h Y hY hYc
      tauto
    · have hwX : w ∈ X := by by_contra h'; exact hne ⟨fun h'' => absurd h'' huX, fun h'' => absurd h'' h'⟩
      obtain ⟨Y, hY, hYc, hYs⟩ := sep_lift hR hC hX hcut hwX hu huX
      have := h Y hY hYc
      tauto
  · intro h X hX hcut
    have hX' : X \ {a, b} ⊆ (rungDel G a b xm xp ym yp true).verts := by
      rw [verts_del hR]
      intro x hx
      obtain ⟨hxX, hxab⟩ := Finset.mem_sdiff.mp hx
      have := (verts_eq hR) ▸ hX hxX
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this hxab ⊢
      tauto
    have := h (X \ {a, b}) hX' ((sep_drop hR hX hcut).trans hcut)
    have e : ∀ {z : V}, z ∈ Km ∪ Kp → (z ∈ X \ {a, b} ↔ z ∈ X) := fun hz => by
      have := hab hz
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
    rwa [e hu, e hw] at this

end RungFacts

end rung

end WaveTurbulence.TVine.Struct
