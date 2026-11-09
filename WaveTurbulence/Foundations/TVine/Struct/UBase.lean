/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Bridge
public import WaveTurbulence.Foundations.TVine.Struct.CutAlg
import Mathlib.Tactic

/-!
# U-level base for the structure theorems (packet L3)

Over L1's published U-layer (`TVine.Core`: `cut`, `deg`, `ConnOn`, `IsBlockU`, `IsTVineU`, `SamePieceU`, `piecesU`):

* `wG G`: the weight `mult s(·, ·)`; `cut_eq_cutW`, `connOn_iff_connW` (L1's `cut`/`ConnOn` are the generic
  `CutAlg.cutW`/`ConnW` of this weight);
* `loopless_of_isTVineU`: a T-vine has no loops;
* `CutCtx G`: symmetric, loop-free, connected, even degrees; `cutCtx_of_isTVineU`;
* the cut lemmas in L1's vocabulary: `cut_even`, `two_le_cut`, `connOn_of_cut_two`, `cut_union_disjoint`,
  `cut_compl`, `uncross_diff`, `uncross_inter_union`;
* pieces: `samePieceU_iff_cut_two`, `mem_piecesU_iff`, `mem_piecesU_of_class`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

variable {V : Type*} [DecidableEq V]

/-- The weight of a multigraph: `wG G u v = mult s(u, v)`. -/
def wG (G : UMultigraph V) : V → V → ℕ := fun u v => G.mult s(u, v)

theorem symm_wG (G : UMultigraph V) : Symm (wG G) := fun u v => by unfold wG; rw [Sym2.eq_swap]

theorem cut_eq_eW (G : UMultigraph V) (X : Finset V) : cut G X = eW (wG G) X (G.verts \ X) := rfl

theorem cut_eq_cutW (G : UMultigraph V) {X : Finset V} (hX : X ⊆ G.verts) :
    cut G X = cutW (wG G) G.verts X := by
  rw [cut_eq_eW, cutW_eq_eW _ hX]

theorem connOn_iff_connW (G : UMultigraph V) (X : Finset V) : ConnOn G X ↔ ConnW (wG G) X := Iff.rfl

theorem deg_eq_degW (G : UMultigraph V) (v : V) : deg G v = degW (wG G) G.verts v + G.mult s(v, v) := rfl

/-! ## T-vines are loop-free -/

private theorem joint_loop_aux {G : UMultigraph V} {j : V} (hj : j ∈ G.verts) (hdeg : deg G j = 2)
    (hpos : G.mult s(j, j) ≠ 0) : G.mult s(j, j) = 1 ∧ ∀ w ∈ G.verts, w ≠ j → G.mult s(j, w) = 0 := by
  have hsum : ∑ w ∈ G.verts, G.mult s(j, w) + G.mult s(j, j) = 2 := hdeg
  have hle : G.mult s(j, j) ≤ ∑ w ∈ G.verts, G.mult s(j, w) :=
    Finset.single_le_sum (f := fun w => G.mult s(j, w)) (fun _ _ => Nat.zero_le _) hj
  have h1 : G.mult s(j, j) = 1 := by omega
  refine ⟨h1, fun w hw hwj => ?_⟩
  have hsplit := Finset.sum_erase_add G.verts (fun w => G.mult s(j, w)) hj
  have hle2 : G.mult s(j, w) ≤ ∑ x ∈ G.verts.erase j, G.mult s(j, x) :=
    Finset.single_le_sum (f := fun x => G.mult s(j, x)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hwj, hw⟩)
  try simp only at hsplit
  omega

private theorem count_pair_two {a b j : V} (h : ({a, b} : Multiset V).count j = 2) : a = j ∧ b = j := by
  rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at h
  split_ifs at h with h1 h2 <;> first | exact ⟨h2.symm, h1.symm⟩ | omega

/-- **A T-vine has no loops.** Interior loops survive in the closure; a loop at a joint (which then has no other
bond) adds a loop to the closure. -/
theorem loopless_of_isTVineU {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) (v : V) :
    G.mult s(v, v) = 0 := by
  obtain ⟨hB, -, C, hC, -⟩ := h
  obtain ⟨h₁, h₂, hne, hd₁, hd₂, -, -⟩ := hB
  obtain ⟨-, -, hCl, added, hadd, hCm⟩ := hC
  by_contra hpos
  by_cases hv : v = j₁ ∨ v = j₂
  · -- the loop forces `nbrs G v = {v, v}`, and the closure inherits a loop
    have hcnt : ∀ j, j ∈ G.verts → deg G j = 2 → G.mult s(j, j) ≠ 0 → (nbrs G j).count j = 2 := by
      intro j hj hdj hpj
      obtain ⟨hj1, -⟩ := joint_loop_aux hj hdj hpj
      rw [count_nbrs, if_pos hj, if_pos rfl, hj1]
    have hloopC : ∀ j, added.count s(j, j) ≠ 0 → False := by
      intro j hj
      have := hCm s(j, j)
      have hl := hCl j
      omega
    rcases hv with hv | hv
    · rw [hv] at hpos
      obtain ⟨-, hzero⟩ := joint_loop_aux h₁ hd₁ hpos
      have hσ : G.mult s(j₁, j₂) = 0 := hzero j₂ h₂ (Ne.symm hne)
      rcases hadd with ⟨-, a, b, c, d, ha, -, hadd⟩ | ⟨hσ1, -⟩
      · have hc := hcnt j₁ h₁ hd₁ hpos
        rw [ha] at hc
        obtain ⟨haj, hbj⟩ := count_pair_two hc
        exact hloopC j₁ (by rw [hadd, haj, hbj]; simp)
      · omega
    · rw [hv] at hpos
      obtain ⟨-, hzero⟩ := joint_loop_aux h₂ hd₂ hpos
      have hσ : G.mult s(j₂, j₁) = 0 := hzero j₁ h₁ hne
      rw [Sym2.eq_swap] at hσ
      rcases hadd with ⟨-, a, b, c, d, -, hc', hadd⟩ | ⟨hσ1, -⟩
      · have hc := hcnt j₂ h₂ hd₂ hpos
        rw [hc'] at hc
        obtain ⟨hcj, hdj⟩ := count_pair_two hc
        exact hloopC j₂ (by rw [hadd, hcj, hdj]; simp)
      · omega
  · have hj : ¬ (j₁ ∈ s(v, v) ∨ j₂ ∈ s(v, v)) := by
      simp only [Sym2.mem_iff, or_self]; push Not at hv ⊢; exact ⟨Ne.symm hv.1, Ne.symm hv.2⟩
    have := hCm s(v, v)
    rw [if_neg hj] at this
    have hl := hCl v
    omega

/-! ## The cut context -/

/-- The standing facts used by all cut arguments: symmetric, loop-free, connected, all degrees even. -/
structure CutCtx (G : UMultigraph V) : Prop where
  loopless : Loopless (wG G)
  conn : ConnW (wG G) G.verts
  even : ∀ u ∈ G.verts, Even (degW (wG G) G.verts u)

theorem degW_eq_deg {G : UMultigraph V} (hl : Loopless (wG G)) (v : V) : degW (wG G) G.verts v = deg G v := by
  rw [deg_eq_degW]; have := hl v; unfold wG at this; omega

theorem cutCtx_of_isBlockU {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) (hl : ∀ v, G.mult s(v, v) = 0) :
    CutCtx G where
  loopless := hl
  conn := hB.2.2.2.2.2.2
  even := by
    intro u hu
    rw [degW_eq_deg hl]
    by_cases h1 : u = j₁
    · subst h1; rw [hB.2.2.2.1]; exact ⟨1, rfl⟩
    by_cases h2 : u = j₂
    · subst h2; rw [hB.2.2.2.2.1]; exact ⟨1, rfl⟩
    rw [hB.2.2.2.2.2.1 u hu h1 h2]; exact ⟨2, rfl⟩

theorem cutCtx_of_isTVineU {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) : CutCtx G :=
  cutCtx_of_isBlockU h.1 (loopless_of_isTVineU h)

/-! ## Cut lemmas in L1's vocabulary -/

section cuts

variable {G : UMultigraph V}

theorem cut_even (hC : CutCtx G) {X : Finset V} (hX : X ⊆ G.verts) : Even (cut G X) := by
  rw [cut_eq_cutW G hX]; exact cutW_even (symm_wG G) hC.loopless hX hC.even

theorem two_le_cut (hC : CutCtx G) {X : Finset V} (hX : X ⊆ G.verts) {u v : V} (hu : u ∈ X) (hv : v ∈ G.verts)
    (hvX : v ∉ X) : 2 ≤ cut G X := by
  rw [cut_eq_cutW G hX]; exact two_le_cutW (symm_wG G) hC.loopless hX hC.conn hC.even hu hv hvX

theorem connOn_of_cut_two (hC : CutCtx G) {X : Finset V} (hX : X ⊆ G.verts) (h2 : cut G X = 2) : ConnOn G X := by
  rw [cut_eq_cutW G hX] at h2; exact connW_of_cutW_two (symm_wG G) hC.loopless hX hC.conn hC.even h2

theorem cut_compl {X : Finset V} (hX : X ⊆ G.verts) : cut G (G.verts \ X) = cut G X := by
  rw [cut_eq_cutW G hX, cut_eq_cutW G Finset.sdiff_subset, cutW_compl (symm_wG G)]

theorem cut_union_disjoint {X Y : Finset V} (hX : X ⊆ G.verts) (hY : Y ⊆ G.verts) (hXY : Disjoint X Y) :
    cut G (X ∪ Y) + 2 * eW (wG G) X Y = cut G X + cut G Y := by
  rw [cut_eq_cutW G hX, cut_eq_cutW G hY, cut_eq_cutW G (Finset.union_subset hX hY)]
  exact cutW_union_disjoint (symm_wG G) hX hY hXY

theorem uncross_diff (hC : CutCtx G) {X Y : Finset V} (hX : X ⊆ G.verts) (hY : Y ⊆ G.verts) (hX2 : cut G X = 2)
    (hY2 : cut G Y = 2) {a b : V} (ha : a ∈ X) (haY : a ∉ Y) (hb : b ∈ Y) (hbX : b ∉ X) :
    cut G (X \ Y) = 2 ∧ cut G (Y \ X) = 2 := by
  rw [cut_eq_cutW G hX] at hX2; rw [cut_eq_cutW G hY] at hY2
  rw [cut_eq_cutW G (Finset.sdiff_subset.trans hX), cut_eq_cutW G (Finset.sdiff_subset.trans hY)]
  exact CutAlg.uncross_diff (symm_wG G) hC.loopless hX hY hC.conn hC.even hX2 hY2 ha haY hb hbX

theorem uncross_inter_union (hC : CutCtx G) {X Y : Finset V} (hX : X ⊆ G.verts) (hY : Y ⊆ G.verts)
    (hX2 : cut G X = 2) (hY2 : cut G Y = 2) {a b : V} (ha : a ∈ X ∩ Y) (hb : b ∈ G.verts) (hbXY : b ∉ X ∪ Y) :
    cut G (X ∩ Y) = 2 ∧ cut G (X ∪ Y) = 2 := by
  rw [cut_eq_cutW G hX] at hX2; rw [cut_eq_cutW G hY] at hY2
  rw [cut_eq_cutW G (Finset.inter_subset_left.trans hX), cut_eq_cutW G (Finset.union_subset hX hY)]
  exact CutAlg.uncross_inter_union (symm_wG G) hC.loopless hX hY hC.conn hC.even hX2 hY2 ha hb hbXY

/-- The cut of a single atom is its degree (no loops). -/
theorem cut_singleton (hC : CutCtx G) {v : V} (hv : v ∈ G.verts) : cut G {v} = deg G v := by
  rw [← degW_eq_deg hC.loopless, cut_eq_eW]
  unfold eW degW
  rw [Finset.sum_singleton]
  rw [← Finset.sum_erase_add G.verts _ hv]
  have : G.verts \ {v} = G.verts.erase v := by ext x; simp [and_comm]
  rw [this]
  have := hC.loopless v
  simp only [wG] at this ⊢
  rw [this, add_zero]

/-! ## Pieces through 2-cuts -/

/-- On a cut context, `SamePieceU` only needs the 2-cut sides. -/
theorem samePieceU_iff_cut_two (hC : CutCtx G) {u w : V} (hu : u ∈ G.verts) (hw : w ∈ G.verts) :
    SamePieceU G u w ↔ ∀ X ⊆ G.verts, cut G X = 2 → (u ∈ X ↔ w ∈ X) := by
  constructor
  · intro h X hX h2; exact h X hX h2.le
  · intro h X hX hle
    by_cases h2 : cut G X = 2
    · exact h X hX h2
    · -- the cut is `0`: `X` is empty or everything
      have hev := cut_even hC hX
      have h0 : cut G X = 0 := by obtain ⟨k, hk⟩ := hev; omega
      by_cases huX : u ∈ X <;> by_cases hwX : w ∈ X
      · exact ⟨fun _ => hwX, fun _ => huX⟩
      · exact absurd h0 (by have := two_le_cut hC hX huX hw hwX; omega)
      · exact absurd h0 (by have := two_le_cut hC hX hwX hu huX; omega)
      · exact ⟨fun h => absurd h huX, fun h => absurd h hwX⟩

theorem mem_piecesU_iff {j₁ j₂ : V} {P : Finset V} :
    P ∈ piecesU G j₁ j₂ ↔
      ∃ u ∈ Core.interior G j₁ j₂, ∀ w, w ∈ P ↔ w ∈ Core.interior G j₁ j₂ ∧ SamePieceU G u w := by
  classical
  unfold piecesU
  rw [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, fun w => by rw [Finset.mem_filter]⟩
  · rintro ⟨u, hu, hP⟩
    refine ⟨u, hu, ?_⟩
    ext w; rw [Finset.mem_filter, hP w]

/-- A nonempty subset of the interior whose atoms are pairwise in one piece and in no piece with any other interior
atom is a piece. -/
theorem mem_piecesU_of_class {j₁ j₂ : V} {P : Finset V} (hP : P ⊆ Core.interior G j₁ j₂) {u : V} (hu : u ∈ P)
    (hin : ∀ w ∈ P, SamePieceU G u w) (hout : ∀ w ∈ Core.interior G j₁ j₂, w ∉ P → ¬ SamePieceU G u w) :
    P ∈ piecesU G j₁ j₂ := by
  rw [mem_piecesU_iff]
  refine ⟨u, hP hu, fun w => ⟨fun hw => ⟨hP hw, hin w hw⟩, fun ⟨hw, hs⟩ => ?_⟩⟩
  by_contra hwP
  exact hout w hw hwP hs

theorem interior_subset_verts (j₁ j₂ : V) : Core.interior G j₁ j₂ ⊆ G.verts :=
  (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

theorem mem_interior {j₁ j₂ v : V} : v ∈ Core.interior G j₁ j₂ ↔ v ∈ G.verts ∧ v ≠ j₁ ∧ v ≠ j₂ := by
  unfold Core.interior; simp only [Finset.mem_erase]; tauto

/-- Every piece is a nonempty subset of the interior, closed under `SamePieceU`. -/
theorem piece_props {j₁ j₂ : V} {P : Finset V} (hP : P ∈ piecesU G j₁ j₂) :
    P ⊆ Core.interior G j₁ j₂ ∧ P.Nonempty ∧
      ∀ u ∈ P, ∀ w ∈ Core.interior G j₁ j₂, (w ∈ P ↔ SamePieceU G u w) := by
  obtain ⟨u, hu, hPu⟩ := mem_piecesU_iff.mp hP
  refine ⟨fun w hw => ((hPu w).mp hw).1, ⟨u, (hPu u).mpr ⟨hu, samePieceU_refl G u⟩⟩, ?_⟩
  intro v hv w hw
  have hv' := ((hPu v).mp hv).2
  rw [hPu w]
  exact ⟨fun h => samePieceU_trans (samePieceU_symm hv') h.2, fun h => ⟨hw, samePieceU_trans hv' h⟩⟩

end cuts

end WaveTurbulence.TVine.Struct
