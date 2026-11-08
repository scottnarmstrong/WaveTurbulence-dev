/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.PairBranch

/-! # D2c PROT-CUT: the free-time integral of a closing pair with both partners designated

With `𝔫_a` (the root) designated at `u` and `𝔫_b` at `v`, the time domain of a closing pair is the product of
the time domains of its three pieces (`protDom_pair`): the interior with upper clock `u` and lone-port time `v`,
and the two side couples with upper clocks `u` (tree at `𝔫_a`) and `v` (tree at `𝔫_b`). Consequently
(`protTime_pair`) the free-time integral is the two boundary phases times the product of the three free-time
integrals. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The upper clock of tree `j` of the red couple: `u` at `𝔫_a`, `v` at `𝔫_b`. -/
def cupR (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (u v : ℝ) (j : Fin 2) : ℝ :=
  if rBase m inner ζ j = [m.red.1] then u else v

/-- The upper clock of tree `j` of the green couple. -/
def cupG (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (u v : ℝ) (j : Fin 2) : ℝ :=
  if gBase m inner ζ j = [m.green.1] then u else v

theorem rBase_cases (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) :
    rBase m inner ζ j = [m.red.1] ∨ rBase m inner ζ j = bPath m inner ++ [m.red.2] := by
  unfold rBase; split_ifs <;> simp

theorem gBase_cases (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) :
    gBase m inner ζ j = [m.green.1] ∨ gBase m inner ζ j = bPath m inner ++ [m.green.2] := by
  unfold gBase; split_ifs <;> simp

theorem bot_ne_top (m : MiniTreeCode) (inner : RegChain) (k i : Fin 3) (hi : i ≠ m.c) :
    bPath m inner ++ [k] ≠ [i] := by
  intro h
  have := congrArg List.head? h
  simp [bPath_eq] at this
  exact hi this.symm

theorem cupR_top {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {u v : ℝ} {j : Fin 2}
    (h : rBase m inner ζ j = [m.red.1]) : cupR m inner ζ u v j = u := by simp [cupR, h]

theorem cupR_bot {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {u v : ℝ} {j : Fin 2}
    (h : rBase m inner ζ j = bPath m inner ++ [m.red.2]) : cupR m inner ζ u v j = v := by
  simp [cupR, h, bot_ne_top m inner m.red.2 m.red.1 (red_ne_c m)]

theorem cupG_top {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {u v : ℝ} {j : Fin 2}
    (h : gBase m inner ζ j = [m.green.1]) : cupG m inner ζ u v j = u := by simp [cupG, h]

theorem cupG_bot {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {u v : ℝ} {j : Fin 2}
    (h : gBase m inner ζ j = bPath m inner ++ [m.green.2]) : cupG m inner ζ u v j = v := by
  simp [cupG, h, bot_ne_top m inner m.green.2 m.green.1 (green_ne_c m)]

namespace PairData

variable {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {G Gi : Garden 1} {Gr Gg : Garden 2}
variable (h : PairData m Qr Qg inner G Gi Gr Gg)
include h

omit h in
theorem branch_eq_of_path {b b₁ : GBranch G.tree} (hp : b.1.2 = b₁.1.2) : b = b₁ :=
  Subtype.ext (Prod.ext (Subsingleton.elim _ _) hp)

omit h in
theorem isChildOf_iff (b b' : GBranch G.tree) : b'.IsChildOf b ↔ ∃ k, b'.1.2 = b.1.2 ++ [k] :=
  ⟨fun h => h.2, fun h => ⟨Subsingleton.elim _ _, h⟩⟩

/-- The lone parent of the interior piece. -/
theorem isLoneParent_I (x : GBranch Gi.tree) :
    Gi.IsLoneParent x ↔ ∃ k, inner.lonePath = x.1.2 ++ [k] := by
  constructor
  · rintro ⟨ℓ, hℓ, -, k, hk⟩
    have hm := h.decI.2.1 ℓ
    unfold Garden.IsLone at hℓ
    rw [hℓ] at hm
    by_cases he : ℓ.1.2 = inner.lonePath
    · exact ⟨k, he.symm.trans hk⟩
    · rw [if_neg he] at hm; simp at hm
  · rintro ⟨k, hk⟩
    have hmem : inner.lonePath ∈ (Gi.tree 0).leaves := by
      rw [h.decI.1]; exact lonePath_mem_leaves inner _
    refine ⟨⟨((0 : Fin 1), inner.lonePath), hmem⟩, ?_, Subsingleton.elim _ _, k, hk⟩
    unfold Garden.IsLone
    have := h.decI.2.1 ⟨((0 : Fin 1), inner.lonePath), hmem⟩
    simpa using this

/-- The only lone parent of a closing pair is `𝔫_b`. -/
theorem isLoneParent_G (b : GBranch G.tree) (hb : G.IsLoneParent b) : b = h.bB := by
  obtain ⟨ℓ, hℓ, -, k, hk⟩ := hb
  have hm := h.decZ.2.1 ℓ
  unfold Garden.IsLone at hℓ
  rw [hℓ] at hm
  by_cases he : ℓ.1.2 = (RegChain.pair m Qr Qg inner .nil).lonePath
  · apply branch_eq_of_path
    have : (RegChain.pair m Qr Qg inner .nil).lonePath = bPath m inner ++ [m.lone] := by
      simp [RegChain.lonePath, bPath]
    rw [this] at he
    rw [he] at hk
    exact (List.append_inj' hk rfl).1.symm
  · rw [if_neg he] at hm; simp at hm

theorem βi_child_rootB (x : GBranch Gi.tree) (hx : x.1.2 = []) : (h.βi x).IsChildOf h.rootB :=
  ⟨rfl, m.c, by simp [βi, rootB, hx]⟩

theorem bB_child_βi (x : GBranch Gi.tree) (hx : Gi.IsLoneParent x) : h.bB.IsChildOf (h.βi x) := by
  obtain ⟨k, hk⟩ := (h.isLoneParent_I x).mp hx
  exact ⟨rfl, k, by simp [βi, bB, bPath, hk]⟩

theorem βr_child_root (y : GBranch Gr.tree) (hy : y.1.2 = [])
    (ht : rBase m inner (G.sig 0) y.1.1 = [m.red.1]) : (h.βr y).IsChildOf h.rootB :=
  ⟨rfl, m.red.1, by simp [βr, rootB, hy, ht]⟩

theorem βr_child_bB (y : GBranch Gr.tree) (hy : y.1.2 = [])
    (ht : rBase m inner (G.sig 0) y.1.1 = bPath m inner ++ [m.red.2]) : (h.βr y).IsChildOf h.bB :=
  ⟨rfl, m.red.2, by simp [βr, bB, hy, ht]⟩

theorem βg_child_root (y : GBranch Gg.tree) (hy : y.1.2 = [])
    (ht : gBase m inner (G.sig 0) y.1.1 = [m.green.1]) : (h.βg y).IsChildOf h.rootB :=
  ⟨rfl, m.green.1, by simp [βg, rootB, hy, ht]⟩

theorem βg_child_bB (y : GBranch Gg.tree) (hy : y.1.2 = [])
    (ht : gBase m inner (G.sig 0) y.1.1 = bPath m inner ++ [m.green.2]) : (h.βg y).IsChildOf h.bB :=
  ⟨rfl, m.green.2, by simp [βg, bB, hy, ht]⟩

theorem βi_child_iff (x x' : GBranch Gi.tree) : (h.βi x').IsChildOf (h.βi x) ↔ x'.IsChildOf x := by
  constructor
  · rintro ⟨-, k, hk⟩
    exact ⟨Subsingleton.elim _ _, k, by simpa [βi] using hk⟩
  · rintro ⟨-, k, hk⟩
    exact ⟨rfl, k, by simp [βi, hk]⟩

theorem βr_child_iff (y y' : GBranch Gr.tree) : (h.βr y').IsChildOf (h.βr y) ↔ y'.IsChildOf y := by
  constructor
  · rintro ⟨-, k, hk⟩
    have hk' : rBase m inner (G.sig 0) y'.1.1 ++ y'.1.2 = rBase m inner (G.sig 0) y.1.1 ++ (y.1.2 ++ [k]) := by
      simpa [βr] using hk
    have hr := regionOf_rBase m inner (G.sig 0) y'.1.1 y'.1.2
    rw [hk', regionOf_rBase] at hr
    have hj : y'.1.1 = y.1.1 := by simpa using hr.symm
    rw [hj] at hk'
    exact ⟨hj, k, List.append_cancel_left hk'⟩
  · rintro ⟨hj, k, hk⟩
    exact ⟨by simp [βr, hj], k, by simp [βr, hk, hj]⟩

theorem βg_child_iff (y y' : GBranch Gg.tree) : (h.βg y').IsChildOf (h.βg y) ↔ y'.IsChildOf y := by
  constructor
  · rintro ⟨-, k, hk⟩
    have hk' : gBase m inner (G.sig 0) y'.1.1 ++ y'.1.2 = gBase m inner (G.sig 0) y.1.1 ++ (y.1.2 ++ [k]) := by
      simpa [βg] using hk
    have hr := regionOf_gBase m inner (G.sig 0) y'.1.1 y'.1.2
    rw [hk', regionOf_gBase] at hr
    have hj : y'.1.1 = y.1.1 := by simpa using hr.symm
    rw [hj] at hk'
    exact ⟨hj, k, List.append_cancel_left hk'⟩
  · rintro ⟨hj, k, hk⟩
    exact ⟨by simp [βg, hj], k, by simp [βg, hk, hj]⟩

/-- **The parent of every branch of a closing pair.** -/
theorem child_cases (b b' : GBranch G.tree) (hc : b'.IsChildOf b) :
    (b' = h.bB ∧ (b = h.rootB ∨ ∃ x, Gi.IsLoneParent x ∧ b = h.βi x)) ∨
    (∃ x', b' = h.βi x' ∧ ((x'.1.2 = [] ∧ b = h.rootB) ∨ ∃ x, x'.IsChildOf x ∧ b = h.βi x)) ∨
    (∃ y', b' = h.βr y' ∧ ((y'.1.2 = [] ∧ rBase m inner (G.sig 0) y'.1.1 = [m.red.1] ∧ b = h.rootB) ∨
      (y'.1.2 = [] ∧ rBase m inner (G.sig 0) y'.1.1 = bPath m inner ++ [m.red.2] ∧ b = h.bB) ∨
      ∃ y, y'.IsChildOf y ∧ b = h.βr y)) ∨
    (∃ y', b' = h.βg y' ∧ ((y'.1.2 = [] ∧ gBase m inner (G.sig 0) y'.1.1 = [m.green.1] ∧ b = h.rootB) ∨
      (y'.1.2 = [] ∧ gBase m inner (G.sig 0) y'.1.1 = bPath m inner ++ [m.green.2] ∧ b = h.bB) ∨
      ∃ y, y'.IsChildOf y ∧ b = h.βg y)) := by
  obtain ⟨k, hk⟩ := (isChildOf_iff b b').mp hc
  obtain ⟨z', rfl⟩ := h.pairBranch_surjective b'
  rcases z' with j | x' | y' | y'
  · fin_cases j
    · exfalso
      have : ([] : Path) = b.1.2 ++ [k] := hk
      simp at this
    · left
      refine ⟨rfl, ?_⟩
      have hk' : m.c :: inner.lonePath = b.1.2 ++ [k] := hk
      rcases List.eq_nil_or_concat inner.lonePath with hl | ⟨q, k', hq⟩
      · left
        apply branch_eq_of_path
        rw [hl] at hk'
        have := List.append_inj' (show [] ++ [m.c] = b.1.2 ++ [k] by simpa using hk') rfl
        exact this.1.symm
      · right
        rw [hq, List.concat_eq_append, ← List.cons_append] at hk'
        have e := List.append_inj' hk' rfl
        have hmem : q ∈ (Gi.tree 0).branching := by
          rw [h.decI.1]
          refine TTree.branching_of_append_mem _ (i := k') ?_
          rw [← List.concat_eq_append, ← hq]
          exact lonePath_mem_plug inner _ _
        refine ⟨⟨((0 : Fin 1), q), hmem⟩, (h.isLoneParent_I _).mpr ⟨k', by simpa using hq⟩, ?_⟩
        apply branch_eq_of_path
        exact e.1.symm
  · right; left
    refine ⟨x', rfl, ?_⟩
    have hk' : m.c :: x'.1.2 = b.1.2 ++ [k] := hk
    rcases List.eq_nil_or_concat x'.1.2 with hl | ⟨q, k', hq⟩
    · left
      refine ⟨hl, branch_eq_of_path ?_⟩
      rw [hl] at hk'
      exact (List.append_inj' (show [] ++ [m.c] = b.1.2 ++ [k] by simpa using hk') rfl).1.symm
    · right
      rw [hq, List.concat_eq_append, ← List.cons_append] at hk'
      have e := List.append_inj' hk' rfl
      have hmem : q ∈ (Gi.tree x'.1.1).branching := by
        refine TTree.branching_of_append_mem _ (i := k') ?_
        rw [← List.concat_eq_append, ← hq]
        exact TTree.branching_subset_nodes _ x'.2
      refine ⟨⟨(x'.1.1, q), hmem⟩, ⟨rfl, k', by simpa using hq⟩, branch_eq_of_path ?_⟩
      exact e.1.symm
  · right; right; left
    refine ⟨y', rfl, ?_⟩
    have hk' : rBase m inner (G.sig 0) y'.1.1 ++ y'.1.2 = b.1.2 ++ [k] := hk
    rcases List.eq_nil_or_concat y'.1.2 with hl | ⟨q, k', hq⟩
    · rw [hl, List.append_nil] at hk'
      rcases rBase_cases m inner (G.sig 0) y'.1.1 with ht | ht
      · left
        refine ⟨hl, ht, branch_eq_of_path ?_⟩
        rw [ht] at hk'
        exact (List.append_inj' (show [] ++ [m.red.1] = b.1.2 ++ [k] by simpa using hk') rfl).1.symm
      · right; left
        refine ⟨hl, ht, branch_eq_of_path ?_⟩
        rw [ht] at hk'
        exact (List.append_inj' hk' rfl).1.symm
    · right; right
      rw [hq, List.concat_eq_append, ← List.append_assoc] at hk'
      have e := List.append_inj' hk' rfl
      have hmem : q ∈ (Gr.tree y'.1.1).branching := by
        refine TTree.branching_of_append_mem _ (i := k') ?_
        rw [← List.concat_eq_append, ← hq]
        exact TTree.branching_subset_nodes _ y'.2
      refine ⟨⟨(y'.1.1, q), hmem⟩, ⟨rfl, k', by simpa using hq⟩, branch_eq_of_path ?_⟩
      exact e.1.symm
  · right; right; right
    refine ⟨y', rfl, ?_⟩
    have hk' : gBase m inner (G.sig 0) y'.1.1 ++ y'.1.2 = b.1.2 ++ [k] := hk
    rcases List.eq_nil_or_concat y'.1.2 with hl | ⟨q, k', hq⟩
    · rw [hl, List.append_nil] at hk'
      rcases gBase_cases m inner (G.sig 0) y'.1.1 with ht | ht
      · left
        refine ⟨hl, ht, branch_eq_of_path ?_⟩
        rw [ht] at hk'
        exact (List.append_inj' (show [] ++ [m.green.1] = b.1.2 ++ [k] by simpa using hk') rfl).1.symm
      · right; left
        refine ⟨hl, ht, branch_eq_of_path ?_⟩
        rw [ht] at hk'
        exact (List.append_inj' hk' rfl).1.symm
    · right; right
      rw [hq, List.concat_eq_append, ← List.append_assoc] at hk'
      have e := List.append_inj' hk' rfl
      have hmem : q ∈ (Gg.tree y'.1.1).branching := by
        refine TTree.branching_of_append_mem _ (i := k') ?_
        rw [← List.concat_eq_append, ← hq]
        exact TTree.branching_subset_nodes _ y'.2
      refine ⟨⟨(y'.1.1, q), hmem⟩, ⟨rfl, k', by simpa using hq⟩, branch_eq_of_path ?_⟩
      exact e.1.symm

end PairData

end WaveTurbulence.Flower.ProtCut
