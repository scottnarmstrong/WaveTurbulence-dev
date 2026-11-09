/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.UBase
public import WaveTurbulence.Foundations.TVine.Core.Statements
import Mathlib.Tactic

/-!
# N3 Theorem 6, part 1: the two chains of 2-cut sides (packet L3)

Setting `T6Ctx G v₁ v₂`: a cut context (connected, loop-free, even degrees), joints `v₁ ≠ v₂` of degree 2, all other
atoms of degree 4, and **N3 Lemma 6.2** (no two disjoint nonempty joint-free 2-cut sides; owner L1, named input
`PendantPolesInput`).

* `IsKSide`: a nonempty joint-free side with cut 2 (a 2-pole); `IsXSide`: a side with cut 2 containing `v₂`, not `v₁`.
* `kside_chain`, `xside_chain`: each family is a chain (uncrossing by posimodularity + Lemma 6.2).
* `kside_xside`: every `𝒦`-side lies inside or outside every `𝒳`-side.
* `side_cases`: every 2-cut side is an `𝒳`-side, a `𝒦`-side, or the complement of one.
* `samePieceU_iff_sides`: two atoms are in one piece iff no `𝒳`- or `𝒦`-side separates them.
* `exists_chain_list`: a finite chain of sets, listed in strictly increasing order.

This is the uncrossing form of N3 §1.4 (Lemmas 6.1, 6.3): instead of the block-cut tree of the cactus `Γ`, the two
chains carry the spine and the pendant (see HANDOFF.md).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

universe u

/-- **NAMED INPUT (N3 Lemma 6.2 = N2 Lemma 1.6 for T-vines, pendant poles; owner L1).** A T-vine has no two disjoint
nonempty sets `K₁, K₂` of interior atoms with `|δ(K₁)| = |δ(K₂)| = 2` (`research-gamma-half-3/NOTES.txt` L203–L205;
M4 §2.2 L135–L137; REFEREED REF3). Same binders as L1's drafted `Core.PendantPolesStatement`. -/
def PendantPolesInput : Prop := Core.PendantPolesStatement.{u}

variable {V : Type*} [DecidableEq V]

/-- The setting of N3 Theorem 6 at U level, for the labelling `(v₁, v₂)`. -/
structure T6Ctx (G : UMultigraph V) (v₁ v₂ : V) : Prop where
  cc : CutCtx G
  mem₁ : v₁ ∈ G.verts
  mem₂ : v₂ ∈ G.verts
  ne : v₁ ≠ v₂
  deg₁ : deg G v₁ = 2
  deg₂ : deg G v₂ = 2
  deg4 : ∀ v ∈ G.verts, v ≠ v₁ → v ≠ v₂ → deg G v = 4
  noPend : ∀ K₁ K₂ : Finset V, K₁ ⊆ Core.interior G v₁ v₂ → K₂ ⊆ Core.interior G v₁ v₂ → Disjoint K₁ K₂ →
    K₁.Nonempty → K₂.Nonempty → cut G K₁ = 2 → cut G K₂ = 2 → False

theorem interior_comm (G : UMultigraph V) (a b : V) : Core.interior G a b = Core.interior G b a := by
  unfold Core.interior; exact Finset.erase_right_comm

theorem T6Ctx.swap {G : UMultigraph V} {v₁ v₂ : V} (h : T6Ctx G v₁ v₂) : T6Ctx G v₂ v₁ where
  cc := h.cc
  mem₁ := h.mem₂
  mem₂ := h.mem₁
  ne := h.ne.symm
  deg₁ := h.deg₂
  deg₂ := h.deg₁
  deg4 := fun v hv h1 h2 => h.deg4 v hv h2 h1
  noPend := fun K₁ K₂ h1 h2 => h.noPend K₁ K₂ (interior_comm G v₁ v₂ ▸ h1) (interior_comm G v₁ v₂ ▸ h2)

/-- The T6 context of a T-vine, given Lemma 6.2. -/
theorem t6Ctx_of_isTVineU (h62 : PendantPolesInput.{u}) {V : Type u} [DecidableEq V] {G : UMultigraph V}
    {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) : T6Ctx G j₁ j₂ where
  cc := cutCtx_of_isTVineU h
  mem₁ := h.1.1
  mem₂ := h.1.2.1
  ne := h.1.2.2.1
  deg₁ := h.1.2.2.2.1
  deg₂ := h.1.2.2.2.2.1
  deg4 := h.1.2.2.2.2.2.1
  noPend := fun K₁ K₂ => h62 G j₁ j₂ K₁ K₂ h

section sides

variable {G : UMultigraph V} {v₁ v₂ : V}

/-- A joint-free 2-pole: a nonempty set of interior atoms with cut 2. -/
def IsKSide (G : UMultigraph V) (v₁ v₂ : V) (K : Finset V) : Prop :=
  K ⊆ G.verts ∧ v₁ ∉ K ∧ v₂ ∉ K ∧ K.Nonempty ∧ cut G K = 2

/-- A `v₂`-side: a 2-cut side containing `v₂` and not `v₁`. -/
def IsXSide (G : UMultigraph V) (v₁ v₂ : V) (X : Finset V) : Prop :=
  X ⊆ G.verts ∧ v₂ ∈ X ∧ v₁ ∉ X ∧ cut G X = 2

theorem subset_interior_of_joint_free {K : Finset V} (hK : K ⊆ G.verts) (h₁ : v₁ ∉ K) (h₂ : v₂ ∉ K) :
    K ⊆ Core.interior G v₁ v₂ := fun x hx =>
  mem_interior.mpr ⟨hK hx, fun h => h₁ (h ▸ hx), fun h => h₂ (h ▸ hx)⟩

theorem T6Ctx.noPend' (hT : T6Ctx G v₁ v₂) {K₁ K₂ : Finset V} (h₁ : IsKSide G v₁ v₂ K₁)
    (h₂ : IsKSide G v₁ v₂ K₂) (hd : Disjoint K₁ K₂) : False :=
  hT.noPend K₁ K₂ (subset_interior_of_joint_free h₁.1 h₁.2.1 h₁.2.2.1)
    (subset_interior_of_joint_free h₂.1 h₂.2.1 h₂.2.2.1) hd h₁.2.2.2.1 h₂.2.2.2.1 h₁.2.2.2.2 h₂.2.2.2.2

private theorem not_subset_witness {A B : Finset V} (h : ¬ A ⊆ B) : ∃ a ∈ A, a ∉ B := by
  by_contra hc; push Not at hc; exact h hc

/-- **The `𝒦`-sides form a chain.** -/
theorem kside_chain (hT : T6Ctx G v₁ v₂) {K₁ K₂ : Finset V} (h₁ : IsKSide G v₁ v₂ K₁)
    (h₂ : IsKSide G v₁ v₂ K₂) : K₁ ⊆ K₂ ∨ K₂ ⊆ K₁ := by
  by_contra hc
  push Not at hc
  obtain ⟨a, ha, haK⟩ := not_subset_witness hc.1
  obtain ⟨b, hb, hbK⟩ := not_subset_witness hc.2
  obtain ⟨hd₁, hd₂⟩ := uncross_diff hT.cc h₁.1 h₂.1 h₁.2.2.2.2 h₂.2.2.2.2 ha haK hb hbK
  refine hT.noPend' (K₁ := K₁ \ K₂) (K₂ := K₂ \ K₁) ⟨Finset.sdiff_subset.trans h₁.1, fun h => h₁.2.1
    (Finset.mem_sdiff.mp h).1, fun h => h₁.2.2.1 (Finset.mem_sdiff.mp h).1, ⟨a, Finset.mem_sdiff.mpr ⟨ha, haK⟩⟩, hd₁⟩
    ⟨Finset.sdiff_subset.trans h₂.1, fun h => h₂.2.1 (Finset.mem_sdiff.mp h).1,
      fun h => h₂.2.2.1 (Finset.mem_sdiff.mp h).1, ⟨b, Finset.mem_sdiff.mpr ⟨hb, hbK⟩⟩, hd₂⟩ ?_
  exact Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1

/-- **The `𝒳`-sides form a chain.** -/
theorem xside_chain (hT : T6Ctx G v₁ v₂) {X₁ X₂ : Finset V} (h₁ : IsXSide G v₁ v₂ X₁)
    (h₂ : IsXSide G v₁ v₂ X₂) : X₁ ⊆ X₂ ∨ X₂ ⊆ X₁ := by
  by_contra hc
  push Not at hc
  obtain ⟨a, ha, haK⟩ := not_subset_witness hc.1
  obtain ⟨b, hb, hbK⟩ := not_subset_witness hc.2
  obtain ⟨hd₁, hd₂⟩ := uncross_diff hT.cc h₁.1 h₂.1 h₁.2.2.2 h₂.2.2.2 ha haK hb hbK
  refine hT.noPend' (K₁ := X₁ \ X₂) (K₂ := X₂ \ X₁) ⟨Finset.sdiff_subset.trans h₁.1, fun h => h₁.2.2.1
    (Finset.mem_sdiff.mp h).1, fun h => (Finset.mem_sdiff.mp h).2 h₂.2.1, ⟨a, Finset.mem_sdiff.mpr ⟨ha, haK⟩⟩, hd₁⟩
    ⟨Finset.sdiff_subset.trans h₂.1, fun h => h₂.2.2.1 (Finset.mem_sdiff.mp h).1,
      fun h => (Finset.mem_sdiff.mp h).2 h₁.2.1, ⟨b, Finset.mem_sdiff.mpr ⟨hb, hbK⟩⟩, hd₂⟩ ?_
  exact Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1

/-- **A `𝒦`-side lies inside or outside every `𝒳`-side.** -/
theorem kside_xside (hT : T6Ctx G v₁ v₂) {K X : Finset V} (hK : IsKSide G v₁ v₂ K) (hX : IsXSide G v₁ v₂ X) :
    K ⊆ X ∨ Disjoint K X := by
  by_contra hc
  push Not at hc
  obtain ⟨b, hb, hbX⟩ := not_subset_witness hc.1
  obtain ⟨a, ha⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hc.2
  obtain ⟨hi, -⟩ := uncross_inter_union hT.cc hK.1 hX.1 hK.2.2.2.2 hX.2.2.2 ha hT.mem₁
    (by rw [Finset.mem_union]; exact fun h => h.elim hK.2.1 hX.2.2.1)
  obtain ⟨hd, -⟩ := uncross_diff hT.cc hK.1 hX.1 hK.2.2.2.2 hX.2.2.2 hb hbX hX.2.1 hK.2.2.1
  refine hT.noPend' (K₁ := K ∩ X) (K₂ := K \ X)
    ⟨Finset.inter_subset_left.trans hK.1, fun h => hK.2.1 (Finset.mem_inter.mp h).1,
      fun h => hK.2.2.1 (Finset.mem_inter.mp h).1, ⟨a, ha⟩, hi⟩
    ⟨Finset.sdiff_subset.trans hK.1, fun h => hK.2.1 (Finset.mem_sdiff.mp h).1,
      fun h => hK.2.2.1 (Finset.mem_sdiff.mp h).1, ⟨b, Finset.mem_sdiff.mpr ⟨hb, hbX⟩⟩, hd⟩ ?_
  exact Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2

/-- **Every 2-cut side** is an `𝒳`-side, a `𝒦`-side, or the complement of one. -/
theorem side_cases (hT : T6Ctx G v₁ v₂) {X : Finset V} (hX : X ⊆ G.verts) (h2 : cut G X = 2) :
    IsXSide G v₁ v₂ X ∨ IsXSide G v₁ v₂ (G.verts \ X) ∨ IsKSide G v₁ v₂ X ∨ IsKSide G v₁ v₂ (G.verts \ X) := by
  have hc : cut G (G.verts \ X) = 2 := by rw [cut_compl hX]; exact h2
  by_cases h₁ : v₁ ∈ X <;> by_cases h₂ : v₂ ∈ X
  · -- both joints inside: the complement is joint-free and nonempty
    right; right; right
    refine ⟨Finset.sdiff_subset, fun h => (Finset.mem_sdiff.mp h).2 h₁, fun h => (Finset.mem_sdiff.mp h).2 h₂,
      ?_, hc⟩
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    have hXV : X = G.verts := Finset.Subset.antisymm hX hne
    rw [hXV] at h2
    have : cut G G.verts = 0 := by unfold cut; simp
    omega
  · right; left
    exact ⟨Finset.sdiff_subset, Finset.mem_sdiff.mpr ⟨hT.mem₂, h₂⟩, fun h => (Finset.mem_sdiff.mp h).2 h₁, hc⟩
  · left; exact ⟨hX, h₂, h₁, h2⟩
  · right; right; left
    refine ⟨hX, h₁, h₂, ?_, h2⟩
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h2
    have : cut G ∅ = 0 := by unfold cut; simp
    omega

/-- **Pieces through the two chains.** Two atoms are in one piece iff no `𝒳`-side and no `𝒦`-side separates them. -/
theorem samePieceU_iff_sides (hT : T6Ctx G v₁ v₂) {u w : V} (hu : u ∈ G.verts) (hw : w ∈ G.verts) :
    SamePieceU G u w ↔ (∀ X, IsXSide G v₁ v₂ X → (u ∈ X ↔ w ∈ X)) ∧ (∀ K, IsKSide G v₁ v₂ K → (u ∈ K ↔ w ∈ K)) := by
  rw [samePieceU_iff_cut_two hT.cc hu hw]
  constructor
  · intro h
    exact ⟨fun X hX => h X hX.1 hX.2.2.2, fun K hK => h K hK.1 hK.2.2.2.2⟩
  · rintro ⟨hx, hk⟩ X hX h2
    have compl_iff : ∀ Y : Finset V, (u ∈ Y ↔ w ∈ Y) → (u ∈ G.verts \ X → Y = G.verts \ X →
        (u ∈ X ↔ w ∈ X)) := by
      intro Y hY _ hYe
      rw [hYe] at hY
      simp only [Finset.mem_sdiff, hu, hw, true_and] at hY
      exact not_iff_not.mp hY
    rcases side_cases hT hX h2 with h | h | h | h
    · exact hx X h
    · have := hx _ h
      simp only [Finset.mem_sdiff, hu, hw, true_and] at this
      exact not_iff_not.mp this
    · exact hk X h
    · have := hk _ h
      simp only [Finset.mem_sdiff, hu, hw, true_and] at this
      exact not_iff_not.mp this

end sides

/-! ## Sorted chains -/

/-- A finite chain of sets, listed in strictly increasing order. -/
theorem exists_chain_list {α : Type*} [DecidableEq α] (C : Finset (Finset α))
    (hC : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) : ∃ l : List (Finset α), l.toFinset = C ∧ l.Pairwise (· ⊂ ·) := by
  induction h : C.card generalizing C with
  | zero =>
    rw [Finset.card_eq_zero] at h
    exact ⟨[], by simp [h], List.Pairwise.nil⟩
  | succ n ih =>
    have hne : C.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image C Finset.card hne
    have hC' : ∀ X ∈ C.erase A, ∀ Y ∈ C.erase A, X ⊆ Y ∨ Y ⊆ X := fun X hX Y hY =>
      hC X (Finset.mem_of_mem_erase hX) Y (Finset.mem_of_mem_erase hY)
    obtain ⟨l, hl, hp⟩ := ih (C.erase A) hC' (by rw [Finset.card_erase_of_mem hA, h]; rfl)
    refine ⟨l ++ [A], ?_, ?_⟩
    · rw [List.toFinset_append, hl]
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
      rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hA]
    · rw [List.pairwise_append]
      refine ⟨hp, List.pairwise_singleton _ _, ?_⟩
      intro B hB A' hA'
      rw [List.mem_singleton] at hA'
      rw [hA']
      have hB' : B ∈ C.erase A := by rw [← hl]; exact List.mem_toFinset.mpr hB
      obtain ⟨hBA, hBC⟩ := Finset.mem_erase.mp hB'
      rcases hC B hBC A hA with hs | hs
      · exact Finset.ssubset_iff_subset_ne.mpr ⟨hs, hBA⟩
      · exfalso
        have hcard := hmax B hBC
        exact hBA (Finset.eq_of_subset_of_card_le hs hcard).symm

end WaveTurbulence.TVine.Struct
