/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.VineLike
public import WaveTurbulence.Foundations.TVine.Core.Y2
public import WaveTurbulence.Foundations.TVine.Struct.UBase
import Mathlib.Tactic

/-!
# Sizes of the members of `𝒱_enl` and the kinds of short vine chains (packet L3)

* `card_isTVineU`: a T-vine has an odd number `≥ 5` of atoms (its closure reaches the 3-atom `T` by (Y2) steps, each
  removing two atoms);
* `card_isVineXU_I` (2 atoms), `card_isVineXU_II` (an even number `≥ 4`);
* `card_isVineKindU`: the size of a member of each kind;
* `chain_card`: a vine chain with `ℓ` ingredients on `S` has `|S| ≥ ℓ + 1`, with `|S| = Σ |S_i| − (ℓ − 1)`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

variable {V : Type*} [DecidableEq V]

/-- A (Y2) step removes two atoms. -/
theorem card_y2Step {G G' : UMultigraph V} (h : Y2Step G G') : G'.verts.card + 2 = G.verts.card := by
  obtain ⟨a, b, c, d, hab, -, -, -, -, -, h3, -, -, -, -, hv, -⟩ := h
  have ha : a ∈ G.verts := G.supp _ (by omega) a (Sym2.mem_mk_left a b)
  have hb : b ∈ G.verts.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, G.supp _ (by omega) b (Sym2.mem_mk_right a b)⟩
  rw [hv, Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hb
  omega

theorem card_rtg_y2 {G G' : UMultigraph V} (h : Relation.ReflTransGen Y2Step G G') :
    ∃ n, G.verts.card = G'.verts.card + 2 * n := by
  induction h with
  | refl => exact ⟨0, by ring⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    have := card_y2Step hbc
    exact ⟨n + 1, by omega⟩

theorem card_doubledTriangle {G : UMultigraph V} (h : IsDoubledTriangle G) : G.verts.card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, hv, -⟩ := h
  rw [hv, Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩

/-- **A T-vine has an odd number `≥ 5` of atoms.** -/
theorem card_isTVineU {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) :
    Odd G.verts.card ∧ 5 ≤ G.verts.card := by
  obtain ⟨hB, -, C, hC, C', hr, hT⟩ := h
  obtain ⟨n, hn⟩ := card_rtg_y2 hr
  rw [card_doubledTriangle hT] at hn
  have hCv := hC.2.1
  have h1 : j₁ ∈ G.verts := hB.1
  have h2 : j₂ ∈ G.verts.erase j₁ := Finset.mem_erase.mpr ⟨Ne.symm hB.2.2.1, hB.2.1⟩
  rw [hCv, Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1] at hn
  have e1 := Finset.card_erase_add_one h1
  have e2 := Finset.card_erase_add_one h2
  refine ⟨⟨n + 2, by omega⟩, by omega⟩

theorem expand_I_n {k : List ℕ} (hk : k.length = VineType.I.template.slots.length) :
    (VineType.I.expand k).n = 2 := by
  have : k = [] := List.eq_nil_of_length_eq_zero (by simpa [VineType.template] using hk)
  subst this; rfl

theorem expand_II_n {k : List ℕ} (hk : k.length = VineType.II.template.slots.length) :
    ∃ m, (VineType.II.expand k).n = 2 * m + 4 := by
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = [k₀] := by
    have : k.length = 1 := by simpa [VineType.template] using hk
    match k, this with
    | [k₀], _ => exact ⟨k₀, rfl⟩
  refine ⟨k₀, ?_⟩
  simp only [VineType.expand, VineType.template, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
    List.foldl_nil, insertRungs]
  split_ifs with h
  · subst h; rfl
  · simp only; ring

theorem card_of_isVineXU {X : VineType} {G : UMultigraph V} {j₁ j₂ : V} (h : IsVineXU X G j₁ j₂) :
    ∃ k : List ℕ, k.length = X.template.slots.length ∧ G.verts.card = (X.expand k).n := by
  obtain ⟨-, k, hk, f, hinj, himg, -, -⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [← Finset.card_image_of_injOn hinj, himg, Finset.card_range]

theorem card_isVineXU_I {G : UMultigraph V} {j₁ j₂ : V} (h : IsVineXU .I G j₁ j₂) : G.verts.card = 2 := by
  obtain ⟨k, hk, he⟩ := card_of_isVineXU h
  rw [he, expand_I_n hk]

theorem card_isVineXU_II {G : UMultigraph V} {j₁ j₂ : V} (h : IsVineXU .II G j₁ j₂) :
    Even G.verts.card ∧ 4 ≤ G.verts.card := by
  obtain ⟨k, hk, he⟩ := card_of_isVineXU h
  obtain ⟨m, hm⟩ := expand_II_n hk
  rw [he, hm]
  exact ⟨⟨m + 2, by ring⟩, by omega⟩

/-- The size of a member of each kind: (I) two atoms, (II) an even number `≥ 4`, a T-vine an odd number `≥ 5`. -/
theorem card_isVineKindU {k : EnlKind} {G : UMultigraph V} {j₁ j₂ : V} (h : IsVineKindU k G j₁ j₂) :
    (k = .I ∧ G.verts.card = 2) ∨ (k = .II ∧ Even G.verts.card ∧ 4 ≤ G.verts.card) ∨
      (k = .T ∧ Odd G.verts.card ∧ 5 ≤ G.verts.card) := by
  cases k with
  | I => exact Or.inl ⟨rfl, card_isVineXU_I h⟩
  | II => exact Or.inr (Or.inl ⟨rfl, card_isVineXU_II h⟩)
  | T => exact Or.inr (Or.inr ⟨rfl, card_isTVineU h⟩)

theorem isBlockU_of_isVineKindU {k : EnlKind} {G : UMultigraph V} {j₁ j₂ : V} (h : IsVineKindU k G j₁ j₂) :
    IsBlockU G j₁ j₂ := by
  cases k with
  | I => exact h.1
  | II => exact h.1
  | T => exact h.1

theorem induce_verts (G : UMultigraph V) (S : Finset V) : (induce G S).verts = S := rfl

/-- The atom set of a chain contains its ends, the chain is nonempty, and `|S| ≥ ℓ + 1`. -/
theorem chain_card {H : UMultigraph V} {S : Finset V} {a b : V} {ks : List EnlKind} (h : ChainU H S a b ks) :
    a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ks ≠ [] ∧ ks.length + 1 ≤ S.card := by
  induction h with
  | @single S a b k hk =>
    have hB := isBlockU_of_isVineKindU hk
    refine ⟨hB.1, hB.2.1, hB.2.2.1, List.cons_ne_nil _ _, ?_⟩
    have := Finset.card_le_card (show ({a, b} : Finset V) ⊆ S from
      Finset.insert_subset hB.1 (Finset.singleton_subset_iff.mpr hB.2.1))
    rw [Finset.card_pair hB.2.2.1] at this
    simpa using this
  | @append S T a b c ks k _ hk hST hac ih =>
    have hB := isBlockU_of_isVineKindU hk
    obtain ⟨ha, hb, hab, -, hcard⟩ := ih
    refine ⟨Finset.mem_union_left _ ha, Finset.mem_union_right _ hB.2.1, hac, by simp, ?_⟩
    have hc : c ∈ T \ S := by
      refine Finset.mem_sdiff.mpr ⟨hB.2.1, fun hcS => ?_⟩
      have : c ∈ S ∩ T := Finset.mem_inter.mpr ⟨hcS, hB.2.1⟩
      rw [hST, Finset.mem_singleton] at this
      exact hB.2.2.1 this.symm
    have h1 : (S ∪ T).card = S.card + (T \ S).card := by
      rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
    have h2 : 1 ≤ (T \ S).card := Finset.card_pos.mpr ⟨c, hc⟩
    simp only [List.length_append, List.length_singleton]
    omega

/-! ## Inversion of short chains -/

theorem induce_mult_of_mem (G : UMultigraph V) {S : Finset V} {u w : V} (hu : u ∈ S) (hw : w ∈ S) :
    (induce G S).mult s(u, w) = G.mult s(u, w) := by
  show (if s(u, w) ∈ S.sym2 then G.mult s(u, w) else 0) = _
  rw [if_pos (Finset.mk_mem_sym2_iff.mpr ⟨hu, hw⟩)]

theorem chain_single_inv {H : UMultigraph V} {S : Finset V} {a b : V} {k : EnlKind}
    (h : ChainU H S a b [k]) : IsVineKindU k (induce H S) a b := by
  generalize hl : [k] = l at h
  cases h with
  | single hk =>
    simp only [List.cons.injEq, and_true] at hl
    subst hl; exact hk
  | append h1 _ _ _ =>
    exfalso
    have hne := (chain_card h1).2.2.2.1
    have := congrArg List.length hl
    simp only [List.length_singleton, List.length_append] at this
    have : 0 < _ := List.length_pos_of_ne_nil hne
    omega

theorem chain_append_inv {H : UMultigraph V} {S : Finset V} {a c : V} {ks : List EnlKind} {k : EnlKind}
    (hne : ks ≠ []) (h : ChainU H S a c (ks ++ [k])) :
    ∃ (S' T : Finset V) (b : V), ChainU H S' a b ks ∧ IsVineKindU k (induce H T) b c ∧ S' ∩ T = {b} ∧
      a ≠ c ∧ S = S' ∪ T := by
  generalize hl : ks ++ [k] = l at h
  cases h with
  | single hk =>
    exfalso
    have := congrArg List.length hl
    simp only [List.length_singleton, List.length_append] at this
    have : 0 < _ := List.length_pos_of_ne_nil hne
    omega
  | @append S' T a' b c' ks' k' h1 hk hST hac =>
    obtain ⟨h1', h2'⟩ := List.append_inj' hl rfl
    simp only [List.cons.injEq, and_true] at h2'
    subst h1' h2'
    exact ⟨S', T, b, h1, hk, hST, hac, rfl⟩

/-- **A chain on two atoms is a single (I).** -/
theorem kinds_of_card_two {H : UMultigraph V} {S : Finset V} {a b : V} {ks : List EnlKind}
    (h : ChainU H S a b ks) (hS : S.card = 2) : ks = [.I] := by
  obtain ⟨-, -, -, hne, hlen⟩ := chain_card h
  obtain ⟨k, rfl⟩ : ∃ k, ks = [k] := by
    match ks, hne, hlen with
    | [k], _, _ => exact ⟨k, rfl⟩
    | _ :: _ :: _, _, hlen => simp at hlen; omega
  have hk := chain_single_inv h
  rcases card_isVineKindU hk with ⟨rfl, -⟩ | ⟨-, -, h4⟩ | ⟨-, -, h5⟩
  · rfl
  · rw [induce_verts] at h4; omega
  · rw [induce_verts] at h5; omega

/-- **A chain on three atoms is two (I)'s.** -/
theorem kinds_of_card_three {H : UMultigraph V} {S : Finset V} {a b : V} {ks : List EnlKind}
    (h : ChainU H S a b ks) (hS : S.card = 3) : ks = [.I, .I] := by
  obtain ⟨-, -, -, hne, hlen⟩ := chain_card h
  rcases ks with _ | ⟨k₁, _ | ⟨k₂, _ | ⟨k₃, ks⟩⟩⟩
  · exact absurd rfl hne
  · exfalso
    rcases card_isVineKindU (chain_single_inv h) with ⟨-, h2⟩ | ⟨-, ⟨m, hm⟩, -⟩ | ⟨-, -, h5⟩
    · rw [induce_verts] at h2; omega
    · rw [induce_verts] at hm; omega
    · rw [induce_verts] at h5; omega
  · obtain ⟨S', T, b', h1, hk, hST, -, rfl⟩ := chain_append_inv (ks := [k₁]) (List.cons_ne_nil _ _) h
    have hk1 := chain_single_inv h1
    have hT := isBlockU_of_isVineKindU hk
    have hS'2 := (chain_card h1).2.2.2.2
    have hc : (S' ∪ T).card = S'.card + T.card - 1 := by
      have := Finset.card_union_add_card_inter S' T
      rw [hST, Finset.card_singleton] at this; omega
    have hT2 : 2 ≤ T.card := by
      have := Finset.card_le_card (Finset.insert_subset hT.1 (Finset.singleton_subset_iff.mpr hT.2.1))
      rw [Finset.card_pair hT.2.2.1] at this; exact this
    simp only [List.length_singleton] at hS'2
    have hS'c : S'.card = 2 := by omega
    have hTc : T.card = 2 := by omega
    have e1 : k₁ = .I := by
      rcases card_isVineKindU hk1 with ⟨h, -⟩ | ⟨-, -, h4⟩ | ⟨-, -, h5⟩
      · exact h
      · rw [induce_verts] at h4; omega
      · rw [induce_verts] at h5; omega
    have e2 : k₂ = .I := by
      rcases card_isVineKindU hk with ⟨h, -⟩ | ⟨-, -, h4⟩ | ⟨-, -, h5⟩
      · exact h
      · rw [induce_verts] at h4; omega
      · rw [induce_verts] at h5; omega
    rw [e1, e2]
  · simp at hlen; omega

/-! ## A chain of at least two ingredients has a cut atom -/

theorem deg_induce (H : UMultigraph V) {T : Finset V} {y : V} (hy : y ∈ T) (hT : T ⊆ H.verts) :
    deg H y = deg (induce H T) y + ∑ w ∈ H.verts \ T, H.mult s(y, w) := by
  unfold deg
  rw [induce_verts, induce_mult_of_mem H hy hy,
    Finset.sum_congr rfl fun w hw => induce_mult_of_mem H hy hw, ← Finset.sum_sdiff hT]
  ring

/-- **A chain of `≥ 2` ingredients filling a block has an interior cut atom** (its last junction). -/
theorem chain_cut_atom {H : UMultigraph V} {S : Finset V} {a c : V} {ks : List EnlKind} {k : EnlKind}
    (hne : ks ≠ []) (h : ChainU H S a c (ks ++ [k])) (hB : IsBlockU H a c) (hS : H.verts = S) :
    ∃ b, b ∈ S ∧ b ≠ a ∧ b ≠ c ∧ ¬ ConnOn H (H.verts.erase b) := by
  obtain ⟨S', T, b, h1, hk, hST, hac, rfl⟩ := chain_append_inv hne h
  have hTB := isBlockU_of_isVineKindU hk
  obtain ⟨ha', hb', hab, -, -⟩ := chain_card h1
  have hbS : b ∈ S' ∪ T := Finset.mem_union_left _ hb'
  have hTsub : T ⊆ H.verts := by rw [hS]; exact Finset.subset_union_right
  have haT : a ∉ T := fun haT => by
    have : a ∈ S' ∩ T := Finset.mem_inter.mpr ⟨ha', haT⟩
    rw [hST, Finset.mem_singleton] at this; exact hab this
  -- every bond at an atom of `T ∖ {b}` stays in `T`
  have hstay : ∀ y ∈ T, y ≠ b → ∀ w ∈ H.verts, w ∉ T → H.mult s(y, w) = 0 := by
    intro y hy hyb w hw hwT
    have hdeg := deg_induce H hy hTsub
    have hyc : y = c ∨ y ≠ c := eq_or_ne y c
    have heq : deg H y = deg (induce H T) y := by
      rcases hyc with rfl | hyc
      · rw [hB.2.2.2.2.1, hTB.2.2.2.2.1]
      · have hya : y ≠ a := fun e => haT (e ▸ hy)
        rw [hB.2.2.2.2.2.1 y (hTsub hy) hya hyc, hTB.2.2.2.2.2.1 y hy hyb hyc]
    have hz : ∑ w ∈ H.verts \ T, H.mult s(y, w) = 0 := by omega
    exact (Finset.sum_eq_zero_iff.mp hz) w (Finset.mem_sdiff.mpr ⟨hw, hwT⟩)
  refine ⟨b, hbS, Ne.symm hab, hTB.2.2.1, fun hconn => ?_⟩
  have hcV : c ∈ H.verts.erase b := Finset.mem_erase.mpr ⟨Ne.symm hTB.2.2.1, hTsub hTB.2.1⟩
  have haV : a ∈ H.verts.erase b := Finset.mem_erase.mpr ⟨hab, by rw [hS]; exact Finset.mem_union_left _ ha'⟩
  have hreach := hconn c hcV a haV
  have key : ∀ y, Relation.ReflTransGen (AdjIn H (H.verts.erase b)) c y → y ∈ T := by
    intro y hy
    induction hy with
    | refl => exact hTB.2.1
    | @tail y z _ hyz ih =>
      by_contra hzT
      have hyb : y ≠ b := (Finset.mem_erase.mp hyz.1).1
      exact hyz.2.2 (hstay y ih hyb z (Finset.mem_erase.mp hyz.2.1).2 hzT)
  exact haT (key a hreach)

/-- **The kinds of a chain filling a T-vine** (with no interior cut atom): a single T-vine. -/
theorem kinds_of_tvine {H : UMultigraph V} {S : Finset V} {a c : V} {ks : List EnlKind} (h : ChainU H S a c ks)
    (hT : IsTVineU H a c) (hS : H.verts = S) (hcut : ∀ v ∈ Core.interior H a c, ConnOn H (H.verts.erase v)) :
    ks = [.T] := by
  obtain ⟨-, -, -, hne, -⟩ := chain_card h
  rcases List.eq_nil_or_concat ks with h0 | ⟨ks', k, rfl⟩
  · exact absurd h0 hne
  · rw [List.concat_eq_append] at h
    rcases List.eq_nil_or_concat ks' with h0' | ⟨ks'', k', rfl⟩
    · subst h0'
      have hk := chain_single_inv (k := k) h
      rcases card_isVineKindU hk with ⟨-, h2⟩ | ⟨-, ⟨m, hm⟩, -⟩ | ⟨rfl, -⟩
      · have := (card_isTVineU hT).2; rw [hS] at this; rw [induce_verts] at h2; omega
      · have := (card_isTVineU hT).1; rw [hS] at this; rw [induce_verts] at hm
        obtain ⟨j, hj⟩ := this; omega
      · rfl
    · exfalso
      rw [List.concat_eq_append] at h
      obtain ⟨b, hbS, hba, hbc, hnc⟩ := chain_cut_atom (by simp) h hT.1 hS
      exact hnc (hcut b (mem_interior.mpr ⟨hS ▸ hbS, hba, hbc⟩))

end WaveTurbulence.TVine.Struct
