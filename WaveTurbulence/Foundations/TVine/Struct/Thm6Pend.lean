/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Thm6Spine
public import WaveTurbulence.Foundations.TVine.Struct.Attach
import Mathlib.Tactic

/-!
# N3 Theorem 6, part 4: the pendant (packet L3)

* `KChain`: the `𝒦`-chain in decreasing order `Kd 0 = H ⊃ Kd 1 ⊃ ⋯ ⊃ Kd (s-1) ⊃ Kd s = ∅`;
* the pendant layers `Y k = Kd k ∖ Kd (k+1)`: `Kd_inner` (all bonds of `Kd (k+1)` go into `Y k`), `cut_Y`,
  `eW_Y_succ` (consecutive `Y`'s: 2 bonds), `eW_Y_far` (non-consecutive: none), `Y_piece`;
* `two_exits`: a 2-cut side whose atoms (inside and outside) each carry at most one of its bonds has two single exit
  bonds with distinct inner and distinct outer ends; `exit_le_one_inner`, `exit_le_one_outer` (Lemma A and the
  joints).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

variable {V : Type*} [DecidableEq V]

/-- The `𝒦`-chain in decreasing order: `Kd k ⊃ Kd l` for `k < l ≤ s`, `Kd s = ∅`, every `𝒦`-side is some `Kd k`. -/
structure KChain (G : UMultigraph V) (v₁ v₂ : V) where
  s : ℕ
  Kd : ℕ → Finset V
  side : ∀ k, k < s → IsKSide G v₁ v₂ (Kd k)
  strict : ∀ k l, k < l → l ≤ s → Kd l ⊂ Kd k
  all : ∀ K, IsKSide G v₁ v₂ K → ∃ k, k < s ∧ Kd k = K
  bot : ∀ k, s ≤ k → Kd k = ∅

theorem exists_kChain {G : UMultigraph V} {v₁ v₂ : V} (hT : T6Ctx G v₁ v₂) : Nonempty (KChain G v₁ v₂) := by
  classical
  set C := G.verts.powerset.filter fun K => IsKSide G v₁ v₂ K with hC
  have hmem : ∀ K, K ∈ C ↔ IsKSide G v₁ v₂ K := fun K => by
    rw [hC, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  obtain ⟨l, hl, hp⟩ := exists_chain_list C fun A hA B hB =>
    kside_chain hT ((hmem A).mp hA) ((hmem B).mp hB)
  have hlmem : ∀ K, K ∈ l ↔ IsKSide G v₁ v₂ K := fun K => by rw [← List.mem_toFinset, hl, hmem]
  have hget : ∀ i j (hi : i < l.length) (hj : j < l.length), i < j → l[i] ⊂ l[j] := by
    intro i j hi hj hij
    exact List.pairwise_iff_getElem.mp hp i j hi hj hij
  refine ⟨{
    s := l.length
    Kd := fun k => if h : k < l.length then l[l.length - 1 - k] else ∅
    side := ?_
    strict := ?_
    all := ?_
    bot := ?_ }⟩
  · intro k hk
    simp only [hk, dite_true]; exact (hlmem _).mp (List.getElem_mem _)
  · intro k m hkm hm
    have hk : k < l.length := by omega
    by_cases hm' : m < l.length
    · simp only [hk, hm', dite_true]; exact hget _ _ (by omega) (by omega) (by omega)
    · simp only [hk, hm', dite_true, dite_false]
      exact Finset.empty_ssubset.mpr ((hlmem _).mp (List.getElem_mem _)).2.2.2.1
  · intro K hK
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem ((hlmem K).mpr hK)
    refine ⟨l.length - 1 - i, by omega, ?_⟩
    simp only [show l.length - 1 - i < l.length by omega, dite_true]
    rw [← he]; congr 1; omega
  · intro k hk
    simp only [show ¬ k < l.length by omega, dite_false]

namespace KChain

variable {G : UMultigraph V} {v₁ v₂ : V} (C : KChain G v₁ v₂)

theorem anti {k l : ℕ} (h : k ≤ l) : C.Kd l ⊆ C.Kd k := by
  rcases Nat.lt_or_ge l C.s with hl | hl
  · rcases h.lt_or_eq with h | rfl
    · exact (C.strict k l h hl.le).1
    · exact subset_rfl
  · rw [C.bot l hl]; exact Finset.empty_subset _

theorem Kd_sub (k : ℕ) : C.Kd k ⊆ G.verts := by
  rcases Nat.lt_or_ge k C.s with hk | hk
  · exact (C.side k hk).1
  · rw [C.bot k hk]; exact Finset.empty_subset _

/-- The top of the chain is the pendant. -/
theorem Kd_zero_eq_Hp (hT : T6Ctx G v₁ v₂) : C.Kd 0 = Hp G v₁ v₂ := by
  rcases Nat.eq_zero_or_pos C.s with hs | hs
  · rw [C.bot 0 (by omega)]
    rcases Hp_cases hT with h | h
    · exact h.symm
    · obtain ⟨k, hk, -⟩ := C.all _ h; omega
  · apply Finset.Subset.antisymm (subset_Hp (C.side 0 hs))
    rcases Hp_cases hT with h | h
    · rw [h]; exact Finset.empty_subset _
    · obtain ⟨k, hk, he⟩ := C.all _ h
      rw [← he]; exact C.anti (Nat.zero_le k)

/-- The pendant layers. -/
def Y (k : ℕ) : Finset V := C.Kd k \ C.Kd (k + 1)

theorem Y_sub (k : ℕ) : C.Y k ⊆ C.Kd k := Finset.sdiff_subset

theorem Y_nonempty {k : ℕ} (hk : k < C.s) : (C.Y k).Nonempty := by
  obtain ⟨x, hx⟩ := Finset.exists_of_ssubset (C.strict k (k + 1) (Nat.lt_succ_self k) hk)
  exact ⟨x, Finset.mem_sdiff.mpr hx⟩

theorem Kd_eq_union (k : ℕ) : C.Kd k = C.Y k ∪ C.Kd (k + 1) := by
  rw [Y, Finset.sdiff_union_of_subset (C.anti (Nat.le_succ k))]

theorem Y_disjoint_Kd (k : ℕ) : Disjoint (C.Y k) (C.Kd (k + 1)) := Finset.sdiff_disjoint

theorem Y_disjoint {k l : ℕ} (h : k ≠ l) : Disjoint (C.Y k) (C.Y l) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact (C.Y_disjoint_Kd k).mono_right ((C.Y_sub l).trans (C.anti (by omega)))
  · exact ((C.Y_disjoint_Kd l).mono_right ((C.Y_sub k).trans (C.anti (by omega)))).symm

/-- Every bond of `Kd (k+1)` leaving it goes into `Y k`; `Y k` has cut 4 (`k + 1 < s`). -/
theorem Kd_inner (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 < C.s) :
    eW (wG G) (C.Kd (k + 1)) (G.verts \ C.Kd k) = 0 ∧ eW (wG G) (C.Y k) (C.Kd (k + 1)) = 2 ∧
      cut G (C.Y k) = 4 := by
  have hw := symm_wG G
  have hK0 := C.side k (by omega)
  have hK1 := C.side (k + 1) hk
  have hsplit := cut_union_disjoint (G := G) ((C.Y_sub k).trans hK0.1) hK1.1 (C.Y_disjoint_Kd k)
  rw [← C.Kd_eq_union, hK0.2.2.2.2, hK1.2.2.2.2] at hsplit
  have hYne := C.Y_nonempty (show k < C.s by omega)
  have hY2 : 2 ≤ cut G (C.Y k) := by
    obtain ⟨x, hx⟩ := hYne
    exact two_le_cut hT.cc ((C.Y_sub k).trans hK0.1) hx hT.mem₁
      (fun h => hK0.2.1 (C.Y_sub k h))
  have hYne2 : cut G (C.Y k) ≠ 2 := by
    intro h2
    exact hT.noPend' (K₁ := C.Y k) (K₂ := C.Kd (k + 1))
      ⟨(C.Y_sub k).trans hK0.1, fun h => hK0.2.1 (C.Y_sub k h), fun h => hK0.2.2.1 (C.Y_sub k h), hYne, h2⟩ hK1
      (C.Y_disjoint_Kd k)
  -- the cut of Kd (k+1) splits between Y k and the outside of Kd k
  have hcut1 : cut G (C.Kd (k + 1)) =
      eW (wG G) (C.Kd (k + 1)) (C.Y k) + eW (wG G) (C.Kd (k + 1)) (G.verts \ C.Kd k) := by
    rw [cut_eq_eW]
    have : G.verts \ C.Kd (k + 1) = C.Y k ∪ (G.verts \ C.Kd k) := by
      ext x
      have h1 : x ∈ C.Kd (k + 1) → x ∈ C.Kd k := fun h => C.anti (Nat.le_succ k) h
      have h2 : x ∈ C.Kd k → x ∈ G.verts := fun h => hK0.1 h
      simp only [Y, Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [this, eW_union_right _ (Finset.disjoint_left.mpr fun x h1 h2 =>
      (Finset.mem_sdiff.mp h2).2 (C.Y_sub k h1))]
  rw [hK1.2.2.2.2, eW_comm hw (C.Kd (k + 1)) (C.Y k)] at hcut1
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Consecutive pendant layers are joined by 2 bonds. -/
theorem eW_Y_succ (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 < C.s) :
    eW (wG G) (C.Y k) (C.Y (k + 1)) = 2 := by
  have h := (C.Kd_inner hT hk).2.1
  rw [C.Kd_eq_union (k + 1), eW_union_right _ (C.Y_disjoint_Kd (k + 1))] at h
  have h0 : eW (wG G) (C.Y k) (C.Kd (k + 1 + 1)) = 0 := by
    rcases Nat.lt_or_ge (k + 2) C.s with h2 | h2
    · have hz := (C.Kd_inner hT (k := k + 1) h2).1
      rw [eW_comm (symm_wG G)]
      refine Nat.eq_zero_of_le_zero ((eW_mono_right _ fun x hx => ?_).trans hz.le)
      exact Finset.mem_sdiff.mpr ⟨(C.side k (by omega)).1 (C.Y_sub k hx),
        (Finset.mem_sdiff.mp hx).2⟩
    · rw [C.bot (k + 1 + 1) (by omega), eW_empty_right]
  omega

/-- Non-consecutive pendant layers are not joined. -/
theorem eW_Y_far (hT : T6Ctx G v₁ v₂) {k l : ℕ} (hkl : k + 2 ≤ l) :
    eW (wG G) (C.Y k) (C.Y l) = 0 := by
  rcases Nat.lt_or_ge (k + 2) C.s with h2 | h2
  · have hz := (C.Kd_inner hT (k := k + 1) h2).1
    rw [eW_comm (symm_wG G)]
    refine Nat.eq_zero_of_le_zero ((eW_mono_left _ ((C.Y_sub l).trans (C.anti (by omega)))).trans
      ((eW_mono_right _ fun x hx => ?_).trans hz.le))
    exact Finset.mem_sdiff.mpr ⟨(C.side k (by omega)).1 (C.Y_sub k hx), (Finset.mem_sdiff.mp hx).2⟩
  · have : C.Y l = ∅ := by
      rw [Y, C.bot l (by omega), Finset.empty_sdiff]
    rw [this, eW_empty_right]

/-- **A pendant layer is a piece.** -/
theorem Y_piece (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k < C.s) : C.Y k ∈ piecesU G v₁ v₂ := by
  have hK0 := C.side k hk
  obtain ⟨u, hu⟩ := C.Y_nonempty hk
  have huK := C.Y_sub k hu
  have hsubI : C.Y k ⊆ Core.interior G v₁ v₂ :=
    ((C.Y_sub k).trans (subset_interior_of_joint_free hK0.1 hK0.2.1 hK0.2.2.1))
  refine mem_piecesU_of_class hsubI hu (fun w hw => ?_) (fun w hw hwY => ?_)
  · have hwK := C.Y_sub k hw
    rw [samePieceU_iff_sides hT (hK0.1 huK) (hK0.1 hwK)]
    refine ⟨fun X hX => ?_, fun K hK => ?_⟩
    · rcases kside_xside hT hK0 hX with h | h
      · exact ⟨fun _ => h hwK, fun _ => h huK⟩
      · exact ⟨fun h' => absurd h' (Finset.disjoint_left.mp h huK),
          fun h' => absurd h' (Finset.disjoint_left.mp h hwK)⟩
    · obtain ⟨l, hl, rfl⟩ := C.all K hK
      rcases Nat.lt_or_ge k l with h | h
      · have hsub := C.anti (show k + 1 ≤ l by omega)
        exact ⟨fun h' => absurd (hsub h') (Finset.mem_sdiff.mp hu).2,
          fun h' => absurd (hsub h') (Finset.mem_sdiff.mp hw).2⟩
      · exact ⟨fun _ => C.anti h hwK, fun _ => C.anti h huK⟩
  · rw [samePieceU_iff_sides hT (hK0.1 huK) (interior_subset_verts _ _ hw)]
    rintro ⟨-, hkk⟩
    by_cases hwK : w ∈ C.Kd k
    · have hwK1 : w ∈ C.Kd (k + 1) := by
        by_contra h; exact hwY (Finset.mem_sdiff.mpr ⟨hwK, h⟩)
      have hs1 : k + 1 < C.s := by
        by_contra h; push Not at h; rw [C.bot (k + 1) h] at hwK1; exact absurd hwK1 (Finset.notMem_empty _)
      exact (Finset.mem_sdiff.mp hu).2 ((hkk _ (C.side (k + 1) hs1)).mpr hwK1)
    · exact hwK ((hkk _ hK0).mp huK)

end KChain

/-! ## Exit bonds of a 2-cut side -/

section exits

variable {G : UMultigraph V}

/-- A 2-cut side whose atoms, inside and outside, each carry at most one of its bonds has exactly two exit bonds,
single, with distinct inner ends and distinct outer ends. -/
theorem two_exits (hl : Loopless (wG G)) {H : Finset V} (h2 : cut G H = 2)
    (hin : ∀ y ∈ H, eW (wG G) {y} (G.verts \ H) ≤ 1) (hout : ∀ x ∈ G.verts \ H, eW (wG G) {x} H ≤ 1) :
    ∃ y ∈ H, ∃ y' ∈ H, ∃ x ∈ G.verts \ H, ∃ x' ∈ G.verts \ H, y ≠ y' ∧ x ≠ x' ∧
      G.mult s(y, x) = 1 ∧ G.mult s(y', x') = 1 := by
  have hw := symm_wG G
  rw [cut_eq_eW] at h2
  obtain ⟨y, hy, x, hx, hyx⟩ := exists_pos_of_eW_pos (show 0 < eW (wG G) H (G.verts \ H) by omega)
  have hyx1 : G.mult s(y, x) = 1 := by
    have := (le_eW_of_mem (w := wG G) (Finset.mem_singleton_self y) hx).trans (hin y hy)
    exact le_antisymm this hyx
  -- remove the row of y
  have hrow : eW (wG G) H (G.verts \ H) = eW (wG G) {y} (G.verts \ H) + eW (wG G) (H.erase y) (G.verts \ H) := by
    rw [← eW_union_left _ (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase y H)), ← Finset.insert_eq,
      Finset.insert_erase hy]
  have hrowy : eW (wG G) {y} (G.verts \ H) = 1 := by
    have := (le_eW_of_mem (w := wG G) (Finset.mem_singleton_self y) hx)
    have := hin y hy
    unfold wG at *; omega
  obtain ⟨y', hy', x', hx', hyx'⟩ :=
    exists_pos_of_eW_pos (show 0 < eW (wG G) (H.erase y) (G.verts \ H) by omega)
  obtain ⟨hy'y, hy'H⟩ := Finset.mem_erase.mp hy'
  have hyx'1 : G.mult s(y', x') = 1 :=
    le_antisymm ((le_eW_of_mem (w := wG G) (Finset.mem_singleton_self y') hx').trans (hin y' hy'H)) hyx'
  refine ⟨y, hy, y', hy'H, x, hx, x', hx', Ne.symm hy'y, ?_, hyx1, hyx'1⟩
  rintro rfl
  -- the column of x carries two bonds
  have hcol : 2 ≤ eW (wG G) {x} H := by
    have hsub : ({y, y'} : Finset V) ⊆ H := by
      intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have h1 : eW (wG G) {x} {y, y'} ≤ eW (wG G) {x} H := eW_mono_right _ hsub
    have h2' : eW (wG G) {x} {y, y'} = G.mult s(x, y) + G.mult s(x, y') := by
      unfold eW; rw [Finset.sum_singleton, Finset.sum_pair (Ne.symm hy'y)]; rfl
    rw [Sym2.eq_swap] at hyx1 hyx'1
    omega
  have := hout x hx
  omega

/-- Inner atoms of a 2-cut side of a T6 context with large pieces carry at most one of its bonds (Lemma A). -/
theorem exit_le_one_inner {v₁ v₂ : V} (hT : T6Ctx G v₁ v₂) (hbig : ∀ P ∈ piecesU G v₁ v₂, 2 ≤ P.card)
    {K : Finset V} (hK : IsKSide G v₁ v₂ K) : ∀ y ∈ K, eW (wG G) {y} (G.verts \ K) ≤ 1 := by
  intro y hy
  refine attachU hT.cc (fun v hv => ?_) hbig hK.1 hK.2.2.2.2
    (subset_interior_of_joint_free hK.1 hK.2.1 hK.2.2.1 hy) hy
  rw [mem_interior] at hv; exact hT.deg4 v hv.1 hv.2.1 hv.2.2

/-- Outer atoms of a 2-cut side `K` (joint-free) carry at most one of its bonds: interior atoms by Lemma A, joints
because a joint with both bonds into `K` would close `K ∪ {joint}` off. -/
theorem exit_le_one_outer {v₁ v₂ : V} (hT : T6Ctx G v₁ v₂) (hbig : ∀ P ∈ piecesU G v₁ v₂, 2 ≤ P.card)
    {K : Finset V} (hK : IsKSide G v₁ v₂ K) : ∀ x ∈ G.verts \ K, eW (wG G) {x} K ≤ 1 := by
  intro x hx
  obtain ⟨hxV, hxK⟩ := Finset.mem_sdiff.mp hx
  have hjoint : ∀ j, j ∈ G.verts → j ∉ K → deg G j = 2 → ∀ o, o ∈ G.verts → o ∉ K → o ≠ j →
      eW (wG G) {j} K ≤ 1 := by
    intro j hjV hjK hdj o hoV hoK hoj
    by_contra hgt
    push Not at hgt
    have hcu := cut_union_disjoint (G := G) (Finset.singleton_subset_iff.mpr hjV) hK.1
      (Finset.disjoint_singleton_left.mpr hjK)
    rw [cut_singleton hT.cc hjV, hdj, hK.2.2.2.2] at hcu
    have hle : eW (wG G) {j} K ≤ 2 := by
      have := deg_split (G := G) hT.cc (X := insert j K) (Finset.insert_subset hjV hK.1)
        (Finset.mem_insert_self j K)
      rw [Finset.erase_insert hjK, hdj] at this
      omega
    have := two_le_cut hT.cc (Finset.union_subset (Finset.singleton_subset_iff.mpr hjV) hK.1)
      (Finset.mem_union_left _ (Finset.mem_singleton_self j)) hoV
      (fun h => (Finset.mem_union.mp h).elim (fun h' => hoj (Finset.mem_singleton.mp h')) hoK)
    omega
  by_cases h1 : x = v₁
  · rw [h1] at hxV hxK ⊢; exact hjoint v₁ hxV hxK hT.deg₁ v₂ hT.mem₂ hK.2.2.1 hT.ne.symm
  by_cases h2 : x = v₂
  · rw [h2] at hxV hxK ⊢; exact hjoint v₂ hxV hxK hT.deg₂ v₁ hT.mem₁ hK.2.1 hT.ne
  have hxI : x ∈ Core.interior G v₁ v₂ := mem_interior.mpr ⟨hxV, h1, h2⟩
  exact attachU_compl hT.cc (fun v hv => by rw [mem_interior] at hv; exact hT.deg4 v hv.1 hv.2.1 hv.2.2) hbig
    hK.1 hK.2.2.2.2 hxI hxK

end exits

end WaveTurbulence.TVine.Struct
