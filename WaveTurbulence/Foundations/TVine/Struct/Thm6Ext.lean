/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Thm6Pend
import Mathlib.Tactic

/-!
# N3 Theorem 6, part 5: the extended spine as a function (packet L3)

* piece cuts under the U-level piece shape (`PieceShapeU`): `cut_pair`, `cut_triple`, `piece_cut_cases`;
* `cut_E_interior`: an interior layer that is not the pendant has cut 4;
* the skip index `pbIdx` (the P-b layer, if any), the reindexing `sk`, the spine length `r`, and the extended spine
  `Ext j = E (sk j) ∖ H` (`Ext 0 = {v₂}`, `Ext (r+1) = {v₁}`), with: pieces, disjointness, cover, bond counts,
  `r = 0 ↔ σ = 1`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

variable {V : Type*} [DecidableEq V]

/-! ## The U-level piece shape and piece cuts -/

/-- N2 Prop 1.17(b) core shapes, U level. -/
def CoreShapeU (G : UMultigraph V) (P : Finset V) : Prop :=
  ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ P = {x, y, z} ∧ G.mult s(x, y) = 2 ∧
    ((G.mult s(y, z) = 1 ∧ G.mult s(x, z) = 1) ∨ (G.mult s(y, z) = 2 ∧ G.mult s(x, z) = 0) ∨
     (G.mult s(y, z) = 2 ∧ G.mult s(x, z) = 1))

/-- A 2-atom piece, U level. -/
def TwoAtomPieceU (G : UMultigraph V) (P : Finset V) : Prop :=
  ∃ a b : V, a ≠ b ∧ P = {a, b} ∧ (G.mult s(a, b) = 1 ∨ G.mult s(a, b) = 2)

/-- **The piece shape at U level.** -/
def PieceShapeU (G : UMultigraph V) (v₁ v₂ : V) : Prop :=
  ∃ core ∈ piecesU G v₁ v₂, CoreShapeU G core ∧ ∀ P ∈ piecesU G v₁ v₂, P ≠ core → TwoAtomPieceU G P

section piececut

variable {G : UMultigraph V} {v₁ v₂ : V}

theorem eW_singletons (a b : V) : eW (wG G) {a} {b} = G.mult s(a, b) := by
  unfold eW; simp [wG]

theorem cut_pair (hT : T6Ctx G v₁ v₂) {a b : V} (ha : a ∈ Core.interior G v₁ v₂)
    (hb : b ∈ Core.interior G v₁ v₂) (hab : a ≠ b) : cut G {a, b} + 2 * G.mult s(a, b) = 8 := by
  have haV := interior_subset_verts v₁ v₂ ha
  have hbV := interior_subset_verts v₁ v₂ hb
  rw [mem_interior] at ha hb
  have h := cut_union_disjoint (G := G) (Finset.singleton_subset_iff.mpr haV)
    (Finset.singleton_subset_iff.mpr hbV) (Finset.disjoint_singleton.mpr hab)
  rw [cut_singleton hT.cc haV, cut_singleton hT.cc hbV, hT.deg4 a haV ha.2.1 ha.2.2,
    hT.deg4 b hbV hb.2.1 hb.2.2, eW_singletons, ← Finset.insert_eq] at h
  exact h

theorem cut_triple (hT : T6Ctx G v₁ v₂) {x y z : V} (hx : x ∈ Core.interior G v₁ v₂)
    (hy : y ∈ Core.interior G v₁ v₂) (hz : z ∈ Core.interior G v₁ v₂) (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) :
    cut G {x, y, z} + 2 * (G.mult s(x, y) + G.mult s(y, z) + G.mult s(x, z)) = 12 := by
  have hzV := interior_subset_verts v₁ v₂ hz
  have hp := cut_pair hT hx hy hxy
  have hsub : ({x, y} : Finset V) ⊆ G.verts :=
    Finset.insert_subset (interior_subset_verts v₁ v₂ hx)
      (Finset.singleton_subset_iff.mpr (interior_subset_verts v₁ v₂ hy))
  have hd : Disjoint ({x, y} : Finset V) {z} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim (fun h => hxz h.symm) (fun h => hyz h.symm)
  have h := cut_union_disjoint (G := G) hsub (Finset.singleton_subset_iff.mpr hzV) hd
  have he : eW (wG G) {x, y} {z} = G.mult s(x, z) + G.mult s(y, z) := by
    unfold eW; rw [Finset.sum_pair hxy]; simp [wG]
  rw [cut_singleton hT.cc hzV, he] at h
  rw [mem_interior] at hz
  rw [hT.deg4 z hzV hz.2.1 hz.2.2] at h
  have hset : ({x, y} : Finset V) ∪ {z} = {x, y, z} := by
    ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hset] at h
  omega

/-- **Piece cuts.** Under the piece shape, a piece has cut 2 (the (D) core), 4 (a rung or a (B)/(C) core) or 6 (a
junction). -/
theorem piece_cut_cases (hT : T6Ctx G v₁ v₂) (hPS : PieceShapeU G v₁ v₂) {P : Finset V}
    (hP : P ∈ piecesU G v₁ v₂) :
    (cut G P = 2 ∧ ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ P = {x, y, z} ∧ G.mult s(x, y) = 2 ∧
        G.mult s(y, z) = 2 ∧ G.mult s(x, z) = 1) ∨
      (cut G P = 4 ∧ ((∃ a b : V, a ≠ b ∧ P = {a, b} ∧ G.mult s(a, b) = 2) ∨
        (∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ P = {x, y, z} ∧ G.mult s(x, y) = 2 ∧
          ((G.mult s(y, z) = 1 ∧ G.mult s(x, z) = 1) ∨ (G.mult s(y, z) = 2 ∧ G.mult s(x, z) = 0))))) ∨
      (cut G P = 6 ∧ ∃ a b : V, a ≠ b ∧ P = {a, b} ∧ G.mult s(a, b) = 1) := by
  obtain ⟨core, hcore, hcs, hrest⟩ := hPS
  have hPI := (piece_props hP).1
  by_cases hc : P = core
  · subst hc
    obtain ⟨x, y, z, hxy, hyz, hxz, rfl, hm, hcase⟩ := hcs
    have hx := hPI (show x ∈ ({x, y, z} : Finset V) by simp)
    have hy := hPI (show y ∈ ({x, y, z} : Finset V) by simp)
    have hz := hPI (show z ∈ ({x, y, z} : Finset V) by simp)
    have h := cut_triple hT hx hy hz hxy hyz hxz
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; left; exact ⟨by omega, Or.inr ⟨x, y, z, hxy, hyz, hxz, rfl, hm, Or.inl ⟨h1, h2⟩⟩⟩
    · right; left; exact ⟨by omega, Or.inr ⟨x, y, z, hxy, hyz, hxz, rfl, hm, Or.inr ⟨h1, h2⟩⟩⟩
    · left; exact ⟨by omega, x, y, z, hxy, hyz, hxz, rfl, hm, h1, h2⟩
  · obtain ⟨a, b, hab, rfl, hm⟩ := hrest P hP hc
    have h := cut_pair hT (hPI (show a ∈ ({a, b} : Finset V) by simp))
      (hPI (show b ∈ ({a, b} : Finset V) by simp)) hab
    rcases hm with hm | hm
    · right; right; exact ⟨by omega, a, b, hab, rfl, hm⟩
    · right; left; exact ⟨by omega, Or.inl ⟨a, b, hab, rfl, hm⟩⟩

end piececut

/-! ## Interior layers -/

namespace XLayers

variable {G : UMultigraph V} {v₁ v₂ : V} (L : XLayers G v₁ v₂)

/-- An interior layer that is not the pendant has 2 bonds on each side, hence cut 4. -/
theorem cut_E_interior (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 < L.t) (hne : L.E (k + 1) ≠ Hp G v₁ v₂) :
    eW (wG G) (L.X k) (L.E (k + 1)) = 2 ∧ eW (wG G) (L.E (k + 1)) (G.verts \ L.X (k + 1)) = 2 ∧
      cut G (L.E (k + 1)) = 4 := by
  have hca := L.cut_X k (by omega)
  rw [L.eW_compl_X_right, L.skip_zero hT hk.le hne, add_zero] at hca
  have hca1 := L.cut_X (k + 1) hk
  rw [L.eW_X_succ_left, L.skip_zero hT hk.le hne, zero_add] at hca1
  have hcE := L.cut_E_succ k
  refine ⟨hca, hca1, by omega⟩

/-- A nonempty pendant lies in a single layer, so `E i ∖ H` is `E i` unless `H ⊆ E i`. -/
theorem E_sdiff_Hp_of_ne (hT : T6Ctx G v₁ v₂) {i j : ℕ} (hij : i ≠ j) (hH : Hp G v₁ v₂ ⊆ L.E i) :
    L.E j \ Hp G v₁ v₂ = L.E j := by
  rw [Finset.sdiff_eq_self_iff_disjoint]
  exact ((L.E_disjoint hij).mono_left hH).symm

/-- **Removing the pendant does not change the weight between two non-pendant layers.** -/
theorem eW_sdiff_Hp (hT : T6Ctx G v₁ v₂) {c d : ℕ} (hcd : c ≠ d) (hct : c ≤ L.t) (hdt : d ≤ L.t)
    (hc : L.E c ≠ Hp G v₁ v₂) (hd : L.E d ≠ Hp G v₁ v₂) :
    eW (wG G) (L.E c \ Hp G v₁ v₂) (L.E d \ Hp G v₁ v₂) = eW (wG G) (L.E c) (L.E d) := by
  have hw := symm_wG G
  rcases (Hp G v₁ v₂).eq_empty_or_nonempty with hH | hH
  · rw [hH, Finset.sdiff_empty, Finset.sdiff_empty]
  obtain ⟨i, hi0, hit, hiE⟩ := L.Hp_loc hT hH
  -- the pendant has no bond to a layer other than its own
  have hzero : ∀ e, e ≠ i → e ≤ L.t → L.E i ≠ Hp G v₁ v₂ → eW (wG G) (Hp G v₁ v₂) (L.E e) = 0 := by
    intro e hei het hne
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    obtain ⟨hA, hB, -⟩ := L.Hp_pa hT hit hiE hne hH
    rcases Nat.lt_or_gt_of_ne hei with h | h
    · exact Nat.eq_zero_of_le_zero ((eW_mono_right _ (L.E_subset_X (by omega))).trans hA.le)
    · refine Nat.eq_zero_of_le_zero ((eW_mono_right _ fun x hx => ?_).trans hB.le)
      exact Finset.mem_sdiff.mpr ⟨L.E_sub e hx, Finset.disjoint_left.mp (L.E_disjoint_X h) hx⟩
  by_cases hic : i = c
  · rw [← hic] at hc ⊢
    have hdi : d ≠ i := fun h => hcd (hic ▸ h.symm)
    rw [L.E_sdiff_Hp_of_ne hT (Ne.symm hdi) hiE]
    have hsplit : L.E i = (L.E i \ Hp G v₁ v₂) ∪ Hp G v₁ v₂ := (Finset.sdiff_union_of_subset hiE).symm
    conv_rhs => rw [hsplit]
    rw [eW_union_left _ Finset.sdiff_disjoint, hzero d hdi hdt hc, add_zero]
  by_cases hid : i = d
  · rw [← hid] at hd ⊢
    have hci : c ≠ i := fun h => hcd (h.trans hid)
    rw [L.E_sdiff_Hp_of_ne hT (Ne.symm hci) hiE]
    have hsplit : L.E i = (L.E i \ Hp G v₁ v₂) ∪ Hp G v₁ v₂ := (Finset.sdiff_union_of_subset hiE).symm
    conv_rhs => rw [hsplit]
    rw [eW_union_right _ Finset.sdiff_disjoint, eW_comm hw (L.E c) (Hp G v₁ v₂), hzero c hci hct hd, add_zero]
  rw [L.E_sdiff_Hp_of_ne hT hic hiE, L.E_sdiff_Hp_of_ne hT hid hiE]

/-! ## The skip index -/

/-- The P-b layer (the pendant forming a whole layer), if any. -/
noncomputable def pbIdx (G : UMultigraph V) (v₁ v₂ : V) (L : XLayers G v₁ v₂) : Option ℕ := by
  classical
  exact if h : ∃ i, 0 < i ∧ i < L.t ∧ L.E i = Hp G v₁ v₂ then some (Nat.find h) else none

theorem pbIdx_some {i₀ : ℕ} (h : pbIdx G v₁ v₂ L = some i₀) : 0 < i₀ ∧ i₀ < L.t ∧ L.E i₀ = Hp G v₁ v₂ := by
  classical
  unfold pbIdx at h
  split_ifs at h with hh
  · simp only [Option.some.injEq] at h
    subst h
    exact Nat.find_spec hh

theorem pbIdx_none (h : pbIdx G v₁ v₂ L = none) {i : ℕ} (h0 : 0 < i) (hi : i < L.t) :
    L.E i ≠ Hp G v₁ v₂ := by
  classical
  unfold pbIdx at h
  split_ifs at h with hh
  intro he
  exact hh ⟨i, h0, hi, he⟩

/-- The reindexing that skips the P-b layer. -/
noncomputable def sk (j : ℕ) : ℕ :=
  match pbIdx G v₁ v₂ L with
  | none => j
  | some i₀ => if j < i₀ then j else j + 1

/-- The number of spine pieces. -/
noncomputable def r : ℕ :=
  match pbIdx G v₁ v₂ L with
  | none => L.t - 1
  | some _ => L.t - 2

/-- The extended spine `(v₂, G₁, …, G_r, v₁)`. -/
noncomputable def Ext (j : ℕ) : Finset V := L.E (L.sk j) \ Hp G v₁ v₂

theorem sk_zero : L.sk 0 = 0 := by
  unfold sk
  rcases h : pbIdx G v₁ v₂ L with _ | i₀
  · rfl
  · have := (L.pbIdx_some h).1
    dsimp only; rw [if_pos this]

theorem sk_last : L.sk (L.r + 1) = L.t := by
  unfold sk r
  have ht := L.two_le
  rcases h : pbIdx G v₁ v₂ L with _ | i₀
  · dsimp only; omega
  · have := L.pbIdx_some h
    dsimp only; rw [if_neg (show ¬ L.t - 2 + 1 < i₀ by omega)]; omega

theorem sk_lt {j j' : ℕ} (h : j < j') : L.sk j < L.sk j' := by
  unfold sk
  rcases pbIdx G v₁ v₂ L with _ | i₀
  · exact h
  · dsimp only; split_ifs <;> omega

theorem sk_mono {j j' : ℕ} (h : j ≤ j') : L.sk j ≤ L.sk j' := by
  rcases h.lt_or_eq with h | rfl
  · exact (L.sk_lt h).le
  · exact le_rfl

theorem sk_le {j : ℕ} (h : j ≤ L.r + 1) : L.sk j ≤ L.t := L.sk_last ▸ L.sk_mono h

theorem sk_pos {j : ℕ} (h : 1 ≤ j) : 0 < L.sk j := lt_of_le_of_lt (Nat.zero_le _) (L.sk_zero ▸ L.sk_lt h)

theorem sk_lt_t {j : ℕ} (h : j ≤ L.r) : L.sk j < L.t := L.sk_last ▸ L.sk_lt (Nat.lt_succ_of_le h)

theorem sk_succ (j : ℕ) : L.sk (j + 1) = L.sk j + 1 ∨
    (L.sk (j + 1) = L.sk j + 2 ∧ pbIdx G v₁ v₂ L = some (L.sk j + 1)) := by
  unfold sk
  rcases h : pbIdx G v₁ v₂ L with _ | i₀
  · left; rfl
  · dsimp only
    simp only [Option.some.injEq]
    split_ifs with h1 h2 h2 <;> first | (left; omega) | (right; constructor <;> omega) | omega

theorem sk_ne_pb {j i₀ : ℕ} (h : pbIdx G v₁ v₂ L = some i₀) : L.sk j ≠ i₀ := by
  unfold sk; rw [h]; dsimp only; split_ifs <;> omega

/-- The layers of the extended spine are not the pendant. -/
theorem E_sk_ne_Hp (hT : T6Ctx G v₁ v₂) {j : ℕ} (hj : j ≤ L.r + 1) : L.E (L.sk j) ≠ Hp G v₁ v₂ := by
  intro he
  have hst := L.sk_le hj
  rcases Nat.eq_zero_or_pos (L.sk j) with h0 | h0
  · rw [h0, L.E_zero hT] at he
    exact (joint_not_mem_Hp hT).2 (he ▸ Finset.mem_singleton_self v₂)
  rcases hst.lt_or_eq with hlt | heq
  · rcases hpb : pbIdx G v₁ v₂ L with _ | i₀
    · exact L.pbIdx_none hpb h0 hlt he
    · have h1 := L.pbIdx_some hpb
      obtain ⟨x, hx⟩ := L.E_nonempty hst
      have hx' : x ∈ L.E i₀ := by rw [h1.2.2, ← he]; exact hx
      exact L.sk_ne_pb hpb (L.layer_unique hx hx')
  · rw [heq, L.E_top hT] at he
    exact (joint_not_mem_Hp hT).1 (he ▸ Finset.mem_singleton_self v₁)

/-- Every non-pendant layer is an extended-spine layer. -/
theorem sk_surj (hT : T6Ctx G v₁ v₂) {i : ℕ} (hi : i ≤ L.t) (hne : L.E i ≠ Hp G v₁ v₂) :
    ∃ j, j ≤ L.r + 1 ∧ L.sk j = i := by
  unfold sk r
  have ht := L.two_le
  rcases hpb : pbIdx G v₁ v₂ L with _ | i₀
  · exact ⟨i, by dsimp only; omega, rfl⟩
  · have h1 := L.pbIdx_some hpb
    have hii : i ≠ i₀ := fun h => hne (h ▸ h1.2.2)
    rcases Nat.lt_or_gt_of_ne hii with h | h
    · exact ⟨i, by dsimp only; omega, by dsimp only; rw [if_pos h]⟩
    · exact ⟨i - 1, by dsimp only; omega, by dsimp only; rw [if_neg (show ¬ i - 1 < i₀ by omega)]; omega⟩

/-! ## The extended spine -/

theorem Ext_zero (hT : T6Ctx G v₁ v₂) : L.Ext 0 = {v₂} := by
  unfold Ext; rw [L.sk_zero, L.E_zero hT, Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_left]
  exact (joint_not_mem_Hp hT).2

theorem Ext_last (hT : T6Ctx G v₁ v₂) : L.Ext (L.r + 1) = {v₁} := by
  unfold Ext; rw [L.sk_last, L.E_top hT, Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_singleton_left]
  exact (joint_not_mem_Hp hT).1

theorem Ext_sub_E (j : ℕ) : L.Ext j ⊆ L.E (L.sk j) := Finset.sdiff_subset

theorem Ext_sub (j : ℕ) : L.Ext j ⊆ G.verts := (L.Ext_sub_E j).trans (L.E_sub _)

theorem Ext_disjoint_Hp (j : ℕ) : Disjoint (L.Ext j) (Hp G v₁ v₂) := Finset.sdiff_disjoint

theorem Ext_disjoint {j j' : ℕ} (h : j ≠ j') : Disjoint (L.Ext j) (L.Ext j') :=
  (L.E_disjoint (fun he => h (by
    rcases Nat.lt_or_gt_of_ne h with h' | h'
    · exact absurd he (L.sk_lt h').ne
    · exact absurd he (L.sk_lt h').ne'))).mono (L.Ext_sub_E j) (L.Ext_sub_E j')

theorem Ext_nonempty (hT : T6Ctx G v₁ v₂) {j : ℕ} (hj : j ≤ L.r + 1) : (L.Ext j).Nonempty := by
  have hst := L.sk_le hj
  rcases (Hp G v₁ v₂).eq_empty_or_nonempty with hH | hH
  · unfold Ext; rw [hH, Finset.sdiff_empty]; exact L.E_nonempty hst
  obtain ⟨i, -, -, hiE⟩ := L.Hp_loc hT hH
  by_cases hi : i = L.sk j
  · unfold Ext
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact L.E_sk_ne_Hp hT hj (Finset.Subset.antisymm hsub (hi ▸ hiE))
  · unfold Ext; rw [L.E_sdiff_Hp_of_ne hT hi hiE]
    exact L.E_nonempty hst

theorem Ext_piece (hT : T6Ctx G v₁ v₂) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ L.r) : L.Ext j ∈ piecesU G v₁ v₂ :=
  L.spine_piece hT (L.sk_pos h1) (L.sk_lt_t hj) (L.Ext_nonempty hT (by omega))

/-- The weights between extended-spine members are those between their layers. -/
theorem eW_Ext (hT : T6Ctx G v₁ v₂) {a b : ℕ} (hab : a ≠ b) (ha : a ≤ L.r + 1) (hb : b ≤ L.r + 1) :
    eW (wG G) (L.Ext a) (L.Ext b) = eW (wG G) (L.E (L.sk a)) (L.E (L.sk b)) :=
  L.eW_sdiff_Hp hT (fun h => hab (by
      rcases Nat.lt_or_gt_of_ne hab with h' | h'
      · exact absurd h (L.sk_lt h').ne
      · exact absurd h (L.sk_lt h').ne')) (L.sk_le ha) (L.sk_le hb) (L.E_sk_ne_Hp hT ha) (L.E_sk_ne_Hp hT hb)

/-- **Consecutive members**: 2 bonds, or 1 across the P-b skip. -/
theorem eW_Ext_succ (hT : T6Ctx G v₁ v₂) {a : ℕ} (ha : a ≤ L.r) :
    (eW (wG G) (L.Ext a) (L.Ext (a + 1)) = 2 ∧ L.sk (a + 1) = L.sk a + 1) ∨
      (eW (wG G) (L.Ext a) (L.Ext (a + 1)) = 1 ∧ L.sk (a + 1) = L.sk a + 2) := by
  rw [L.eW_Ext hT (by omega) (by omega) (by omega)]
  rcases L.sk_succ a with h | ⟨h, hpb⟩
  · left
    refine ⟨?_, h⟩
    rw [h]
    exact L.eW_consec hT (by rw [← h]; exact L.sk_le (by omega)) (by rw [← h]; exact L.E_sk_ne_Hp hT (by omega))
      (L.E_sk_ne_Hp hT (by omega))
  · right
    refine ⟨?_, h⟩
    have h1 := L.pbIdx_some hpb
    rw [h]
    exact (L.pb_counts hT h1.2.1 h1.2.2).1

/-- **Non-consecutive members** are not joined. -/
theorem eW_Ext_far (hT : T6Ctx G v₁ v₂) {a b : ℕ} (hab : a + 2 ≤ b) (hb : b ≤ L.r + 1) :
    eW (wG G) (L.Ext a) (L.Ext b) = 0 := by
  rw [L.eW_Ext hT (by omega) (by omega) hb]
  have hlt : L.sk a + 2 ≤ L.sk b := by
    have h1 := L.sk_lt (show a < a + 1 by omega)
    have h2 := L.sk_lt (show a + 1 < b by omega)
    omega
  by_contra hpos
  obtain ⟨heq, hH⟩ := L.long_bond hT hlt (L.sk_le hb) (Nat.pos_of_ne_zero hpos)
  -- then `sk a + 1` is a skipped layer, so `sk (a+1) = sk a + 2 = sk b`, impossible since `a + 1 < b`
  have h1 := L.sk_lt (show a + 1 < b by omega)
  rcases L.sk_succ a with h | ⟨h, -⟩
  · exact L.E_sk_ne_Hp hT (j := a + 1) (by omega) (by rw [h]; exact hH)
  · omega

/-- At most one consecutive pair is joined by a single bond. -/
theorem Ext_one_unique (hT : T6Ctx G v₁ v₂) {a a' : ℕ} (ha : a ≤ L.r) (ha' : a' ≤ L.r)
    (h : eW (wG G) (L.Ext a) (L.Ext (a + 1)) = 1) (h' : eW (wG G) (L.Ext a') (L.Ext (a' + 1)) = 1) : a = a' := by
  have hs : L.sk (a + 1) = L.sk a + 2 := by
    rcases L.eW_Ext_succ hT ha with ⟨h2, -⟩ | ⟨-, hs⟩
    · omega
    · exact hs
  have hs' : L.sk (a' + 1) = L.sk a' + 2 := by
    rcases L.eW_Ext_succ hT ha' with ⟨h2, -⟩ | ⟨-, hs⟩
    · omega
    · exact hs
  unfold sk at hs hs'
  rcases hpb : pbIdx G v₁ v₂ L with _ | i₀ <;> rw [hpb] at hs hs'
  · dsimp only at hs; omega
  · dsimp only at hs hs'
    split_ifs at hs hs' <;> omega

/-- **`r = 0` iff `σ = 1`.** -/
theorem r_eq_zero_iff (hT : T6Ctx G v₁ v₂) : L.r = 0 ↔ G.mult s(v₁, v₂) = 1 := by
  have ht := L.two_le
  have hE0 := L.E_zero hT
  have hEt := L.E_top hT
  have hmul : eW (wG G) (L.E 0) (L.E L.t) = G.mult s(v₂, v₁) := by rw [hE0, hEt, eW_singletons]
  rw [Sym2.eq_swap] at hmul
  constructor
  · intro hr
    unfold r at hr
    rcases hpb : pbIdx G v₁ v₂ L with _ | i₀ <;> rw [hpb] at hr
    · dsimp only at hr; omega
    · dsimp only at hr
      have h1 := L.pbIdx_some hpb
      have hi : i₀ = 1 := by omega
      have := (L.pb_counts hT (k := 0) (by omega) (by rw [show (0 : ℕ) + 1 = i₀ by omega]; exact h1.2.2)).1
      rw [show (0 : ℕ) + 2 = L.t by omega, hmul] at this
      exact this
  · intro hσ
    have hpos : 0 < eW (wG G) (L.E 0) (L.E L.t) := by rw [hmul, hσ]; omega
    obtain ⟨heq, hH⟩ := L.long_bond hT (by omega) le_rfl hpos
    unfold r
    rcases hpb : pbIdx G v₁ v₂ L with _ | i₀
    · exact absurd hH (L.pbIdx_none hpb (by omega) (by omega))
    · dsimp only; omega

end XLayers

end WaveTurbulence.TVine.Struct
