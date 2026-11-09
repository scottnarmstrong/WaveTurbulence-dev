/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Thm6Chain
import Mathlib.Tactic

/-!
# N3 Theorem 6, part 2: the layers of the `𝒳`-chain and the long-bond lemma (packet L3)

* `eW` calculus: additivity over disjoint unions, monotonicity, symmetry;
* `XLayers`: the `𝒳`-chain `{v₂} = X 0 ⊂ X 1 ⊂ ⋯ ⊂ X (t-1) = verts ∖ {v₁} ⊂ X t = verts` (every `𝒳`-side is one
  `X i`), and its layers `E 0 = {v₂}`, `E i = X i ∖ X (i-1)`;
* `Hp`: the pendant `H`, the union of all `𝒦`-sides (the largest one, or `∅`);
* `long_bond`: a bond between layers `a` and `b ≥ a + 2` forces `b = a + 2` and `E (a+1) = H`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

variable {V : Type*} [DecidableEq V]

/-! ## `eW` calculus -/

section eWcalc

variable {w : V → V → ℕ}

theorem eW_union_right (A : Finset V) {B C : Finset V} (h : Disjoint B C) :
    eW w A (B ∪ C) = eW w A B + eW w A C := by
  unfold eW; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_union h

theorem eW_union_left {A B : Finset V} (C : Finset V) (h : Disjoint A B) :
    eW w (A ∪ B) C = eW w A C + eW w B C := by
  unfold eW; exact Finset.sum_union h

theorem eW_mono_right (A : Finset V) {B B' : Finset V} (h : B ⊆ B') : eW w A B ≤ eW w A B' := by
  unfold eW
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset h

theorem eW_mono_left {A A' : Finset V} (B : Finset V) (h : A ⊆ A') : eW w A B ≤ eW w A' B := by
  unfold eW; exact Finset.sum_le_sum_of_subset h

theorem eW_comm (hw : Symm w) (A B : Finset V) : eW w A B = eW w B A := by
  unfold eW; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hw v u

theorem eW_empty_left (B : Finset V) : eW w ∅ B = 0 := by unfold eW; simp

theorem eW_empty_right (A : Finset V) : eW w A ∅ = 0 := by unfold eW; simp

/-- A positive weight between two sets gives a positive weight between some atoms. -/
theorem exists_pos_of_eW_pos {A B : Finset V} (h : 0 < eW w A B) : ∃ a ∈ A, ∃ b ∈ B, 0 < w a b := by
  unfold eW at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_lt_of_sum_lt (by simpa using h : ∑ a ∈ A, 0 < ∑ a ∈ A, ∑ b ∈ B, w a b)
  obtain ⟨b, hb, h2⟩ := Finset.exists_lt_of_sum_lt (by simpa using h1 : ∑ b ∈ B, 0 < ∑ b ∈ B, w a b)
  exact ⟨a, ha, b, hb, h2⟩

theorem le_eW_of_mem {A B : Finset V} {a b : V} (ha : a ∈ A) (hb : b ∈ B) : w a b ≤ eW w A B := by
  unfold eW
  exact (Finset.single_le_sum (f := fun b => w a b) (fun _ _ => Nat.zero_le _) hb).trans
    (Finset.single_le_sum (f := fun a => ∑ b ∈ B, w a b) (fun _ _ => Nat.zero_le _) ha)

end eWcalc

/-! ## The `𝒳`-layers -/

/-- The `𝒳`-chain as a function: `X 0 = {v₂} ⊂ ⋯ ⊂ X (t-1) = verts ∖ {v₁} ⊂ X t = verts = X i (i ≥ t)`, every
`𝒳`-side being one of `X 0, …, X (t-1)`. -/
structure XLayers (G : UMultigraph V) (v₁ v₂ : V) where
  t : ℕ
  X : ℕ → Finset V
  two_le : 2 ≤ t
  sub : ∀ i, X i ⊆ G.verts
  strict : ∀ i j, i < j → j ≤ t → X i ⊂ X j
  side : ∀ i, i < t → IsXSide G v₁ v₂ (X i)
  all : ∀ Z, IsXSide G v₁ v₂ Z → ∃ i, i < t ∧ X i = Z
  top : ∀ i, t ≤ i → X i = G.verts

namespace XLayers

variable {G : UMultigraph V} {v₁ v₂ : V} (L : XLayers G v₁ v₂)

theorem mono {i j : ℕ} (h : i ≤ j) : L.X i ⊆ L.X j := by
  rcases Nat.lt_or_ge j L.t with hj | hj
  · rcases h.lt_or_eq with h | rfl
    · exact (L.strict i j h hj.le).1
    · exact subset_rfl
  · rw [L.top j hj]; exact L.sub i

/-- The layers: `E 0 = X 0`, `E (i+1) = X (i+1) ∖ X i`. -/
def E : ℕ → Finset V
  | 0 => L.X 0
  | i + 1 => L.X (i + 1) \ L.X i

theorem E_sub (i : ℕ) : L.E i ⊆ G.verts := by
  cases i with
  | zero => exact L.sub 0
  | succ i => exact Finset.sdiff_subset.trans (L.sub _)

theorem E_subset_X {i j : ℕ} (h : i ≤ j) : L.E i ⊆ L.X j := by
  cases i with
  | zero => exact L.mono h
  | succ i => exact Finset.sdiff_subset.trans (L.mono h)

theorem E_disjoint_X {i j : ℕ} (h : j < i) : Disjoint (L.E i) (L.X j) := by
  cases i with
  | zero => omega
  | succ i =>
    rw [Finset.disjoint_left]
    intro x hx hxj
    exact (Finset.mem_sdiff.mp hx).2 (L.mono (Nat.lt_succ_iff.mp h) hxj)

theorem E_disjoint {i j : ℕ} (h : i ≠ j) : Disjoint (L.E i) (L.E j) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact ((L.E_disjoint_X h).mono_right (L.E_subset_X le_rfl)).symm
  · exact (L.E_disjoint_X h).mono_right (L.E_subset_X le_rfl)

theorem E_nonempty {i : ℕ} (hi : i ≤ L.t) : (L.E i).Nonempty := by
  cases i with
  | zero =>
    obtain ⟨-, h2, -, -⟩ := L.side 0 (by have := L.two_le; omega)
    exact ⟨v₂, h2⟩
  | succ i =>
    obtain ⟨x, hx⟩ := Finset.exists_of_ssubset (L.strict i (i + 1) (Nat.lt_succ_self i) hi)
    exact ⟨x, Finset.mem_sdiff.mpr hx⟩

theorem X_succ (i : ℕ) : L.X (i + 1) = L.X i ∪ L.E (i + 1) := by
  show L.X (i + 1) = L.X i ∪ (L.X (i + 1) \ L.X i)
  rw [Finset.union_sdiff_of_subset (L.mono (Nat.le_succ i))]

theorem compl_X (i : ℕ) : G.verts \ L.X i = L.E (i + 1) ∪ (G.verts \ L.X (i + 1)) := by
  ext x
  simp only [E, Finset.mem_sdiff, Finset.mem_union]
  have h1 : x ∈ L.X i → x ∈ L.X (i + 1) := fun h => L.mono (Nat.le_succ i) h
  have h2 : x ∈ L.X (i + 1) → x ∈ G.verts := fun h => L.sub (i + 1) h
  tauto

theorem compl_E (i : ℕ) : G.verts \ L.E (i + 1) = L.X i ∪ (G.verts \ L.X (i + 1)) := by
  ext x
  simp only [E, Finset.mem_sdiff, Finset.mem_union]
  have h0 : x ∈ L.X i → x ∈ L.X (i + 1) := fun h => L.mono (Nat.le_succ i) h
  have h1 : x ∈ L.X i → x ∈ G.verts := fun h => L.sub i h
  have h2 : x ∈ L.X (i + 1) → x ∈ G.verts := fun h => L.sub (i + 1) h
  tauto

theorem eW_X_succ_left (i : ℕ) (Z : Finset V) :
    eW (wG G) (L.X (i + 1)) Z = eW (wG G) (L.X i) Z + eW (wG G) (L.E (i + 1)) Z := by
  conv_lhs => rw [L.X_succ i]
  exact eW_union_left _ (L.E_disjoint_X (Nat.lt_succ_self i)).symm

theorem eW_compl_X_right (A : Finset V) (i : ℕ) :
    eW (wG G) A (G.verts \ L.X i) = eW (wG G) A (L.E (i + 1)) + eW (wG G) A (G.verts \ L.X (i + 1)) := by
  rw [L.compl_X i]
  exact eW_union_right _ (Finset.disjoint_left.mpr fun x h1 h2 =>
    (Finset.mem_sdiff.mp h2).2 (L.E_subset_X le_rfl h1))

theorem cut_E_succ (i : ℕ) : cut G (L.E (i + 1)) =
    eW (wG G) (L.X i) (L.E (i + 1)) + eW (wG G) (L.E (i + 1)) (G.verts \ L.X (i + 1)) := by
  rw [cut_eq_eW, L.compl_E i, eW_union_right _ (Finset.disjoint_left.mpr fun x h1 h2 =>
    (Finset.mem_sdiff.mp h2).2 (L.mono (Nat.le_succ i) h1)), eW_comm (symm_wG G) (L.E (i + 1)) (L.X i)]

theorem v₂_mem_X (i : ℕ) : v₂ ∈ L.X i := by
  rcases Nat.lt_or_ge i L.t with h | h
  · exact (L.side i h).2.1
  · rw [L.top i h]; exact (L.side 0 (by have := L.two_le; omega)).1 (L.side 0 (by have := L.two_le; omega)).2.1

theorem v₁_not_mem_X {i : ℕ} (hi : i < L.t) : v₁ ∉ L.X i := (L.side i hi).2.2.1

/-- An interior layer avoids both joints. -/
theorem E_joint_free {i : ℕ} (h0 : 0 < i) (hi : i < L.t) : v₁ ∉ L.E i ∧ v₂ ∉ L.E i := by
  obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  refine ⟨fun h => L.v₁_not_mem_X hi (L.E_subset_X le_rfl h), fun h => ?_⟩
  exact (Finset.mem_sdiff.mp h).2 (L.v₂_mem_X i)

/-- Every atom lies in some layer `≤ t`. -/
theorem exists_layer {x : V} (hx : x ∈ G.verts) : ∃ i, i ≤ L.t ∧ x ∈ L.E i := by
  classical
  have hP : ∃ i, x ∈ L.X i := ⟨L.t, by rw [L.top L.t le_rfl]; exact hx⟩
  set i := Nat.find hP with hi
  have hxi : x ∈ L.X i := Nat.find_spec hP
  refine ⟨i, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact Nat.find_min hP (show L.t < i from h) (by rw [L.top L.t le_rfl]; exact hx)
  · cases hc : i with
    | zero => rw [hc] at hxi; exact hxi
    | succ k =>
      rw [hc] at hxi
      exact Finset.mem_sdiff.mpr ⟨hxi, Nat.find_min hP (by omega)⟩

end XLayers

/-! ## Construction of the layers -/

section construct

variable {G : UMultigraph V} {v₁ v₂ : V}

/-- **The `𝒳`-chain exists** (for a T-vine context with nonempty interior). -/
theorem exists_xLayers (hT : T6Ctx G v₁ v₂) (hint : (Core.interior G v₁ v₂).Nonempty) :
    Nonempty (XLayers G v₁ v₂) := by
  classical
  set C := G.verts.powerset.filter fun X => IsXSide G v₁ v₂ X with hC
  have hmem : ∀ X, X ∈ C ↔ IsXSide G v₁ v₂ X := fun X => by
    rw [hC, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  obtain ⟨l, hl, hp⟩ := exists_chain_list C fun A hA B hB =>
    xside_chain hT ((hmem A).mp hA) ((hmem B).mp hB)
  have hlmem : ∀ X, X ∈ l ↔ IsXSide G v₁ v₂ X := fun X => by rw [← List.mem_toFinset, hl, hmem]
  -- {v₂} and verts ∖ {v₁} are 𝒳-sides
  have hsing : IsXSide G v₁ v₂ {v₂} := by
    refine ⟨Finset.singleton_subset_iff.mpr hT.mem₂, Finset.mem_singleton_self _,
      fun h => hT.ne (Finset.mem_singleton.mp h), ?_⟩
    rw [cut_singleton hT.cc hT.mem₂, hT.deg₂]
  have hcomp : IsXSide G v₁ v₂ (G.verts.erase v₁) := by
    refine ⟨Finset.erase_subset _ _, Finset.mem_erase.mpr ⟨hT.ne.symm, hT.mem₂⟩, Finset.notMem_erase _ _, ?_⟩
    have : G.verts.erase v₁ = G.verts \ {v₁} := by ext; simp [and_comm]
    rw [this, cut_compl (Finset.singleton_subset_iff.mpr hT.mem₁), cut_singleton hT.cc hT.mem₁, hT.deg₁]
  have hne : {v₂} ≠ G.verts.erase v₁ := by
    obtain ⟨x, hx⟩ := hint
    rw [mem_interior] at hx
    intro h
    have : x ∈ G.verts.erase v₁ := Finset.mem_erase.mpr ⟨hx.2.1, hx.1⟩
    rw [← h, Finset.mem_singleton] at this
    exact hx.2.2 this
  have hlen : 2 ≤ l.length := by
    have h1 := (hlmem _).mpr hsing
    have h2 := (hlmem _).mpr hcomp
    have hnd : l.Nodup := hp.imp (fun h => h.ne)
    have : ({{v₂}, G.verts.erase v₁} : Finset (Finset V)) ⊆ l.toFinset := by
      intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr ‹_›
    have := Finset.card_le_card this
    rw [Finset.card_pair hne, List.toFinset_card_of_nodup hnd] at this
    exact this
  have hget : ∀ i j (hi : i < l.length) (hj : j < l.length), i < j → l[i] ⊂ l[j] := by
    intro i j hi hj hij
    exact List.pairwise_iff_getElem.mp hp i j hi hj hij
  refine ⟨{
    t := l.length
    X := fun i => if h : i < l.length then l[i] else G.verts
    two_le := hlen
    sub := ?_
    strict := ?_
    side := ?_
    all := ?_
    top := ?_ }⟩
  · intro i
    by_cases h : i < l.length
    · simp only [h, dite_true]; exact ((hlmem _).mp (List.getElem_mem h)).1
    · simp only [h, dite_false]; exact subset_rfl
  · intro i j hij hj
    have hi : i < l.length := by omega
    by_cases hj' : j < l.length
    · simp only [hi, hj', dite_true]; exact hget i j hi hj' hij
    · simp only [hi, hj', dite_true, dite_false]
      refine Finset.ssubset_iff_subset_ne.mpr ⟨((hlmem _).mp (List.getElem_mem hi)).1, fun h => ?_⟩
      exact ((hlmem _).mp (List.getElem_mem hi)).2.2.1 (h ▸ hT.mem₁)
  · intro i hi
    simp only [hi, dite_true]; exact (hlmem _).mp (List.getElem_mem hi)
  · intro Z hZ
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem ((hlmem Z).mpr hZ)
    exact ⟨i, hi, by simp only [hi, dite_true]; exact he⟩
  · intro i hi
    simp only [show ¬ i < l.length by omega, dite_false]

end construct

/-! ## The pendant `H` -/

section pendant

variable {G : UMultigraph V} {v₁ v₂ : V}

/-- The pendant `H`: the union of all `𝒦`-sides. -/
noncomputable def Hp (G : UMultigraph V) (v₁ v₂ : V) : Finset V := by
  classical
  exact (G.verts.powerset.filter fun K => IsKSide G v₁ v₂ K).sup id

theorem subset_Hp {K : Finset V} (hK : IsKSide G v₁ v₂ K) : K ⊆ Hp G v₁ v₂ := by
  classical
  unfold Hp
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hK.1, hK⟩)

/-- `H` is empty or itself a `𝒦`-side (the largest one). -/
theorem Hp_cases (hT : T6Ctx G v₁ v₂) : Hp G v₁ v₂ = ∅ ∨ IsKSide G v₁ v₂ (Hp G v₁ v₂) := by
  classical
  set C := G.verts.powerset.filter fun K => IsKSide G v₁ v₂ K with hC
  rcases C.eq_empty_or_nonempty with h | h
  · left; unfold Hp; rw [← hC, h]; rfl
  · right
    obtain ⟨K, hK, hmax⟩ := Finset.exists_max_image C Finset.card h
    have hKs : IsKSide G v₁ v₂ K := (Finset.mem_filter.mp hK).2
    have hsup : Hp G v₁ v₂ = K := by
      apply Finset.Subset.antisymm _ (subset_Hp hKs)
      unfold Hp
      rw [← hC]
      refine Finset.sup_le fun K' hK' => ?_
      have hK's : IsKSide G v₁ v₂ K' := (Finset.mem_filter.mp hK').2
      rcases kside_chain hT hK's hKs with h | h
      · exact h
      · have := hmax K' hK'
        exact (Finset.eq_of_subset_of_card_le h this).symm ▸ subset_rfl
    rw [hsup]; exact hKs

theorem Hp_subset_verts : Hp G v₁ v₂ ⊆ G.verts := by
  classical
  unfold Hp
  exact Finset.sup_le fun K hK => (Finset.mem_filter.mp hK).2.1

theorem joint_not_mem_Hp (hT : T6Ctx G v₁ v₂) : v₁ ∉ Hp G v₁ v₂ ∧ v₂ ∉ Hp G v₁ v₂ := by
  rcases Hp_cases hT with h | h
  · rw [h]; simp
  · exact ⟨h.2.1, h.2.2.1⟩

/-- `H` lies inside or outside every `𝒳`-side. -/
theorem Hp_xside (hT : T6Ctx G v₁ v₂) {X : Finset V} (hX : IsXSide G v₁ v₂ X) :
    Hp G v₁ v₂ ⊆ X ∨ Disjoint (Hp G v₁ v₂) X := by
  rcases Hp_cases hT with h | h
  · rw [h]; exact Or.inl (Finset.empty_subset _)
  · exact kside_xside hT h hX

end pendant

/-! ## The long-bond lemma -/

namespace XLayers

variable {G : UMultigraph V} {v₁ v₂ : V} (L : XLayers G v₁ v₂)

theorem cut_X (i : ℕ) (hi : i < L.t) : eW (wG G) (L.X i) (G.verts \ L.X i) = 2 := (L.side i hi).2.2.2

/-- A layer with cut at most 2 strictly between the ends is the pendant. -/
theorem E_eq_Hp_of_cut (hT : T6Ctx G v₁ v₂) {m : ℕ} (h0 : 0 < m) (hm : m < L.t)
    (hc : cut G (L.E m) ≤ 2) : L.E m = Hp G v₁ v₂ := by
  obtain ⟨hj₁, hj₂⟩ := L.E_joint_free h0 hm
  have hne := L.E_nonempty hm.le
  have h2 : cut G (L.E m) = 2 := by
    obtain ⟨x, hx⟩ := hne
    have := two_le_cut hT.cc (L.E_sub m) hx hT.mem₁ hj₁
    omega
  have hK : IsKSide G v₁ v₂ (L.E m) := ⟨L.E_sub m, hj₁, hj₂, hne, h2⟩
  have hsub := subset_Hp hK
  apply Finset.Subset.antisymm hsub
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨x, hx⟩ := hne
  have hHm : Hp G v₁ v₂ ⊆ L.X (m + 1) := by
    rcases Hp_xside hT (L.side (m + 1) hm) with h | h
    · exact h
    · exact absurd (L.E_subset_X le_rfl hx) (Finset.disjoint_left.mp h (hsub hx))
  have hHm' : Disjoint (Hp G v₁ v₂) (L.X m) := by
    rcases Hp_xside hT (L.side m (by omega)) with h | h
    · exact absurd (h (hsub hx)) (Finset.mem_sdiff.mp hx).2
    · exact h
  intro y hy
  exact Finset.mem_sdiff.mpr ⟨hHm hy, Finset.disjoint_left.mp hHm' hy⟩

/-- **The skip lemma.** If some bond jumps over the layer `k + 1` (from `X k` to beyond `X (k+1)`), that layer is
the pendant `H`, and the three weights around it are `1`. -/
theorem skip (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 < L.t)
    (hpos : 0 < eW (wG G) (L.X k) (G.verts \ L.X (k + 1))) :
    L.E (k + 1) = Hp G v₁ v₂ ∧ eW (wG G) (L.X k) (G.verts \ L.X (k + 1)) = 1 ∧
      eW (wG G) (L.X k) (L.E (k + 1)) = 1 ∧ eW (wG G) (L.E (k + 1)) (G.verts \ L.X (k + 1)) = 1 := by
  have hca := L.cut_X k (by omega)
  rw [L.eW_compl_X_right] at hca
  have hca1 := L.cut_X (k + 1) hk
  rw [L.eW_X_succ_left] at hca1
  have hcE := L.cut_E_succ k
  have hcut : cut G (L.E (k + 1)) ≤ 2 := by omega
  have hH := L.E_eq_Hp_of_cut hT (by omega) hk hcut
  have h2 : cut G (L.E (k + 1)) = 2 := by
    obtain ⟨x, hx⟩ := L.E_nonempty hk.le
    have := two_le_cut hT.cc (L.E_sub _) hx hT.mem₁ (L.E_joint_free (by omega) hk).1
    omega
  refine ⟨hH, ?_, ?_, ?_⟩ <;> omega

/-- The weight from `X k` beyond `X (k+1)` dominates the weight between a layer `≤ k` and a layer `≥ k + 2`. -/
theorem le_skip {a b k : ℕ} (ha : a ≤ k) (hb : k + 2 ≤ b) :
    eW (wG G) (L.E a) (L.E b) ≤ eW (wG G) (L.X k) (G.verts \ L.X (k + 1)) := by
  refine (eW_mono_left _ (L.E_subset_X ha)).trans (eW_mono_right _ ?_)
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨L.E_sub b hx, Finset.disjoint_left.mp (L.E_disjoint_X (by omega)) hx⟩

/-- Two distinct layers cannot both be the pendant. -/
theorem not_two_Hp {i j : ℕ} (hij : i ≠ j) (hi : i ≤ L.t) (hEi : L.E i = Hp G v₁ v₂)
    (hEj : L.E j = Hp G v₁ v₂) : False := by
  have hd := L.E_disjoint hij
  rw [hEi, hEj] at hd
  obtain ⟨x, hx⟩ := L.E_nonempty hi
  rw [hEi] at hx
  exact Finset.disjoint_left.mp hd hx hx

/-- **The long-bond lemma.** A bond between layers `a` and `b ≥ a + 2` (`b ≤ t`) forces `b = a + 2` and the layer
`a + 1` to be the pendant `H`. -/
theorem long_bond (hT : T6Ctx G v₁ v₂) {a b : ℕ} (hab : a + 2 ≤ b) (hb : b ≤ L.t)
    (hpos : 0 < eW (wG G) (L.E a) (L.E b)) : b = a + 2 ∧ L.E (a + 1) = Hp G v₁ v₂ := by
  have h1 := (L.skip hT (by omega) (lt_of_lt_of_le hpos (L.le_skip le_rfl hab))).1
  refine ⟨?_, h1⟩
  by_contra hne
  have h2 := (L.skip hT (k := a + 1) (by omega)
    (lt_of_lt_of_le hpos (L.le_skip (Nat.le_succ a) (by omega)))).1
  exact L.not_two_Hp (show a + 1 ≠ a + 1 + 1 by omega) (by omega) h1 h2

/-- Bonds between layers at distance `≥ 3` do not exist. -/
theorem eW_far (hT : T6Ctx G v₁ v₂) {a b : ℕ} (hab : a + 3 ≤ b) (hb : b ≤ L.t) :
    eW (wG G) (L.E a) (L.E b) = 0 := by
  by_contra hpos
  have := (L.long_bond hT (by omega) hb (Nat.pos_of_ne_zero hpos)).1
  omega

end XLayers

end WaveTurbulence.TVine.Struct
