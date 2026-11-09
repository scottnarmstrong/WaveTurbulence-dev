/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Thm6Layer
import Mathlib.Tactic

/-!
# N3 Theorem 6, part 3: the spine (packet L3)

For a T6 context with its `𝒳`-layers `L` and pendant `H = Hp`:

* the end layers are the joints (`E_zero`, `E_top`); layer membership `mem_X_iff_of_mem_E`;
* `Hp_loc`: a nonempty pendant lies in exactly one interior layer `E i`;
* `Hp_pa`: if `H ⊊ E i` (P-a), all bonds of `H` go into `E i ∖ H`;
* `eW_consec`: consecutive layers, neither the pendant, are joined by 2 bonds;
* `pb_counts`: if `E i = H` (P-b), the three bonds of the triangle are single;
* `spine_piece`: `E i ∖ H` (nonempty, `0 < i < t`) is a piece;
* `separates`, `conn_before`, `conn_after`: spine separation and order (N3 Thm 6 (ii), (U1)(a)).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

variable {V : Type*} [DecidableEq V]

namespace XLayers

variable {G : UMultigraph V} {v₁ v₂ : V} (L : XLayers G v₁ v₂)

/-! ## The end layers -/

theorem X_zero (hT : T6Ctx G v₁ v₂) : L.X 0 = {v₂} := by
  have hs : IsXSide G v₁ v₂ {v₂} := by
    refine ⟨Finset.singleton_subset_iff.mpr hT.mem₂, Finset.mem_singleton_self _,
      fun h => hT.ne (Finset.mem_singleton.mp h), ?_⟩
    rw [cut_singleton hT.cc hT.mem₂, hT.deg₂]
  obtain ⟨j, hj, he⟩ := L.all _ hs
  apply Finset.Subset.antisymm
  · rw [← he]; exact L.mono (Nat.zero_le j)
  · exact Finset.singleton_subset_iff.mpr (L.v₂_mem_X 0)

theorem X_last (hT : T6Ctx G v₁ v₂) : L.X (L.t - 1) = G.verts.erase v₁ := by
  have hs : IsXSide G v₁ v₂ (G.verts.erase v₁) := by
    refine ⟨Finset.erase_subset _ _, Finset.mem_erase.mpr ⟨hT.ne.symm, hT.mem₂⟩, Finset.notMem_erase _ _, ?_⟩
    have : G.verts.erase v₁ = G.verts \ {v₁} := by ext; simp [and_comm]
    rw [this, cut_compl (Finset.singleton_subset_iff.mpr hT.mem₁), cut_singleton hT.cc hT.mem₁, hT.deg₁]
  obtain ⟨j, hj, he⟩ := L.all _ hs
  have ht := L.two_le
  apply Finset.Subset.antisymm
  · intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => L.v₁_not_mem_X (by omega) (h ▸ hx), L.sub _ hx⟩
  · rw [← he]; exact L.mono (by omega)

theorem E_zero (hT : T6Ctx G v₁ v₂) : L.E 0 = {v₂} := L.X_zero hT

theorem E_top (hT : T6Ctx G v₁ v₂) : L.E L.t = {v₁} := by
  have ht := L.two_le
  obtain ⟨k, hk⟩ : ∃ k, L.t = k + 1 := ⟨L.t - 1, by omega⟩
  rw [hk]
  show L.X (k + 1) \ L.X k = {v₁}
  rw [L.top (k + 1) (by omega), show k = L.t - 1 by omega, L.X_last hT]
  ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, h⟩; by_contra hne; exact h ⟨hne, hx⟩
  · rintro rfl; exact ⟨hT.mem₁, fun h => h.1 rfl⟩

/-- Membership of a layer element in the `X`'s. -/
theorem mem_X_iff_of_mem_E {i j : ℕ} {x : V} (hx : x ∈ L.E i) : x ∈ L.X j ↔ i ≤ j := by
  constructor
  · intro h; by_contra hlt; push Not at hlt
    exact Finset.disjoint_left.mp (L.E_disjoint_X hlt) hx h
  · intro h; exact L.E_subset_X h hx

/-- Two atoms of different layers are separated by an `𝒳`-side. -/
theorem layer_unique {i j : ℕ} {x : V} (hi : x ∈ L.E i) (hj : x ∈ L.E j) : i = j := by
  by_contra h
  exact Finset.disjoint_left.mp (L.E_disjoint h) hi hj

/-- No `𝒳`-side lies strictly between two consecutive `X`'s. -/
theorem no_between {Z : Finset V} (hZ : IsXSide G v₁ v₂ Z) {j : ℕ} (h1 : L.X j ⊆ Z) (h2 : Z ⊆ L.X (j + 1))
    (hj : j + 1 ≤ L.t) : Z = L.X j ∨ Z = L.X (j + 1) := by
  obtain ⟨m, hm, rfl⟩ := L.all Z hZ
  rcases Nat.lt_trichotomy m j with h | rfl | h
  · exfalso
    have := (L.strict m j h (by omega)).2
    exact this h1
  · exact Or.inl rfl
  · rcases Nat.lt_or_ge (j + 1) m with h' | h'
    · exfalso; exact (L.strict (j + 1) m h' hm.le).2 h2
    · right; congr 1; omega

/-! ## The location of the pendant -/

/-- A nonempty pendant lies in exactly one interior layer. -/
theorem Hp_loc (hT : T6Ctx G v₁ v₂) (hH : (Hp G v₁ v₂).Nonempty) :
    ∃ i, 0 < i ∧ i < L.t ∧ Hp G v₁ v₂ ⊆ L.E i := by
  classical
  have hP : ∃ i, Hp G v₁ v₂ ⊆ L.X i := ⟨L.t, by rw [L.top L.t le_rfl]; exact Hp_subset_verts⟩
  set i := Nat.find hP with hidef
  have hsub : Hp G v₁ v₂ ⊆ L.X i := Nat.find_spec hP
  obtain ⟨y, hy⟩ := hH
  have hj := joint_not_mem_Hp hT
  have hi0 : 0 < i := by
    by_contra h
    have hi : i = 0 := by omega
    have := hsub hy
    rw [hi, L.X_zero hT, Finset.mem_singleton] at this
    exact hj.2 (this ▸ hy)
  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hnot : ¬ Hp G v₁ v₂ ⊆ L.X k := Nat.find_min hP (by omega)
  have ht := L.two_le
  have hkt : k < L.t := by
    by_contra h; push Not at h
    exact hnot (by rw [L.top k h]; exact Hp_subset_verts)
  have hdisj : Disjoint (Hp G v₁ v₂) (L.X k) := (Hp_xside hT (L.side k hkt)).resolve_left hnot
  have hsubE : Hp G v₁ v₂ ⊆ L.E (k + 1) := fun x hx =>
    Finset.mem_sdiff.mpr ⟨hk ▸ hsub hx, Finset.disjoint_left.mp hdisj hx⟩
  refine ⟨k + 1, by omega, ?_, hsubE⟩
  by_contra h; push Not at h
  have hkt' : k + 1 = L.t := by
    rcases h.lt_or_eq with h | h
    · exfalso
      have := hsubE hy
      have hE : L.E (k + 1) = ∅ := by
        show L.X (k + 1) \ L.X k = ∅
        rw [L.top (k + 1) (by omega), L.top k (by omega), Finset.sdiff_self]
      rw [hE] at this; exact absurd this (Finset.notMem_empty _)
    · exact h.symm
  have := hsubE hy
  rw [hkt', L.E_top hT, Finset.mem_singleton] at this
  exact hj.1 (this ▸ hy)

/-- **P-a** (for any `𝒦`-side `K`): if `K` is a proper part of the layer `k + 1`, all bonds of `K` go into the rest of
that layer. -/
theorem pa_aux (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 < L.t) {K : Finset V} (hKs : IsKSide G v₁ v₂ K)
    (hsub : K ⊆ L.E (k + 1)) (hne : L.E (k + 1) ≠ K) :
    eW (wG G) K (L.X k) = 0 ∧ eW (wG G) K (G.verts \ L.X (k + 1)) = 0 ∧
      eW (wG G) K (L.E (k + 1) \ K) = 2 := by
  have hw := symm_wG G
  have hHV : K ⊆ G.verts := hKs.1
  have hcH : cut G K = 2 := hKs.2.2.2.2
  have hdk : Disjoint K (L.X k) := Finset.disjoint_left.mpr fun x hx hxk =>
    (Finset.mem_sdiff.mp (hsub hx)).2 hxk
  have hKX1 : K ⊆ L.X (k + 1) := hsub.trans (L.E_subset_X le_rfl)
  obtain ⟨g, hg⟩ : (L.E (k + 1) \ K).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact fun h => hne (Finset.Subset.antisymm h hsub)
  obtain ⟨hgE, hgH⟩ := Finset.mem_sdiff.mp hg
  have hgX1 : g ∈ L.X (k + 1) := L.E_subset_X le_rfl hgE
  have hgXk : g ∉ L.X k := (Finset.mem_sdiff.mp hgE).2
  obtain ⟨y, hy⟩ := hKs.2.2.2.1
  -- the complement of `K` splits into three parts
  have hsplitset : G.verts \ K = L.X k ∪ ((L.E (k + 1) \ K) ∪ (G.verts \ L.X (k + 1))) := by
    ext x
    have h0 : x ∈ L.X k → x ∈ L.X (k + 1) := fun h => L.mono (Nat.le_succ k) h
    have h1 : x ∈ L.X (k + 1) → x ∈ G.verts := fun h => L.sub (k + 1) h
    have h2 : x ∈ L.X k → x ∉ K := fun h hH => Finset.disjoint_left.mp hdk hH h
    have h3 : x ∈ L.E (k + 1) ↔ x ∈ L.X (k + 1) ∧ x ∉ L.X k := Finset.mem_sdiff
    simp only [Finset.mem_sdiff, Finset.mem_union, h3]
    tauto
  have hd1 : Disjoint (L.E (k + 1) \ K) (G.verts \ L.X (k + 1)) :=
    Finset.disjoint_left.mpr fun x h1 h2 => (Finset.mem_sdiff.mp h2).2
      (L.E_subset_X le_rfl (Finset.mem_sdiff.mp h1).1)
  have hd2 : Disjoint (L.X k) ((L.E (k + 1) \ K) ∪ (G.verts \ L.X (k + 1))) := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    rcases Finset.mem_union.mp h2 with h2 | h2
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2 h1
    · exact (Finset.mem_sdiff.mp h2).2 (L.mono (Nat.le_succ k) h1)
  have hcutH : cut G K = eW (wG G) K (L.X k) + (eW (wG G) K (L.E (k + 1) \ K) +
      eW (wG G) K (G.verts \ L.X (k + 1))) := by
    rw [cut_eq_eW, hsplitset, eW_union_right _ hd2, eW_union_right _ hd1]
  have hXk := L.side k (by omega)
  have hXk1 := L.side (k + 1) hk
  have hA : eW (wG G) K (L.X k) = 0 := by
    by_contra hpos
    have hZ := cut_union_disjoint (G := G) (L.sub k) hHV hdk.symm
    rw [eW_comm hw (L.X k) K, hXk.2.2.2, hcH] at hZ
    have hZV : L.X k ∪ K ⊆ G.verts := Finset.union_subset (L.sub k) hHV
    have hv1 : v₁ ∉ L.X k ∪ K := fun h => (Finset.mem_union.mp h).elim hXk.2.2.1 hKs.2.1
    rcases (show eW (wG G) K (L.X k) = 1 ∨ eW (wG G) K (L.X k) = 2 by omega) with h1 | h1
    · have hside : IsXSide G v₁ v₂ (L.X k ∪ K) :=
        ⟨hZV, Finset.mem_union_left _ hXk.2.1, hv1, by omega⟩
      rcases L.no_between hside Finset.subset_union_left
        (Finset.union_subset (L.mono (Nat.le_succ k)) hKX1) hk.le with h | h
      · have hyK : y ∈ L.X k ∪ K := Finset.mem_union_right _ hy
        rw [h] at hyK
        exact Finset.disjoint_left.mp hdk hy hyK
      · have hgK : g ∈ L.X k ∪ K := by rw [h]; exact hgX1
        rcases Finset.mem_union.mp hgK with h' | h'
        · exact hgXk h'
        · exact hgH h'
    · have h0 : cut G (L.X k ∪ K) = 0 := by omega
      have := two_le_cut hT.cc hZV (Finset.mem_union_left _ hXk.2.1) hT.mem₁ hv1
      omega
  have hinner : eW (wG G) (L.X (k + 1) \ K) K = eW (wG G) K (L.E (k + 1) \ K) := by
    rw [eW_comm hw]
    have hset : L.X (k + 1) \ K = L.X k ∪ (L.E (k + 1) \ K) := by
      ext x
      have h0 : x ∈ L.X k → x ∈ L.X (k + 1) := fun h => L.mono (Nat.le_succ k) h
      have h2 : x ∈ L.X k → x ∉ K := fun h hH => Finset.disjoint_left.mp hdk hH h
      have h3 : x ∈ L.E (k + 1) ↔ x ∈ L.X (k + 1) ∧ x ∉ L.X k := Finset.mem_sdiff
      simp only [Finset.mem_sdiff, Finset.mem_union, h3]
      tauto
    rw [hset, eW_union_right _ ?_, hA, zero_add]
    exact Finset.disjoint_left.mpr fun x h1 h2 => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2 h1
  have hB : eW (wG G) K (G.verts \ L.X (k + 1)) = 0 := by
    by_contra hpos
    have hsplit := cut_union_disjoint (G := G) (X := L.X (k + 1) \ K) (Y := K)
      (Finset.sdiff_subset.trans (L.sub _)) hHV Finset.sdiff_disjoint
    rw [Finset.sdiff_union_of_subset hKX1, hXk1.2.2.2, hcH, hinner] at hsplit
    have hZV : L.X (k + 1) \ K ⊆ G.verts := Finset.sdiff_subset.trans (L.sub _)
    have hv2 : v₂ ∈ L.X (k + 1) \ K := Finset.mem_sdiff.mpr ⟨hXk1.2.1, hKs.2.2.1⟩
    have hv1 : v₁ ∉ L.X (k + 1) \ K := fun h => hXk1.2.2.1 (Finset.mem_sdiff.mp h).1
    rcases (show eW (wG G) K (G.verts \ L.X (k + 1)) = 1 ∨ eW (wG G) K (G.verts \ L.X (k + 1)) = 2 by omega)
      with h1 | h1
    · have hside : IsXSide G v₁ v₂ (L.X (k + 1) \ K) := ⟨hZV, hv2, hv1, by omega⟩
      rcases L.no_between hside (fun x hx => Finset.mem_sdiff.mpr ⟨L.mono (Nat.le_succ k) hx,
          fun hH => Finset.disjoint_left.mp hdk hH hx⟩) Finset.sdiff_subset hk.le with h | h
      · have hg' : g ∈ L.X (k + 1) \ K := Finset.mem_sdiff.mpr ⟨hgX1, hgH⟩
        rw [h] at hg'
        exact hgXk hg'
      · have hy' : y ∈ L.X (k + 1) := hKX1 hy
        rw [← h] at hy'
        exact (Finset.mem_sdiff.mp hy').2 hy
    · have h0 : cut G (L.X (k + 1) \ K) = 0 := by omega
      have := two_le_cut hT.cc hZV hv2 hT.mem₁ (fun h => hv1 h)
      omega
  refine ⟨hA, hB, ?_⟩
  omega

/-- **P-a** for the pendant. -/
theorem Hp_pa (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 < L.t) (hsub : Hp G v₁ v₂ ⊆ L.E (k + 1))
    (hne : L.E (k + 1) ≠ Hp G v₁ v₂) (hH : (Hp G v₁ v₂).Nonempty) :
    eW (wG G) (Hp G v₁ v₂) (L.X k) = 0 ∧ eW (wG G) (Hp G v₁ v₂) (G.verts \ L.X (k + 1)) = 0 ∧
      eW (wG G) (Hp G v₁ v₂) (L.E (k + 1) \ Hp G v₁ v₂) = 2 :=
  L.pa_aux hT hk ((Hp_cases hT).resolve_left (Finset.nonempty_iff_ne_empty.mp hH)) hsub hne

/-! ## Bond counts between layers -/

/-- The skip weight is zero over a layer that is not the pendant. -/
theorem skip_zero (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 ≤ L.t) (hne : L.E (k + 1) ≠ Hp G v₁ v₂) :
    eW (wG G) (L.X k) (G.verts \ L.X (k + 1)) = 0 := by
  rcases hk.lt_or_eq with hk | hk
  · by_contra hpos
    exact hne (L.skip hT hk (Nat.pos_of_ne_zero hpos)).1
  · rw [hk, L.top L.t le_rfl, Finset.sdiff_self, eW_empty_right]

/-- **Consecutive layers** that are not the pendant are joined by exactly 2 bonds. -/
theorem eW_consec (hT : T6Ctx G v₁ v₂) {a : ℕ} (ha : a + 1 ≤ L.t) (hne1 : L.E (a + 1) ≠ Hp G v₁ v₂)
    (hne0 : L.E a ≠ Hp G v₁ v₂) : eW (wG G) (L.E a) (L.E (a + 1)) = 2 := by
  have hca := L.cut_X a (by omega)
  rw [L.eW_compl_X_right, L.skip_zero hT ha hne1, add_zero] at hca
  cases a with
  | zero => rwa [show L.E 0 = L.X 0 from rfl]
  | succ k =>
    rw [L.eW_X_succ_left] at hca
    have h0 : eW (wG G) (L.X k) (L.E (k + 1 + 1)) = 0 := by
      have := L.skip_zero hT (by omega) hne0
      have hle : eW (wG G) (L.X k) (L.E (k + 1 + 1)) ≤ eW (wG G) (L.X k) (G.verts \ L.X (k + 1)) := by
        refine eW_mono_right _ fun x hx => Finset.mem_sdiff.mpr ⟨L.E_sub _ hx, ?_⟩
        exact Finset.disjoint_left.mp (L.E_disjoint_X (by omega)) hx
      omega
    omega

/-- **P-b counts**: if the layer `k + 1` is the pendant, the triangle's three bonds are single. -/
theorem pb_counts (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 < L.t) (hE : L.E (k + 1) = Hp G v₁ v₂) :
    eW (wG G) (L.E k) (L.E (k + 2)) = 1 ∧ eW (wG G) (L.E k) (L.E (k + 1)) = 1 ∧
      eW (wG G) (L.E (k + 1)) (L.E (k + 2)) = 1 := by
  have hne2 : L.E (k + 2) ≠ Hp G v₁ v₂ := fun h => L.not_two_Hp (show k + 1 ≠ k + 2 by omega) hk.le hE h
  have hz2 := L.skip_zero hT (k := k + 1) (by omega) hne2
  have hne0 : ∀ j, j ≠ k + 1 → j ≤ L.t → L.E j ≠ Hp G v₁ v₂ := fun j hj hjt h =>
    L.not_two_Hp hj hjt h hE
  have h2 : cut G (L.E (k + 1)) = 2 := by
    have hKs := (Hp_cases hT).resolve_left (by
      rw [← hE]; exact Finset.nonempty_iff_ne_empty.mp (L.E_nonempty hk.le))
    rw [hE]; exact hKs.2.2.2.2
  have hcE := L.cut_E_succ k
  have hca := L.cut_X k (by omega)
  have hca1 := L.cut_X (k + 1) hk
  rw [L.eW_X_succ_left] at hca1
  rw [L.eW_compl_X_right (L.X k) k] at hca
  -- A + B = 2, A + C = 2, B + C = 2 with A = eW (X k) (E (k+1)), B = skip weight, C = forward weight of E (k+1)
  have hBC : eW (wG G) (L.X k) (G.verts \ L.X (k + 1)) + eW (wG G) (L.E (k + 1)) (G.verts \ L.X (k + 1)) = 2 :=
    hca1
  -- the far parts vanish
  have hfarX : eW (wG G) (L.X k) (G.verts \ L.X (k + 1 + 1)) = 0 :=
    Nat.eq_zero_of_le_zero ((eW_mono_left _ (L.mono (Nat.le_succ k))).trans hz2.le)
  have hfarE : eW (wG G) (L.E (k + 1)) (G.verts \ L.X (k + 1 + 1)) = 0 :=
    Nat.eq_zero_of_le_zero ((eW_mono_left _ (L.E_subset_X le_rfl)).trans hz2.le)
  have hB : eW (wG G) (L.X k) (G.verts \ L.X (k + 1)) = eW (wG G) (L.X k) (L.E (k + 2)) := by
    rw [L.eW_compl_X_right (L.X k) (k + 1), hfarX, add_zero]
  have hC : eW (wG G) (L.E (k + 1)) (G.verts \ L.X (k + 1)) = eW (wG G) (L.E (k + 1)) (L.E (k + 2)) := by
    rw [L.eW_compl_X_right (L.E (k + 1)) (k + 1), hfarE, add_zero]
  -- reduce `X k` to `E k`
  have hred : ∀ Z : Finset V, Z ⊆ G.verts \ L.X (k + 1) ∨ Z = L.E (k + 1) →
      eW (wG G) (L.X k) Z = eW (wG G) (L.E k) Z := by
    intro Z hZ
    cases k with
    | zero => rfl
    | succ j =>
      rw [L.eW_X_succ_left]
      have hz := L.skip_zero hT (k := j) (by omega) (hne0 (j + 1) (by omega) (by omega))
      have hle : eW (wG G) (L.X j) Z ≤ eW (wG G) (L.X j) (G.verts \ L.X (j + 1)) := by
        refine eW_mono_right _ fun x hx => Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · rcases hZ with hZ | rfl
          · exact (Finset.mem_sdiff.mp (hZ hx)).1
          · exact L.E_sub _ hx
        · rcases hZ with hZ | rfl
          · exact fun h => (Finset.mem_sdiff.mp (hZ hx)).2 (L.mono (by omega) h)
          · exact Finset.disjoint_left.mp (L.E_disjoint_X (by omega)) hx
      omega
  have hE2sub : L.E (k + 2) ⊆ G.verts \ L.X (k + 1) := fun x hx =>
    Finset.mem_sdiff.mpr ⟨L.E_sub _ hx, Finset.disjoint_left.mp (L.E_disjoint_X (by omega)) hx⟩
  have hA' := hred (L.E (k + 1)) (Or.inr rfl)
  have hB' := hred (L.E (k + 2)) (Or.inl hE2sub)
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## Spine pieces, separation and order -/

/-- **A spine layer minus the pendant is a piece.** -/
theorem spine_piece (hT : T6Ctx G v₁ v₂) {i : ℕ} (h0 : 0 < i) (hi : i < L.t)
    (hne : (L.E i \ Hp G v₁ v₂).Nonempty) : L.E i \ Hp G v₁ v₂ ∈ piecesU G v₁ v₂ := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨huE, huH⟩ := Finset.mem_sdiff.mp hu
  have hj := L.E_joint_free h0 hi
  have hsubI : L.E i \ Hp G v₁ v₂ ⊆ Core.interior G v₁ v₂ := fun x hx =>
    mem_interior.mpr ⟨L.E_sub i (Finset.mem_sdiff.mp hx).1,
      fun h => hj.1 (h ▸ (Finset.mem_sdiff.mp hx).1), fun h => hj.2 (h ▸ (Finset.mem_sdiff.mp hx).1)⟩
  refine mem_piecesU_of_class hsubI hu (fun w hw => ?_) (fun w hw hwP => ?_)
  · obtain ⟨hwE, hwH⟩ := Finset.mem_sdiff.mp hw
    rw [samePieceU_iff_sides hT (L.E_sub i huE) (L.E_sub i hwE)]
    refine ⟨fun X hX => ?_, fun K hK => ?_⟩
    · obtain ⟨j, -, rfl⟩ := L.all X hX
      rw [L.mem_X_iff_of_mem_E huE, L.mem_X_iff_of_mem_E hwE]
    · exact ⟨fun h => absurd (subset_Hp hK h) huH, fun h => absurd (subset_Hp hK h) hwH⟩
  · rw [samePieceU_iff_sides hT (L.E_sub i huE) (interior_subset_verts _ _ hw)]
    rintro ⟨hx, hk⟩
    by_cases hwH : w ∈ Hp G v₁ v₂
    · have hKs := (Hp_cases hT).resolve_left (Finset.ne_empty_of_mem hwH)
      exact huH ((hk _ hKs).mpr hwH)
    · obtain ⟨j, hjt, hwj⟩ := L.exists_layer (interior_subset_verts _ _ hw)
      have hij : i ≠ j := fun h => hwP (Finset.mem_sdiff.mpr ⟨h ▸ hwj, hwH⟩)
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · have := hx (L.X i) (L.side i hi)
        rw [L.mem_X_iff_of_mem_E huE, L.mem_X_iff_of_mem_E hwj] at this
        exact absurd (this.mp le_rfl) (by omega)
      · have := hx (L.X j) (L.side j (by omega))
        rw [L.mem_X_iff_of_mem_E huE, L.mem_X_iff_of_mem_E hwj] at this
        exact absurd (this.mpr le_rfl) (by omega)

/-- Reachability inside `A` stays inside any `B ⊆ A` with no bond from `B` to `A ∖ B`. -/
theorem reach_stays {A B : Finset V} (hBA : B ⊆ A) (hno : eW (wG G) B (A \ B) = 0) {x y : V} (hx : x ∈ B)
    (h : Relation.ReflTransGen (AdjIn G A) x y) : y ∈ B := by
  induction h with
  | refl => exact hx
  | @tail b c _ hbc ih =>
    by_contra hc
    have hpos : 0 < eW (wG G) B (A \ B) :=
      lt_of_lt_of_le (show 0 < wG G b c from Nat.pos_of_ne_zero hbc.2.2)
        (le_eW_of_mem (w := wG G) ih (Finset.mem_sdiff.mpr ⟨hbc.2.1, hc⟩))
    omega

/-- **A spine piece separates the joints**: in `verts ∖ (E k+1 ∖ H)`, the atoms reachable from `v₂` stay in `X k`. -/
theorem separates (hT : T6Ctx G v₁ v₂) {k : ℕ} (hk : k + 1 < L.t) (hne : L.E (k + 1) ≠ Hp G v₁ v₂) :
    ¬ Relation.ReflTransGen (AdjIn G (G.verts \ (L.E (k + 1) \ Hp G v₁ v₂))) v₂ v₁ := by
  intro h
  set A := G.verts \ (L.E (k + 1) \ Hp G v₁ v₂)
  have hBA : L.X k ⊆ A := fun x hx => Finset.mem_sdiff.mpr ⟨L.sub k hx,
    fun h' => Finset.disjoint_left.mp (L.E_disjoint_X (Nat.lt_succ_self k)) (Finset.mem_sdiff.mp h').1 hx⟩
  have hno : eW (wG G) (L.X k) (A \ L.X k) = 0 := by
    have hsub : A \ L.X k ⊆ (L.E (k + 1) ∩ Hp G v₁ v₂) ∪ (G.verts \ L.X (k + 1)) := by
      intro x hx
      simp only [A, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, E] at hx ⊢
      tauto
    refine Nat.eq_zero_of_le_zero ((eW_mono_right _ hsub).trans ?_)
    rw [eW_union_right _ ?_]
    · have h1 := L.skip_zero hT hk.le hne
      have h2 : eW (wG G) (L.X k) (L.E (k + 1) ∩ Hp G v₁ v₂) = 0 := by
        by_cases hH : (Hp G v₁ v₂).Nonempty
        · obtain ⟨i, hi0, hit, hiE⟩ := L.Hp_loc hT hH
          by_cases hik : i = k + 1
          · subst hik
            have := (L.Hp_pa hT hk hiE hne hH).1
            rw [eW_comm (symm_wG G)] at this
            exact Nat.eq_zero_of_le_zero ((eW_mono_right _ Finset.inter_subset_right).trans this.le)
          · have : L.E (k + 1) ∩ Hp G v₁ v₂ = ∅ := by
              ext x; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
              intro hx hxH
              exact Finset.disjoint_left.mp (L.E_disjoint (Ne.symm hik)) hx (hiE hxH)
            rw [this, eW_empty_right]
        · rw [Finset.not_nonempty_iff_eq_empty.mp hH, Finset.inter_empty, eW_empty_right]
      omega
    · exact Finset.disjoint_left.mpr fun x h1 h2 => (Finset.mem_sdiff.mp h2).2
        (L.E_subset_X le_rfl (Finset.mem_inter.mp h1).1)
  have := reach_stays hBA hno (L.v₂_mem_X k) h
  exact L.v₁_not_mem_X (by omega) this

/-- **Order, before**: an atom of a layer `j ≤ k` is joined to `v₂` inside `X k`. -/
theorem conn_before (hT : T6Ctx G v₁ v₂) {k j : ℕ} (hk : k < L.t) (hj : j ≤ k) {q : V} (hq : q ∈ L.E j) :
    Relation.ReflTransGen (AdjIn G (L.X k)) q v₂ :=
  connOn_of_cut_two hT.cc (L.sub k) (L.side k hk).2.2.2 q (L.E_subset_X hj hq) v₂ (L.v₂_mem_X k)

/-- **Order, after**: an atom of a layer `j > k` is joined to `v₁` outside `X k`. -/
theorem conn_after (hT : T6Ctx G v₁ v₂) {k j : ℕ} (hk : k < L.t) (hj : k < j) {q : V} (hq : q ∈ L.E j) :
    Relation.ReflTransGen (AdjIn G (G.verts \ L.X k)) q v₁ :=
  connOn_of_cut_two hT.cc Finset.sdiff_subset (by rw [cut_compl (L.sub k)]; exact (L.side k hk).2.2.2) q
    (Finset.mem_sdiff.mpr ⟨L.E_sub j hq, Finset.disjoint_left.mp (L.E_disjoint_X hj) hq⟩) v₁
    (Finset.mem_sdiff.mpr ⟨hT.mem₁, L.v₁_not_mem_X hk⟩)

end XLayers

end WaveTurbulence.TVine.Struct
