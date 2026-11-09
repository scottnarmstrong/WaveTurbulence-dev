/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Thm6Ext
public import WaveTurbulence.Foundations.TVine.Struct.MBridge
import Mathlib.Tactic

/-!
# N3 Theorem 6 (`layervine` for T-vines), assembled (packet L3)

* `layervineStructure_of_ctx`: from the T6 context (cut context, joint degrees, N3 Lemma 6.2) and the U-level piece
  shape of `groupGraph M S`, the atom-level structure `LayervineStructure M S v₁ v₂` of `Struct.Statement`;
* `pieceShapeU_of`: the molecule-level piece shape gives the U-level one;
* **`layervine_of_pieceShape : PendantPolesInput → PieceShapeStatement → LayervineStatement`**.

Proof (the uncrossing form of N3 §1.4): the spine is the `𝒳`-chain of `v₂`-sides (`XLayers`), with the P-b layer
skipped (`Ext`); the pendant is the `𝒦`-chain of joint-free 2-poles (`KChain`), its layers `Y k` peeling `H`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

section lists

variable {α : Type*}

theorem unionAll_cons {V : Type*} [DecidableEq V] (a : Finset V) (l : List (Finset V)) :
    unionAll (a :: l) = a ∪ unionAll l := rfl

theorem get_map_range (f : ℕ → α) (n : ℕ) (i : Fin ((List.range n).map f).length) :
    ((List.range n).map f).get i = f i.val := by
  simp [List.get_eq_getElem]

theorem get_of_eq_map_range {l : List α} {f : ℕ → α} {n : ℕ} (hl : l = (List.range n).map f)
    (i : Fin l.length) : l.get i = f i.val := by
  subst hl; exact get_map_range f n i

end lists

namespace KChain

variable {V : Type*} [DecidableEq V] {G : UMultigraph V} {v₁ v₂ : V} (C : KChain G v₁ v₂)

theorem unionAll_drop : ∀ m k, k + m = C.s → unionAll (((List.range C.s).map C.Y).drop k) = C.Kd k
  | 0, k, h => by
    rw [List.drop_eq_nil_of_le (by simp; omega), C.bot k (by omega)]; rfl
  | m + 1, k, h => by
    rw [List.drop_eq_getElem_cons (by simp; omega), unionAll_cons, unionAll_drop m (k + 1) (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    exact (C.Kd_eq_union k).symm

end KChain

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Pieces sharing an atom are equal. -/
theorem piece_eq_of_mem {G : UMultigraph V} {v₁ v₂ : V} {P Q : Finset V} (hP : P ∈ piecesU G v₁ v₂)
    (hQ : Q ∈ piecesU G v₁ v₂) {u : V} (huP : u ∈ P) (huQ : u ∈ Q) : P = Q := by
  obtain ⟨hPI, -, hPs⟩ := piece_props hP
  obtain ⟨hQI, -, hQs⟩ := piece_props hQ
  ext w
  constructor
  · intro hw; exact (hQs u huQ w (hPI hw)).mpr ((hPs u huP w (hPI hw)).mp hw)
  · intro hw; exact (hPs u huP w (hQI hw)).mpr ((hQs u huQ w (hQI hw)).mp hw)

theorem rtg_symm_adjIn {G : UMultigraph V} {A : Finset V} {a b : V}
    (h : Relation.ReflTransGen (AdjIn G A) a b) : Relation.ReflTransGen (AdjIn G A) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head ⟨hbc.2.1, hbc.1, by rw [Sym2.eq_swap]; exact hbc.2.2⟩ ih

theorem rtg_mono_adjIn {G : UMultigraph V} {A B : Finset V} (hAB : A ⊆ B) {a b : V}
    (h : Relation.ReflTransGen (AdjIn G A) a b) : Relation.ReflTransGen (AdjIn G B) a b := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .tail ih ⟨hAB hbc.1, hAB hbc.2.1, hbc.2.2⟩

/-- **N3 Theorem 6 (i)–(iii)** from the T6 context and the U-level piece shape. -/
theorem layervineStructure_of_ctx {M : Molecule V D} {S : Finset V} {v₁ v₂ : V}
    (hT : T6Ctx (groupGraph M S) v₁ v₂) (hPS : PieceShapeU (groupGraph M S) v₁ v₂) :
    LayervineStructure M S v₁ v₂ := by
  classical
  set G := groupGraph M S with hGdef
  have hGS : G.verts = S := rfl
  have hw := symm_wG G
  -- interior nonempty (the core)
  have hint : (Core.interior G v₁ v₂).Nonempty := by
    obtain ⟨core, hcore, -⟩ := hPS
    obtain ⟨hI, ⟨x, hx⟩, -⟩ := piece_props hcore
    exact ⟨x, hI hx⟩
  obtain ⟨L⟩ := exists_xLayers hT hint
  obtain ⟨C⟩ := exists_kChain hT
  have hK0 : C.Kd 0 = Hp G v₁ v₂ := C.Kd_zero_eq_Hp hT
  set H := Hp G v₁ v₂ with hHdef
  -- the lists
  set sp : List (Finset V) := (List.range L.r).map fun j => L.Ext (j + 1) with hsp
  set pd : List (Finset V) := (List.range C.s).map C.Y with hpd
  have hext : extSpine v₁ v₂ sp = (List.range (L.r + 2)).map L.Ext := by
    rw [show L.r + 2 = (L.r + 1) + 1 from rfl, List.range_succ, List.range_succ_eq_map, List.cons_append,
      List.map_cons, List.map_append, List.map_map, List.map_singleton, L.Ext_zero hT, L.Ext_last hT]
    rfl
  have hspget : ∀ i : Fin sp.length, sp.get i = L.Ext (i.val + 1) := fun i => get_of_eq_map_range hsp i
  have hsplen : sp.length = L.r := by rw [hsp]; simp
  have hpdget : ∀ k : Fin pd.length, pd.get k = C.Y k.val := fun k => get_of_eq_map_range hpd k
  have hpdlen : pd.length = C.s := by rw [hpd]; simp
  have hextlen : (extSpine v₁ v₂ sp).length = L.r + 2 := by rw [hext]; simp
  have hextget : ∀ i : Fin (extSpine v₁ v₂ sp).length, (extSpine v₁ v₂ sp).get i = L.Ext i.val :=
    fun i => get_of_eq_map_range hext i
  have hmemsp : ∀ P, P ∈ sp ↔ ∃ j, 1 ≤ j ∧ j ≤ L.r ∧ P = L.Ext j := by
    intro P; rw [hsp, List.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩; rw [List.mem_range] at hj; exact ⟨j + 1, by omega, by omega, rfl⟩
    · rintro ⟨j, h1, h2, rfl⟩; exact ⟨j - 1, List.mem_range.mpr (by omega), by congr 1; omega⟩
  have hmempd : ∀ P, P ∈ pd ↔ ∃ k, k < C.s ∧ P = C.Y k := by
    intro P; rw [hpd, List.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, List.mem_range.mp hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, List.mem_range.mpr hk, rfl⟩
  -- the pendant pieces lie in H, the spine pieces outside
  have hYH : ∀ k, C.Y k ⊆ H := fun k => hK0 ▸ (C.Y_sub k).trans (C.anti (Nat.zero_le k))
  have hcross : ∀ {A B : Finset V}, A ⊆ S → B ⊆ S → Disjoint A B → crossBonds M A B = eW (wG G) A B :=
    fun hA hB hAB => crossBonds_eq_eW M hA hB hAB
  have hExtS : ∀ j, L.Ext j ⊆ S := fun j => L.Ext_sub j
  -- every piece is a spine piece or a pendant piece
  have hcover : ∀ Q ∈ piecesU G v₁ v₂, (∃ j, 1 ≤ j ∧ j ≤ L.r ∧ Q = L.Ext j) ∨ (∃ k, k < C.s ∧ Q = C.Y k) := by
    intro Q hQ
    obtain ⟨hQI, ⟨u, hu⟩, -⟩ := piece_props hQ
    have huI := hQI hu
    by_cases huH : u ∈ H
    · right
      have hex : ∃ k, u ∉ C.Kd (k + 1) := ⟨C.s, by rw [C.bot (C.s + 1) (by omega)]; simp⟩
      set k := Nat.find hex
      have hk1 : u ∉ C.Kd (k + 1) := Nat.find_spec hex
      have hkK : u ∈ C.Kd k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0, hK0]; exact huH
        · have := Nat.find_min hex (show k - 1 < k by omega)
          rw [Nat.sub_add_cancel hk0] at this
          exact not_not.mp this
      have hks : k < C.s := by
        by_contra h; push Not at h; rw [C.bot k h] at hkK; exact absurd hkK (Finset.notMem_empty _)
      exact ⟨k, hks, piece_eq_of_mem hQ (C.Y_piece hT hks) hu (Finset.mem_sdiff.mpr ⟨hkK, hk1⟩)⟩
    · left
      obtain ⟨i, hit, hui⟩ := L.exists_layer (interior_subset_verts v₁ v₂ huI)
      rw [mem_interior] at huI
      have hi0 : i ≠ 0 := fun h => huI.2.2 (by rw [h, L.E_zero hT] at hui; exact Finset.mem_singleton.mp hui)
      have hit' : i ≠ L.t := fun h => huI.2.1 (by rw [h, L.E_top hT] at hui; exact Finset.mem_singleton.mp hui)
      have hne : L.E i ≠ H := fun h => huH (h ▸ hui)
      obtain ⟨j, hj, hsk⟩ := L.sk_surj hT hit hne
      have hj0 : j ≠ 0 := fun h => hi0 (by rw [← hsk, h, L.sk_zero])
      have hjr : j ≠ L.r + 1 := fun h => hit' (by rw [← hsk, h, L.sk_last])
      exact ⟨j, by omega, by omega, piece_eq_of_mem hQ (L.Ext_piece hT (by omega) (by omega)) hu
        (Finset.mem_sdiff.mpr ⟨hsk ▸ hui, huH⟩)⟩
  have hlistpieces : (sp ++ pd).toFinset = piecesU G v₁ v₂ := by
    ext Q
    rw [List.mem_toFinset, List.mem_append, hmemsp, hmempd]
    constructor
    · rintro (⟨j, h1, h2, rfl⟩ | ⟨k, hk, rfl⟩)
      · exact L.Ext_piece hT h1 h2
      · exact C.Y_piece hT hk
    · exact hcover Q
  refine ⟨sp, pd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Nodup
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsp, List.nodup_map_iff_inj_on List.nodup_range]
      intro a ha b hb he
      rw [List.mem_range] at ha hb
      by_contra hne
      obtain ⟨x, hx⟩ := L.Ext_nonempty hT (j := a + 1) (by omega)
      exact Finset.disjoint_left.mp (L.Ext_disjoint (show a + 1 ≠ b + 1 by omega)) hx (he ▸ hx)
    · rw [hpd, List.nodup_map_iff_inj_on List.nodup_range]
      intro a ha b hb he
      rw [List.mem_range] at ha hb
      by_contra hne
      obtain ⟨x, hx⟩ := C.Y_nonempty ha
      exact Finset.disjoint_left.mp (C.Y_disjoint hne) hx (he ▸ hx)
    · intro P hP Q hQ hPQ
      obtain ⟨j, h1, h2, rfl⟩ := (hmemsp P).mp hP
      obtain ⟨k, hk, rfl⟩ := (hmempd Q).mp hQ
      obtain ⟨x, hx⟩ := L.Ext_nonempty hT (j := j) (by omega)
      exact Finset.disjoint_left.mp (L.Ext_disjoint_Hp j) hx (hYH k (hPQ ▸ hx))
  · -- the pieces
    rw [pieces_eq]; exact hlistpieces
  · -- spine = separating pieces
    intro P hP
    rw [pieces_eq] at hP
    rw [connIn_iff M Finset.sdiff_subset, hmemsp]
    constructor
    · rintro ⟨j, h1, h2, rfl⟩ hc
      have hpos := L.sk_pos h1
      have hlt := L.sk_lt_t h2
      obtain ⟨k, hk⟩ : ∃ k, L.sk j = k + 1 := ⟨L.sk j - 1, by omega⟩
      have hne := L.E_sk_ne_Hp hT (j := j) (by omega)
      rw [hk] at hne hlt
      have := L.separates hT hlt hne
      apply this
      have hset : G.verts \ (L.E (k + 1) \ H) = S \ L.Ext j := by unfold XLayers.Ext; rw [hk]; rfl
      rw [hset]
      exact rtg_symm_adjIn hc
    · intro hsep
      by_contra hnot
      apply hsep
      -- P is a pendant piece
      have hPpd : ∃ k, k < C.s ∧ P = C.Y k := by
        rcases hcover P hP with h | h
        · exact absurd h hnot
        · exact h
      obtain ⟨k, hk, rfl⟩ := hPpd
      -- verts ∖ H is connected and contains both joints
      have hHne : H.Nonempty := ⟨_, hYH k (C.Y_nonempty hk).choose_spec⟩
      have hKs := (Hp_cases hT).resolve_left (Finset.nonempty_iff_ne_empty.mp hHne)
      have hconn := connOn_of_cut_two hT.cc (X := G.verts \ H) Finset.sdiff_subset
        (by rw [cut_compl hKs.1]; exact hKs.2.2.2.2)
      have h := hconn v₁ (Finset.mem_sdiff.mpr ⟨hT.mem₁, hKs.2.1⟩) v₂ (Finset.mem_sdiff.mpr ⟨hT.mem₂, hKs.2.2.1⟩)
      exact rtg_mono_adjIn (Finset.sdiff_subset_sdiff subset_rfl (hYH k)) h
  · -- the order
    intro i
    have hi : i.val < L.r := by have := i.2; omega
    have hspi := hspget i
    have h1 : 1 ≤ i.val + 1 := by omega
    have hpos := L.sk_pos h1
    have hlt := L.sk_lt_t (j := i.val + 1) (by omega)
    obtain ⟨m, hm⟩ : ∃ m, L.sk (i.val + 1) = m + 1 := ⟨L.sk (i.val + 1) - 1, by omega⟩
    refine ⟨fun j hji q hq => ?_, fun j hij q hq => ?_⟩
    · rw [hspget] at hq
      rw [hspi, connIn_iff M Finset.sdiff_subset]
      have hlay := L.sk_lt (show j.val + 1 < i.val + 1 by omega)
      have h := L.conn_before hT (k := m) (j := L.sk (j.val + 1)) (by omega) (by omega) (L.Ext_sub_E _ hq)
      refine rtg_mono_adjIn (fun x hx => Finset.mem_sdiff.mpr ⟨L.sub m hx, fun hxE => ?_⟩) h
      have := L.Ext_sub_E _ hxE
      rw [hm] at this
      exact Finset.disjoint_left.mp (L.E_disjoint_X (Nat.lt_succ_self m)) this hx
    · rw [hspget] at hq
      rw [hspi, connIn_iff M Finset.sdiff_subset]
      have hlay := L.sk_lt (show i.val + 1 < j.val + 1 by omega)
      have h := L.conn_after hT (k := m + 1) (j := L.sk (j.val + 1)) (by omega) (by omega) (L.Ext_sub_E _ hq)
      refine rtg_mono_adjIn (fun x hx => Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, fun hxE => ?_⟩) h
      have := L.Ext_sub_E _ hxE
      rw [hm] at this
      exact (Finset.mem_sdiff.mp hx).2 (L.E_subset_X le_rfl this)
  · -- consecutive members: 1 or 2 bonds
    intro i j hij
    rw [hextget, hextget]
    have hj : j.val < L.r + 2 := by have := j.2; omega
    rw [hcross (hExtS _) (hExtS _) (L.Ext_disjoint (by omega))]
    obtain ⟨jv, hjv⟩ := j
    simp only at hij hj ⊢
    subst hij
    rcases L.eW_Ext_succ hT (a := i.val) (by omega) with ⟨h, -⟩ | ⟨h, -⟩
    · right; exact h
    · left; exact h
  · -- non-consecutive members: none
    intro i j hij
    rw [hextget, hextget]
    have hj : j.val < L.r + 2 := by have := j.2; omega
    rw [hcross (hExtS _) (hExtS _) (L.Ext_disjoint (by omega))]
    exact L.eW_Ext_far hT hij (by omega)
  · -- at most one single bond
    intro i j i' j' hij hij' h h'
    rw [hextget, hextget] at h h'
    have hj : j.val < L.r + 2 := by have := j.2; omega
    have hj' : j'.val < L.r + 2 := by have := j'.2; omega
    rw [hcross (hExtS _) (hExtS _) (L.Ext_disjoint (by omega))] at h h'
    rw [← hij] at h
    rw [← hij'] at h'
    exact Fin.ext (L.Ext_one_unique hT (by omega) (by omega) h h')
  · -- r = 0 iff σ = 1
    rw [hsp, List.map_eq_nil_iff, List.range_eq_nil, L.r_eq_zero_iff hT, Molecule.sigma,
      bondsBetween_eq M hT.mem₁ hT.mem₂]
    exact Iff.rfl
  · -- the pendant
    obtain ⟨core, hcoreP, hcs, hrest⟩ := hPS
    have hbig : ∀ P ∈ piecesU G v₁ v₂, 2 ≤ P.card := by
      intro P hP
      by_cases hc : P = core
      · obtain ⟨x, y, z, hxy, hyz, hxz, hP3, -⟩ := hcs
        rw [hc, hP3, Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩]; omega
      · obtain ⟨a, b, hab, rfl, -⟩ := hrest P hP hc
        rw [Finset.card_pair hab]
    have hmulS : ∀ {a b : V}, a ∈ S → b ∈ S → M.bondsBetween a b = G.mult s(a, b) :=
      fun ha hb => bondsBetween_eq M ha hb
    have hpI : ∀ {P : Finset V}, P ∈ piecesU G v₁ v₂ → ∀ x ∈ P, x ∈ S := fun hP x hx =>
      interior_subset_verts v₁ v₂ ((piece_props hP).1 hx)
    have hcutcross : ∀ {P : Finset V}, P ⊆ S → crossBonds M P (S \ P) = cut G P := fun hP => by
      rw [hcross hP Finset.sdiff_subset Finset.disjoint_sdiff]; rfl
    rcases Nat.eq_zero_or_pos C.s with hs0 | hs0
    · -- no pendant
      left
      have hpd0 : pd = [] := by rw [hpd, hs0]; rfl
      refine ⟨hpd0, core, ?_, ?_⟩
      · rcases hcover core hcoreP with ⟨j, h1, h2, he⟩ | ⟨k, hk, -⟩
        · exact (hmemsp core).mpr ⟨j, h1, h2, he⟩
        · omega
      · obtain ⟨x, y, z, hxy, hyz, hxz, hP3, hm, hcase⟩ := hcs
        have hx := hpI hcoreP x (by rw [hP3]; simp)
        have hy := hpI hcoreP y (by rw [hP3]; simp)
        have hz := hpI hcoreP z (by rw [hP3]; simp)
        refine ⟨x, y, z, hxy, hyz, hxz, hP3, by rw [hmulS hx hy]; exact hm, ?_⟩
        rw [hmulS hy hz, hmulS hx hz]
        rcases hcase with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · -- a (D) core has cut 2, hence lies in the (empty) pendant
          exfalso
          have hPI := (piece_props hcoreP).1
          have hcut := cut_triple hT (hPI (by rw [hP3]; simp)) (hPI (by rw [hP3]; simp))
            (hPI (by rw [hP3]; simp)) hxy hyz hxz
          rw [hm, h.1, h.2, ← hP3] at hcut
          obtain ⟨u, hu⟩ := (piece_props hcoreP).2.1
          have hKs : IsKSide G v₁ v₂ core := ⟨hPI.trans (interior_subset_verts v₁ v₂),
            fun h' => (mem_interior.mp (hPI h')).2.1 rfl, fun h' => (mem_interior.mp (hPI h')).2.2 rfl,
            ⟨u, hu⟩, by omega⟩
          have := subset_Hp hKs hu
          have hH0 : Hp G v₁ v₂ = ∅ := by rw [← hHdef, ← hK0]; exact C.bot 0 (by omega)
          rw [hH0] at this
          exact absurd this (Finset.notMem_empty _)
    · right
      obtain ⟨n, hn⟩ : ∃ n, C.s = n + 1 := ⟨C.s - 1, by omega⟩
      have hYn : C.Y n = C.Kd n := by
        rw [KChain.Y, C.bot (n + 1) (by omega), Finset.sdiff_empty]
      have hYnP : C.Y n ∈ piecesU G v₁ v₂ := C.Y_piece hT (by omega)
      have hYn2 : cut G (C.Y n) = 2 := by rw [hYn]; exact (C.side n (by omega)).2.2.2.2
      -- the last pendant layer is the core
      have hYncore : C.Y n = core := by
        by_contra hne
        obtain ⟨a, b, hab, he, hmab⟩ := hrest _ hYnP hne
        have hPI := (piece_props hYnP).1
        have := cut_pair hT (hPI (by rw [he]; simp)) (hPI (by rw [he]; simp)) hab
        rw [← he, hYn2] at this
        rcases hmab with h | h <;> omega
      refine ⟨(List.range n).map C.Y, C.Y n, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpd, hn, List.range_succ, List.map_append, List.map_singleton]
      · -- the (D) core
        obtain ⟨x, y, z, hxy, hyz, hxz, hP3, hm, hcase⟩ := hcs
        rw [← hYncore] at hP3
        have hx := hpI hYnP x (by rw [hP3]; simp)
        have hy := hpI hYnP y (by rw [hP3]; simp)
        have hz := hpI hYnP z (by rw [hP3]; simp)
        have hPI := (piece_props hYnP).1
        have hcut := cut_triple hT (hPI (by rw [hP3]; simp)) (hPI (by rw [hP3]; simp))
          (hPI (by rw [hP3]; simp)) hxy hyz hxz
        rw [← hP3, hYn2, hm] at hcut
        refine ⟨x, y, z, hxy, hyz, hxz, hP3, by rw [hmulS hx hy]; exact hm, ?_, ?_⟩
        · rw [hmulS hy hz]; rcases hcase with h | h | h <;> omega
        · rw [hmulS hx hz]; rcases hcase with h | h | h <;> omega
      · -- the rungs
        intro Y hY
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hY
        rw [List.mem_range] at hk
        have hYP := C.Y_piece hT (show k < C.s by omega)
        have hne : C.Y k ≠ core := by
          rw [← hYncore]; intro he
          obtain ⟨u, hu⟩ := C.Y_nonempty (show k < C.s by omega)
          exact Finset.disjoint_left.mp (C.Y_disjoint (show k ≠ n by omega)) hu (he ▸ hu)
        obtain ⟨a, b, hab, he, -⟩ := hrest _ hYP hne
        have hPI := (piece_props hYP).1
        have hc := cut_pair hT (hPI (by rw [he]; simp)) (hPI (by rw [he]; simp)) hab
        rw [← he, (C.Kd_inner hT (k := k) (by omega)).2.2] at hc
        have ha := hpI hYP a (by rw [he]; simp)
        have hb := hpI hYP b (by rw [he]; simp)
        exact ⟨a, b, hab, he, by rw [hmulS ha hb]; omega⟩
      · -- consecutive pendant layers
        intro k l hkl
        rw [hpdget, hpdget]
        have hl : l.val < C.s := by have := l.2; omega
        rw [hcross ((C.Y_sub _).trans (C.Kd_sub _)) ((C.Y_sub _).trans (C.Kd_sub _)) (C.Y_disjoint (by omega)),
          ← hkl]
        exact C.eW_Y_succ hT (by omega)
      · -- non-consecutive pendant layers
        intro k l hkl
        rw [hpdget, hpdget]
        rw [hcross ((C.Y_sub _).trans (C.Kd_sub _)) ((C.Y_sub _).trans (C.Kd_sub _)) (C.Y_disjoint (by omega))]
        exact C.eW_Y_far hT hkl
      · -- exits and attachment
        intro k
        have hk : k.val < C.s := by have := k.2; omega
        have hKs := C.side k.val hk
        obtain ⟨y, hy, y', hy', x, hx, x', hx', hyy, hxx, hm, hm'⟩ :=
          two_exits hT.cc.loopless hKs.2.2.2.2 (exit_le_one_inner hT hbig hKs) (exit_le_one_outer hT hbig hKs)
        -- the inner ends lie in the layer `Y k`
        have hinY : ∀ {w z : V}, w ∈ C.Kd k.val → z ∈ G.verts \ C.Kd k.val → G.mult s(w, z) = 1 →
            w ∈ C.Y k.val := by
          intro w z hw hz hwz
          refine Finset.mem_sdiff.mpr ⟨hw, fun hw1 => ?_⟩
          rcases Nat.lt_or_ge (k.val + 1) C.s with h1 | h1
          · have h0 := (C.Kd_inner hT h1).1
            have := le_eW_of_mem (w := wG G) hw1 hz
            simp only [wG] at this; omega
          · rw [C.bot _ h1] at hw1; exact absurd hw1 (Finset.notMem_empty _)
        have hyY := hinY hy hx hm
        have hy'Y := hinY hy' hx' hm'
        have hunion : unionAll (pd.drop k.val) = C.Kd k.val := by
          show unionAll (((List.range C.s).map C.Y).drop k.val) = _
          exact C.unionAll_drop (C.s - k.val) k.val (by omega)
        have hKdS : C.Kd k.val ⊆ S := C.Kd_sub _
        refine ⟨x, x', ⟨?_, hxx, ?_, ?_, y, ?_, y', ?_, hyy, ?_, ?_⟩, ?_⟩
        · rw [hunion, hcutcross hKdS]; exact hKs.2.2.2.2
        · rw [hunion]; exact hx
        · rw [hunion]; exact hx'
        · rw [hpdget]; exact hyY
        · rw [hpdget]; exact hy'Y
        · rw [hmulS (Finset.mem_sdiff.mp hx).1 (hKdS hy), Sym2.eq_swap]; exact hm
        · rw [hmulS (Finset.mem_sdiff.mp hx').1 (hKdS hy'), Sym2.eq_swap]; exact hm'
        · -- the attachment of `H = Kd 0`
          intro hk0
          have hk0' : k.val = 0 := hk0
          rw [hk0'] at hx hx' hy hy' hKs
          rw [hK0] at hx hx' hy hy'
          have hHne : H.Nonempty := ⟨y, hy⟩
          have hHKs := (Hp_cases hT).resolve_left (Finset.nonempty_iff_ne_empty.mp hHne)
          have hcutH : eW (wG G) H (G.verts \ H) = 2 := hHKs.2.2.2.2
          obtain ⟨i₁, hi0, hit, hiE⟩ := L.Hp_loc hT hHne
          obtain ⟨k₁, rfl⟩ : ∃ k₁, i₁ = k₁ + 1 := ⟨i₁ - 1, by omega⟩
          -- an outer end of an exit bond lies in any part of the complement that already carries both bonds
          have hloc : ∀ {Z : Finset V}, Z ⊆ G.verts \ H → 2 ≤ eW (wG G) H Z →
              ∀ {w z : V}, w ∈ H → z ∈ G.verts \ H → G.mult s(w, z) = 1 → z ∈ Z := by
            intro Z hZ h2 w z hw hz hwz
            by_contra hzZ
            have hd : Disjoint Z {z} := Finset.disjoint_singleton_right.mpr hzZ
            have hsub : Z ∪ {z} ⊆ G.verts \ H := Finset.union_subset hZ (Finset.singleton_subset_iff.mpr hz)
            have h1 := eW_mono_right (w := wG G) H hsub
            rw [eW_union_right _ hd] at h1
            have h2' : 1 ≤ eW (wG G) H {z} := by
              have := le_eW_of_mem (w := wG G) hw (Finset.mem_singleton_self z)
              simp only [wG] at this; omega
            omega
          by_cases hpb : L.E (k₁ + 1) = H
          · -- P-b
            right
            obtain ⟨hb02, hb01, hb12⟩ := L.pb_counts hT hit hpb
            have hne0 : L.E k₁ ≠ H := fun h => L.not_two_Hp (show k₁ ≠ k₁ + 1 by omega) (by omega) h hpb
            have hne2 : L.E (k₁ + 2) ≠ H := fun h => L.not_two_Hp (show k₁ + 2 ≠ k₁ + 1 by omega) (by omega) h hpb
            obtain ⟨a, ha, hska⟩ := L.sk_surj hT (by omega) hne0
            have hart : a ≤ L.r := by
              by_contra h; push Not at h
              have := L.sk_last; have := L.sk_mono (show L.r + 1 ≤ a by omega); omega
            have hska1 : L.sk (a + 1) = k₁ + 2 := by
              rcases L.sk_succ a with h | ⟨h, -⟩
              · exact absurd (by rw [h, hska]; exact hpb) (L.E_sk_ne_Hp hT (j := a + 1) (by omega))
              · omega
            have hA : L.Ext a = L.E k₁ := by
              unfold XLayers.Ext; rw [hska]; exact L.E_sdiff_Hp_of_ne hT (show k₁ + 1 ≠ k₁ by omega) hiE
            have hB : L.Ext (a + 1) = L.E (k₁ + 2) := by
              unfold XLayers.Ext; rw [hska1]; exact L.E_sdiff_Hp_of_ne hT (show k₁ + 1 ≠ k₁ + 2 by omega) hiE
            refine ⟨⟨a, by rw [hextlen]; omega⟩, ⟨a + 1, by rw [hextlen]; omega⟩, rfl, ?_, ?_⟩
            · rw [hextget, hextget]
              simp only
              rw [hcross (hExtS _) (hExtS _) (L.Ext_disjoint (by omega)), hA, hB]
              exact hb02
            · rw [hextget, hextget]
              simp only
              rw [hA, hB]
              -- the two exits split between `E k₁` and `E (k₁+2)`
              have hHE0 : eW (wG G) H (L.E k₁) = 1 := by rw [eW_comm hw, ← hpb]; exact hb01
              have hHE2 : eW (wG G) H (L.E (k₁ + 2)) = 1 := by rw [← hpb]; exact hb12
              have hE0sub : L.E k₁ ⊆ G.verts \ H := fun z hz => Finset.mem_sdiff.mpr ⟨L.E_sub _ hz,
                fun hzH => Finset.disjoint_left.mp (L.E_disjoint (show k₁ ≠ k₁ + 1 by omega)) hz (hpb ▸ hzH)⟩
              have hE2sub : L.E (k₁ + 2) ⊆ G.verts \ H := fun z hz => Finset.mem_sdiff.mpr ⟨L.E_sub _ hz,
                fun hzH => Finset.disjoint_left.mp (L.E_disjoint (show k₁ + 2 ≠ k₁ + 1 by omega)) hz (hpb ▸ hzH)⟩
              have hdisj : Disjoint (L.E k₁) (L.E (k₁ + 2)) := L.E_disjoint (by omega)
              have hsum : 2 ≤ eW (wG G) H (L.E k₁ ∪ L.E (k₁ + 2)) := by
                rw [eW_union_right _ hdisj]; omega
              have hsub : L.E k₁ ∪ L.E (k₁ + 2) ⊆ G.verts \ H := Finset.union_subset hE0sub hE2sub
              have hxin := hloc hsub hsum hy hx hm
              have hx'in := hloc hsub hsum hy' hx' hm'
              -- not both in the same layer
              have hpair : ∀ {Z : Finset V}, x ∈ Z → x' ∈ Z → 2 ≤ eW (wG G) H Z := by
                intro Z hxZ hx'Z
                have h1 : eW (wG G) {y, y'} {x, x'} ≤ eW (wG G) H Z :=
                  (eW_mono_left _ (Finset.insert_subset hy (Finset.singleton_subset_iff.mpr hy'))).trans
                    (eW_mono_right _ (Finset.insert_subset hxZ (Finset.singleton_subset_iff.mpr hx'Z)))
                have h2 : G.mult s(y, x) + G.mult s(y', x') ≤ eW (wG G) {y, y'} {x, x'} := by
                  unfold eW
                  rw [Finset.sum_pair hyy, Finset.sum_pair hxx, Finset.sum_pair hxx]
                  simp only [wG]; omega
                omega
              rcases Finset.mem_union.mp hxin with h1 | h1 <;> rcases Finset.mem_union.mp hx'in with h2 | h2
              · have := hpair h1 h2; omega
              · exact Or.inl ⟨h1, h2⟩
              · exact Or.inr ⟨h2, h1⟩
              · have := hpair h1 h2; omega
          · -- P-a
            left
            obtain ⟨-, -, h2⟩ := L.Hp_pa hT hit hiE hpb hHne
            have hsubE : L.E (k₁ + 1) \ H ⊆ G.verts \ H := Finset.sdiff_subset_sdiff (L.E_sub _) subset_rfl
            have hxin := hloc hsubE h2.ge hy hx hm
            have hx'in := hloc hsubE h2.ge hy' hx' hm'
            obtain ⟨j₁, hj₁, hsk₁⟩ := L.sk_surj hT (by omega) hpb
            have hj0 : j₁ ≠ 0 := fun h => by rw [h, L.sk_zero] at hsk₁; omega
            have hjr : j₁ ≠ L.r + 1 := fun h => by rw [h, L.sk_last] at hsk₁; omega
            have hExt : L.Ext j₁ = L.E (k₁ + 1) \ H := by unfold XLayers.Ext; rw [hsk₁]
            -- its cut is 6
            have hcut6 : cut G (L.Ext j₁) = 6 := by
              have h4 := (L.cut_E_interior hT hit hpb).2.2
              have hsplit := cut_union_disjoint (G := G) (X := L.E (k₁ + 1) \ H) (Y := H)
                (Finset.sdiff_subset.trans (L.E_sub _)) hHKs.1 Finset.sdiff_disjoint
              rw [Finset.sdiff_union_of_subset hiE, h4, hHKs.2.2.2.2, eW_comm hw, h2] at hsplit
              rw [hExt]; omega
            refine ⟨⟨j₁ - 1, by rw [hsplen]; omega⟩, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hspget]; simp only; rw [show j₁ - 1 + 1 = j₁ by omega, hExt]; exact hxin
            · rw [hspget]; simp only; rw [show j₁ - 1 + 1 = j₁ by omega, hExt]; exact hx'in
            · rw [hspget]; simp only; rw [show j₁ - 1 + 1 = j₁ by omega]
              have hP := L.Ext_piece hT (j := j₁) (by omega) (by omega)
              rcases piece_cut_cases hT ⟨core, hcoreP, hcs, hrest⟩ hP with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, a, b, hab, he, hm1⟩
              · omega
              · omega
              · have ha := hpI hP a (by rw [he]; simp)
                have hb := hpI hP b (by rw [he]; simp)
                exact ⟨a, b, hab, he, by rw [hmulS ha hb]; exact hm1⟩
            · rw [hspget]; simp only; rw [show j₁ - 1 + 1 = j₁ by omega, hcutcross (hExtS _)]; exact hcut6
            · intro P hP h6
              rw [hspget]; simp only; rw [show j₁ - 1 + 1 = j₁ by omega]
              rw [pieces_eq] at hP
              have hPS' : P ⊆ S := fun z hz => hpI hP z hz
              rw [hcutcross hPS'] at h6
              rcases hcover P hP with ⟨j, h1, h2', rfl⟩ | ⟨k, hk, rfl⟩
              · by_contra hne
                have hjj : L.sk j ≠ k₁ + 1 := fun h => hne (by rw [show j = j₁ from by
                    by_contra hjj'
                    rcases Nat.lt_or_gt_of_ne hjj' with h' | h'
                    · exact absurd (h.trans hsk₁.symm) (L.sk_lt h').ne
                    · exact absurd (h.trans hsk₁.symm) (L.sk_lt h').ne'])
                have hpos := L.sk_pos h1
                have hlt := L.sk_lt_t h2'
                obtain ⟨m, hm⟩ : ∃ m, L.sk j = m + 1 := ⟨L.sk j - 1, by omega⟩
                have hneH := L.E_sk_ne_Hp hT (j := j) (by omega)
                rw [hm] at hneH hlt
                have h4 := (L.cut_E_interior hT hlt hneH).2.2
                have : L.Ext j = L.E (m + 1) := by
                  unfold XLayers.Ext; rw [hm]
                  exact L.E_sdiff_Hp_of_ne hT (show k₁ + 1 ≠ m + 1 by omega) hiE
                rw [this] at h6; omega
              · exfalso
                rcases Nat.lt_or_ge (k + 1) C.s with h1 | h1
                · have := (C.Kd_inner hT h1).2.2; omega
                · have hk' : k = n := by omega
                  subst hk'
                  omega

/-- The pieces do not depend on the order of the joints. -/
theorem piecesU_comm (G : UMultigraph V) (a b : V) : piecesU G a b = piecesU G b a := by
  classical
  unfold piecesU
  rw [interior_comm G a b]

/-- The molecule-level piece shape (`PieceShapeStatement`'s conclusion) gives the U-level one. -/
theorem pieceShapeU_of {M : Molecule V D} {S : Finset V} {j₁ j₂ : V}
    (h : ∃ core ∈ M.pieces S j₁ j₂, CoreShape M core ∧ (∀ P ∈ M.pieces S j₁ j₂, P ≠ core → TwoAtomPiece M P) ∧
      S.card = 2 * ((M.pieces S j₁ j₂).card - 1) + 5) :
    PieceShapeU (groupGraph M S) j₁ j₂ := by
  obtain ⟨core, hcore, hcs, hrest, -⟩ := h
  rw [pieces_eq] at hcore
  have hS : ∀ {P : Finset V}, P ∈ piecesU (groupGraph M S) j₁ j₂ → ∀ x ∈ P, x ∈ S := fun hP x hx =>
    interior_subset_verts j₁ j₂ ((piece_props hP).1 hx)
  refine ⟨core, hcore, ?_, fun P hP hne => ?_⟩
  · obtain ⟨x, y, z, hxy, hyz, hxz, hP3, hm, hcase⟩ := hcs
    have hx := hS hcore x (by rw [hP3]; simp)
    have hy := hS hcore y (by rw [hP3]; simp)
    have hz := hS hcore z (by rw [hP3]; simp)
    rw [bondsBetween_eq M hx hy] at hm
    rw [bondsBetween_eq M hy hz, bondsBetween_eq M hx hz] at hcase
    exact ⟨x, y, z, hxy, hyz, hxz, hP3, hm, hcase⟩
  · have hP' := hP
    rw [← pieces_eq] at hP'
    obtain ⟨a, b, hab, he, hm⟩ := hrest P hP' hne
    have ha := hS hP a (by rw [he]; simp)
    have hb := hS hP b (by rw [he]; simp)
    rw [bondsBetween_eq M ha hb] at hm
    exact ⟨a, b, hab, he, hm⟩

theorem PieceShapeU.swap {G : UMultigraph V} {a b : V} (h : PieceShapeU G a b) : PieceShapeU G b a := by
  unfold PieceShapeU at h ⊢; rw [← piecesU_comm]; exact h

/-- **N3 Theorem 6 (i)–(iii)** (`LayervineStatement`, both labellings), from the piece-shape theorem and N3 Lemma 6.2
(named input `PendantPolesInput`, owner L1). -/
theorem layervine_of_pieceShape (h62 : PendantPolesInput.{u}) (hPS : PieceShapeStatement.{u, v}) :
    LayervineStatement.{u, v} := by
  intro V D _ _ _ M S j₁ j₂ hT
  have hTU := ((isTVine_iff M).mp hT).2
  have hctx := t6Ctx_of_isTVineU h62 hTU
  have hps := pieceShapeU_of (hPS M S j₁ j₂ hT)
  exact ⟨layervineStructure_of_ctx hctx hps, layervineStructure_of_ctx hctx.swap hps.swap⟩

end WaveTurbulence.TVine.Struct
