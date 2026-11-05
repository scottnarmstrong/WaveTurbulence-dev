/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.MShape

/-!
# Finite sets of enhanced dominant couples, and the leading terms as sums over them

* `ED n`: the (finite) set of well-formed enhanced dominant couple codes with `n(𝒬) = 2n`; `domCodes n`: the
  well-formed dominant couple codes of B2 with `n(𝒬) = 2n`.
* `sum_domCodes_specialSets`: summing over `𝒬 ∈ domCodes n` and its special subsets `Z` is summing over
  `ED n` (the map `(𝒬, Z) ↦ enh Z 𝒬` is a bijection; ENHANCED `mem_specialSets_iff`, `specialList_nodup`).
* `specialWeight_eq_sw`: B2's `specialWeight` (F61) is `ECpl.sw` of the enhanced code.
* `app_eq_sum`: **B2's leading term `(K*_𝒬)_app`** of a dominant code as a sum over its enhanced codes:
  `2^{-2n} δ^n ζ*(𝒬) ∑_e sw(e) 𝒥ℬ*_𝒬(t,s) ℳ*_{shape e}(k)`.
* `sum_app_eq`: `∑_{𝒬 ∈ domCodes n} (K*_𝒬)_app = 2^{-2n} δ^n ∑_{e ∈ ED n} ζ*(e) sw(e) 𝒥ℬ*_e(t,s) ℳ*_{shape e}(k)`.
-/

@[expose] public section

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links Finset

/-! ### Finiteness -/

theorem EChain.one_le_hsize {X : EChain} (h : X.isNil = false) : 1 ≤ X.hsize := by
  cases X with
  | nil => simp [EChain.isNil] at h
  | pair => simp [EChain.hsize]

/-- Bounded well-formed enhanced codes and chains form finite sets. -/
theorem finite_bounded (N : ℕ) : {e : ECpl | e.wf = true ∧ e.hsize ≤ N}.Finite ∧
    {X : EChain | X.wf = true ∧ X.hsize ≤ N}.Finite := by
  induction N with
  | zero =>
    have hC : {X : EChain | X.wf = true ∧ X.hsize ≤ 0} ⊆ {EChain.nil} := by
      rintro (_ | ⟨m, I, Qr, Qg, rest⟩) ⟨-, h⟩
      · rfl
      · simp [EChain.hsize] at h
    refine ⟨(Set.finite_singleton ECpl.triv).subset ?_, (Set.finite_singleton _).subset hC⟩
    rintro (_ | ⟨c, Q₁, Q₂, Q₃⟩ | ⟨Xp, Xm, Qlp⟩) ⟨hw, h⟩
    · rfl
    · simp [ECpl.hsize] at h
    · exfalso
      simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.and_eq_false_iff] at hw
      simp only [ECpl.hsize, nonpos_iff_eq_zero, Nat.add_eq_zero_iff] at h
      rcases hw.2 with h' | h'
      · have := EChain.one_le_hsize h'; omega
      · have := EChain.one_le_hsize h'; omega
  | succ N ih =>
    obtain ⟨hS, hC⟩ := ih
    have hC' : {X : EChain | X.wf = true ∧ X.hsize ≤ N + 1} ⊆ {EChain.nil} ∪
        (fun p : MiniTreeCode × Bool × ECpl × ECpl × EChain =>
          EChain.pair p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ''
          (Set.univ ×ˢ Set.univ ×ˢ {e : ECpl | e.wf = true ∧ e.hsize ≤ N} ×ˢ
            {e : ECpl | e.wf = true ∧ e.hsize ≤ N} ×ˢ {X : EChain | X.wf = true ∧ X.hsize ≤ N}) := by
      rintro (_ | ⟨m, I, Qr, Qg, rest⟩) ⟨hw, h⟩
      · exact Or.inl rfl
      · simp only [EChain.wf, Bool.and_eq_true] at hw
        simp only [EChain.hsize] at h
        refine Or.inr ⟨(m, I, Qr, Qg, rest), ?_, rfl⟩
        simp only [Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, true_and]
        exact ⟨⟨hw.1.1, by omega⟩, ⟨hw.1.2, by omega⟩, ⟨hw.2, by omega⟩⟩
    have hCf : {X : EChain | X.wf = true ∧ X.hsize ≤ N + 1}.Finite :=
      ((Set.finite_singleton _).union ((Set.finite_univ.prod (Set.finite_univ.prod
        (hS.prod (hS.prod hC)))).image _)).subset hC'
    refine ⟨?_, hCf⟩
    have hS' : {e : ECpl | e.wf = true ∧ e.hsize ≤ N + 1} ⊆ {ECpl.triv} ∪
        ((fun p : MiniCplCode × ECpl × ECpl × ECpl => ECpl.type1 p.1 p.2.1 p.2.2.1 p.2.2.2) ''
          (Set.univ ×ˢ {e : ECpl | e.wf = true ∧ e.hsize ≤ N} ×ˢ
            {e : ECpl | e.wf = true ∧ e.hsize ≤ N} ×ˢ {e : ECpl | e.wf = true ∧ e.hsize ≤ N}) ∪
        (fun p : EChain × EChain × ECpl => ECpl.type2 p.1 p.2.1 p.2.2) ''
          ({X : EChain | X.wf = true ∧ X.hsize ≤ N + 1} ×ˢ
            {X : EChain | X.wf = true ∧ X.hsize ≤ N + 1} ×ˢ {e : ECpl | e.wf = true ∧ e.hsize ≤ N})) := by
      rintro (_ | ⟨c, Q₁, Q₂, Q₃⟩ | ⟨Xp, Xm, Qlp⟩) ⟨hw, h⟩
      · exact Or.inl rfl
      · simp only [ECpl.wf, Bool.and_eq_true] at hw
        simp only [ECpl.hsize] at h
        refine Or.inr (Or.inl ⟨(c, Q₁, Q₂, Q₃), ?_, rfl⟩)
        simp only [Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, true_and]
        exact ⟨⟨hw.1.1, by omega⟩, ⟨hw.1.2, by omega⟩, ⟨hw.2, by omega⟩⟩
      · simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          Bool.and_eq_false_iff] at hw
        simp only [ECpl.hsize] at h
        have h1 : 1 ≤ Xp.hsize + Xm.hsize := by
          rcases hw.2 with h' | h'
          · have := EChain.one_le_hsize h'; omega
          · have := EChain.one_le_hsize h'; omega
        refine Or.inr (Or.inr ⟨(Xp, Xm, Qlp), ?_, rfl⟩)
        simp only [Set.mem_prod, Set.mem_ofPred_eq]
        exact ⟨⟨hw.1.1.1.1, by omega⟩, ⟨hw.1.1.1.2, by omega⟩, ⟨hw.1.1.2, by omega⟩⟩
    exact ((Set.finite_singleton _).union (((Set.finite_univ.prod (hS.prod (hS.prod hS))).image _).union
      ((hCf.prod (hCf.prod hS)).image _))).subset hS'

theorem finite_ED (n : ℕ) : {e : ECpl | e.wf = true ∧ e.hsize = n}.Finite :=
  (finite_bounded n).1.subset fun _ he => ⟨he.1, he.2.le⟩

/-- **The well-formed enhanced dominant couple codes of order `2n`.** -/
noncomputable def ED (n : ℕ) : Finset ECpl := (finite_ED n).toFinset

theorem mem_ED {n : ℕ} {e : ECpl} : e ∈ ED n ↔ e.wf = true ∧ e.hsize = n := by
  simp [ED]

theorem wf_enh {w : ℕ} (Z : Finset (Fin w × Path)) {Q : RegCpl} (hQ : Q.dominant = true)
    (a b : Fin w × Path) : (enh Z Q a b).wf = Q.wf := by
  rw [← ECpl.wf_code, code_enh Z Q hQ]

theorem hsize_enh {w : ℕ} (Z : Finset (Fin w × Path)) {Q : RegCpl} (hQ : Q.dominant = true)
    (a b : Fin w × Path) : 2 * (enh Z Q a b).hsize = Q.size := by
  rw [← ECpl.size_code, code_enh Z Q hQ]

theorem finite_domCodes (n : ℕ) :
    {Q : RegCpl | Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n}.Finite := by
  refine ((finite_ED n).image ECpl.code).subset ?_
  rintro Q ⟨hw, hd, hs⟩
  refine ⟨enh ∅ Q ((0 : Fin 2), []) ((1 : Fin 2), []), ⟨?_, ?_⟩, code_enh ∅ Q hd _ _⟩
  · rw [wf_enh ∅ hd, hw]
  · have := hsize_enh ∅ hd ((0 : Fin 2), []) ((1 : Fin 2), [])
    omega

/-- **The well-formed dominant couple codes of order `2n`** (the support of the sum in B2.1 item (4)). -/
noncomputable def domCodes (n : ℕ) : Finset RegCpl := (finite_domCodes n).toFinset

theorem mem_domCodes {n : ℕ} {Q : RegCpl} :
    Q ∈ domCodes n ↔ Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n := by
  simp [domCodes]

/-- The finite sum over `domCodes n` is B2's `∑ᶠ` over well-formed dominant codes of order `2n`. -/
theorem finsum_domCodes {M : Type*} [AddCommMonoid M] (n : ℕ) (f : RegCpl → M) :
    ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n), f Q =
      ∑ Q ∈ domCodes n, f Q := by
  rw [domCodes, ← finsum_mem_eq_finite_toFinset_sum]
  rfl

/-! ### Special subsets are bit vectors -/

/-- The elements of `l` whose bit in `bs` is set. -/
def zfrom {α : Type*} [DecidableEq α] (l : List α) (bs : List Bool) : Finset α :=
  (((l.zip bs).filter fun p => p.2).map Prod.fst).toFinset

theorem zfrom_subset {α : Type*} [DecidableEq α] (l : List α) (bs : List Bool) {z : α}
    (hz : z ∈ zfrom l bs) : z ∈ l := by
  simp only [zfrom, List.mem_toFinset, List.mem_map, List.mem_filter] at hz
  obtain ⟨⟨x, b⟩, ⟨hx, -⟩, rfl⟩ := hz
  exact List.of_mem_zip hx |>.1

theorem map_mem_zfrom {α : Type*} [DecidableEq α] : (l : List α) → l.Nodup → (bs : List Bool) →
    bs.length = l.length → l.map (fun z => decide (z ∈ zfrom l bs)) = bs
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | z :: l, hl, b :: bs, h => by
    rw [List.nodup_cons] at hl
    have hz' : z ∉ zfrom l bs := fun h' => hl.1 (zfrom_subset l bs h')
    have hset : zfrom (z :: l) (b :: bs) = if b then insert z (zfrom l bs) else zfrom l bs := by
      cases b <;> simp [zfrom, List.zip_cons_cons]
    have hrest : l.map (fun x => decide (x ∈ zfrom (z :: l) (b :: bs))) =
        l.map (fun x => decide (x ∈ zfrom l bs)) := by
      refine List.map_congr_left fun x hx => ?_
      have hxz : x ≠ z := fun e => hl.1 (e ▸ hx)
      rw [hset]
      cases b <;> simp [hxz]
    rw [List.map_cons, hrest, map_mem_zfrom l hl.2 bs (by simpa using h), hset]
    cases b <;> simp [hz']

/-! ### The bijection `(𝒬, Z) ↦ enh Z 𝒬` -/

/-- The roots of a couple: `+` tree `(0, [])`, `-` tree `(1, [])`. -/
abbrev rt₀ : Fin 2 × Path := (0, [])

/-- The root of the `-` tree. -/
abbrev rt₁ : Fin 2 × Path := (1, [])

theorem enh_inj {Q : RegCpl} (hQ : Q.dominant = true) {Z Z' : Finset (Fin 2 × Path)}
    (hZ : Z ∈ specialSets Q.links) (hZ' : Z' ∈ specialSets Q.links)
    (h : enh Z Q rt₀ rt₁ = enh Z' Q rt₀ rt₁) : Z = Z' := by
  have hb := congrArg ECpl.bits h
  rw [bits_enh Z Q hQ, bits_enh Z' Q hQ, List.map_inj_left] at hb
  rw [mem_specialSets_iff] at hZ hZ'
  ext z
  constructor
  · intro hz
    exact (decide_eq_decide.mp (hb z (hZ z hz))).mp hz
  · intro hz
    exact (decide_eq_decide.mp (hb z (hZ' z hz))).mpr hz

theorem exists_enh_eq {Q : RegCpl} (hQ : Q.dominant = true) {e : ECpl} (he : e.code = Q) :
    ∃ Z ∈ specialSets Q.links, enh Z Q rt₀ rt₁ = e := by
  set l := cplSpecial Q rt₀ rt₁ with hl
  have hlen : e.bits.length = l.length := by
    have h1 := ECpl.length_bits_eq e (enh ∅ Q rt₀ rt₁) (by rw [he, code_enh ∅ Q hQ])
    rw [h1, bits_enh ∅ Q hQ, List.length_map]
  refine ⟨zfrom l e.bits, ?_, ?_⟩
  · rw [mem_specialSets_iff]
    exact fun z hz => zfrom_subset l e.bits hz
  · refine ECpl.ext_code_bits _ _ (by rw [code_enh _ Q hQ, he]) ?_
    rw [bits_enh _ Q hQ]
    exact map_mem_zfrom l (specialList_nodup Q) e.bits hlen

/-- **Summing over dominant codes and their special subsets is summing over enhanced codes.** -/
theorem sum_domCodes_specialSets {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ECpl → M) :
    ∑ Q ∈ domCodes n, ∑ Z ∈ specialSets Q.links, f (enh Z Q rt₀ rt₁) = ∑ e ∈ ED n, f e := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => enh p.2 p.1 rt₀ rt₁) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨Q, Z⟩ hp
    rw [Finset.mem_sigma, mem_domCodes] at hp
    obtain ⟨⟨hw, hd, hs⟩, -⟩ := hp
    dsimp only at hw hd hs ⊢
    rw [mem_ED]
    refine ⟨by rw [wf_enh Z hd, hw], ?_⟩
    show (enh Z Q rt₀ rt₁).hsize = n
    have := hsize_enh Z hd rt₀ rt₁
    omega
  · rintro ⟨Q, Z⟩ hp ⟨Q', Z'⟩ hp' h
    rw [Finset.mem_sigma, mem_domCodes] at hp hp'
    have hQ : Q = Q' := by
      have := congrArg ECpl.code h
      simp only at this
      rwa [code_enh Z Q hp.1.2.1, code_enh Z' Q' hp'.1.2.1] at this
    subst hQ
    have := enh_inj hp.1.2.1 hp.2 hp'.2 h
    subst this
    rfl
  · intro e he
    rw [mem_ED] at he
    obtain ⟨Z, hZ, hZe⟩ := exists_enh_eq e.dominant_code rfl
    refine ⟨⟨e.code, Z⟩, ?_, hZe⟩
    rw [Finset.mem_sigma, mem_domCodes]
    refine ⟨⟨by rw [ECpl.wf_code, he.1], e.dominant_code, by rw [ECpl.size_code, he.2]⟩, hZ⟩

/-! ### The special weight and the leading term -/

theorem prod_eq_list_prod {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) {Z : Finset α}
    (hZ : ∀ z ∈ Z, z ∈ l) (f : α → ℂ) :
    ∏ z ∈ Z, f z = (l.map fun z => if z ∈ Z then f z else 1).prod := by
  rw [← List.prod_toFinset _ hl, Finset.prod_ite_mem]
  congr 1
  ext z
  simp only [Finset.mem_inter, List.mem_toFinset]
  exact ⟨fun h => ⟨hZ z h, h⟩, fun h => h.2⟩

/-- **B2's `specialWeight` (F61) is the special weight of the enhanced code.** -/
theorem specialWeight_eq_sw {Q : RegCpl} (hQ : Q.dominant = true) {Z : Finset (Fin 2 × Path)}
    (hZ : Z ∈ specialSets Q.links) : specialWeight ![1, -1] Z = (enh Z Q rt₀ rt₁).sw := by
  rw [sw_enh ![1, -1] Z Q hQ rt₀ rt₁ (by simp [nodeSign, pathSign]) (by simp [nodeSign, pathSign])]
  rw [mem_specialSets_iff] at hZ
  exact prod_eq_list_prod (specialList_nodup Q) hZ _

end WaveTurbulence.Mexp
