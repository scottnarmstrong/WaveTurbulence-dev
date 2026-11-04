/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainOne

/-!
# A chain with a bottom coefficient: the expansion (maincoef3)

DH21 Proposition 5.1, Case 2 (L1121–L1150, (newexp4)). If the pair coefficients and the bottom
coefficient have the expansion (maincoef3) (`MCExp`), so does
`(t, s) ↦ chainT c F α t (G α · s)` (`MCExp.chain`): expand the masks of the pairs
(`chainT_expand`) and of the bottom (`chainT_finsum`), apply the fixed-mask theorem
`MCRep.chainOne`, and regroup the terms by their final set `Z = Z_pairs ∪ Z_b ∪ σ(Y')`
(`MCExp.of_sum`). For a fixed `Z` at most `2^{m+1}` terms remain, so the constant gains a factor
`2^{m+1}` only.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Congr

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

/-- `chainT` only sees the pair coefficients of its own pairs, on the unit square. -/
theorem chainT_congr' (c : LegalCode) (q : ℕ) {F F' : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} (α : V → ℝ)
    (hF : ∀ j ∈ Set.Ico q (q + c.size), ∀ t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      F j α t s = F' j α t s)
    {g g' : ℝ → ℂ} (hg : ∀ s ∈ Icc (0 : ℝ) 1, g s = g' s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chainT σ ε c q F α t g = chainT σ ε c q F' α t g' := by
  classical
  set F3 : ℕ → (V → ℝ) → ℝ → ℝ → ℂ := fun j => if j ∈ Set.Ico q (q + c.size) then F' j else F j
    with hF3
  rw [chainT_congr c q (F' := F3) α (fun j t s ht hs => ?_) hg t ht]
  · exact chainT_congr_range c q α (fun j hj => by simp only [hF3, hj, ↓reduceIte]) t g'
  · by_cases hj : j ∈ Set.Ico q (q + c.size)
    · simp only [hF3, hj, ↓reduceIte]
      exact hF j hj t s ht hs
    · simp only [hF3, hj, ↓reduceIte]

end Congr

section Regroup

variable {V : Type} [DecidableEq V] {θ a b A : ℝ}

/-- **Regrouping terms by their set `Z`** (DH21 (maincoef3)): if
`F = Σ_{k ∈ K} ∏_{z ∈ Z_k} Φ(ζ_z α_z) T_k` with `T_k` a coefficient representation in `S ∖ Z_k`,
and at most `n_Z` terms have `Z_k = Z` with `n_Z N₀ ≤ N`, then `F` has the expansion. -/
theorem MCExp.of_sum {ζ : V → ℤ} {S : Finset V} {κ : Type*} (K : Finset κ)
    (Zof : κ → Finset V) (hZ : ∀ k ∈ K, Zof k ⊆ S) {T : κ → (V → ℝ) → ℝ → ℝ → ℂ} {N₀ N : ℝ}
    (hT : ∀ k ∈ K, MCRep θ a b A N₀ (↑(S \ Zof k)) (T k))
    (hcount : ∀ Z, ((K.filter fun k => Zof k = Z).card : ℝ) * N₀ ≤ N) (hθ : 0 ≤ θ)
    (hA : 0 ≤ A) {F : (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      F α t s = ∑ k ∈ K, (∏ z ∈ Zof k, PhiZ ζ z (α z)) * T k α t s) :
    MCExp θ a b A N ζ S F := by
  classical
  refine ⟨fun Z α t s => ∑ k ∈ K.filter fun k => Zof k = Z, T k α t s, fun Z hZS => ?_,
    fun α t s ht hs => ?_⟩
  · have h := MCRep.finsum (K.filter fun k => Zof k = Z) (N := fun _ => N₀)
      (S := ↑(S \ Z)) (fun k hk => by
        rw [Finset.mem_filter] at hk
        rw [← hk.2]
        exact hT k hk.1) hθ hA
      ⟨↥(S \ Z), inferInstance, Subtype.val, Subtype.val_injective, by ext; simp⟩
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h.mono (hcount Z) hA
  · rw [hF α t s ht hs]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Zof) (t := S.powerset)
      fun k hk => Finset.mem_powerset.2 (hZ k hk)]
    refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]

end Regroup

section Vars

variable {V : Type} [DecidableEq V] {σ : ℕ → V} {S : ℕ → Finset V} {Sb : Finset V} {m : ℕ}

theorem mem_unionS_zero {v : V} : v ∈ unionS S 0 m ↔ ∃ j ∈ Set.Ico 0 m, v ∈ S j := by
  simp [unionS, Finset.mem_biUnion]

/-- **The variables of a regrouped chain term.** -/
theorem chainVars_eq (hSb : ∀ j ∈ Set.Ico 0 m, Disjoint (S j) Sb)
    (hσS : ∀ j ∈ Set.Ico 0 m, ∀ k ∈ Set.Ico 0 m, σ k ∉ S j)
    (hσb : ∀ k ∈ Set.Ico 0 m, σ k ∉ Sb) (hinj : Set.InjOn σ (Set.Ico 0 m))
    {Zp Zb : Finset V} {Y' : Finset ℕ} (hZp : Zp ⊆ unionS S 0 m) (hZb : Zb ⊆ Sb)
    (hY' : Y' ⊆ Finset.Ico 0 m) :
    (⋃ j ∈ Set.Ico 0 m, (↑(S j \ (Zp ∩ S j)) : Set V)) ∪ ↑(Sb \ (Zb ∩ Sb)) ∪
        σ '' (Set.Ico 0 m \ ↑Y') =
      ↑((unionS S 0 m ∪ Sb ∪ (Finset.Ico 0 m).image σ) \ (Zp ∪ Zb ∪ Y'.image σ)) := by
  have hY'I : ∀ k ∈ Y', k ∈ Set.Ico 0 m := fun k hk => by
    have := hY' hk; simpa [Finset.mem_Ico] using this
  have hZpU : ∀ v ∈ Zp, ∃ j ∈ Set.Ico 0 m, v ∈ S j := fun v hv => mem_unionS_zero.1 (hZp hv)
  ext v
  simp only [Set.mem_union, Set.mem_iUnion, Finset.coe_sdiff, Finset.coe_inter, Set.mem_sdiff,
    Finset.mem_coe, Set.mem_inter_iff, Set.mem_image, Finset.coe_union, Finset.coe_image,
    exists_prop, not_and]
  constructor
  · rintro ((⟨j, hj, hvS, hvZ⟩ | ⟨hvb, hvZb⟩) | ⟨j, ⟨hj, hjY⟩, rfl⟩)
    · refine ⟨Or.inl (Or.inl (mem_unionS_zero.2 ⟨j, hj, hvS⟩)), ?_⟩
      rintro ((h | h) | ⟨k, hk, rfl⟩)
      · exact hvZ h hvS
      · exact Finset.disjoint_left.1 (hSb j hj) hvS (hZb h)
      · exact hσS j hj k (hY'I k hk) hvS
    · refine ⟨Or.inl (Or.inr hvb), ?_⟩
      rintro ((h | h) | ⟨k, hk, rfl⟩)
      · obtain ⟨j, hj, hvS⟩ := hZpU v h
        exact Finset.disjoint_left.1 (hSb j hj) hvS hvb
      · exact hvZb h hvb
      · exact hσb k (hY'I k hk) hvb
    · refine ⟨Or.inr ⟨j, by simpa [Finset.mem_Ico] using hj, rfl⟩, ?_⟩
      rintro ((h | h) | ⟨k, hk, hkj⟩)
      · obtain ⟨i, hi, hvS⟩ := hZpU _ h
        exact hσS i hi j hj hvS
      · exact hσb j hj (hZb h)
      · exact hjY (hinj (hY'I k hk) hj hkj ▸ hk)
  · rintro ⟨(hv | hv) | ⟨j, hj, rfl⟩, hnot⟩
    · obtain ⟨j, hj, hvS⟩ := mem_unionS_zero.1 hv
      exact Or.inl (Or.inl ⟨j, hj, hvS, fun h _ => hnot (Or.inl (Or.inl h))⟩)
    · exact Or.inl (Or.inr ⟨hv, fun h _ => hnot (Or.inl (Or.inr h))⟩)
    · refine Or.inr ⟨j, ⟨by simpa [Finset.mem_Ico] using hj, fun h => hnot (Or.inr ⟨j, h, rfl⟩)⟩,
        rfl⟩

end Vars

section Count

variable {V : Type} [DecidableEq V] {σ : ℕ → V} {S : ℕ → Finset V} {Sb : Finset V} {m : ℕ}

/-- The masks of a regrouped term are determined by its set `Z`. -/
theorem chainMasks_eq (hSb : ∀ j ∈ Set.Ico 0 m, Disjoint (S j) Sb)
    (hσS : ∀ j ∈ Set.Ico 0 m, ∀ k ∈ Set.Ico 0 m, σ k ∉ S j)
    (hσb : ∀ k ∈ Set.Ico 0 m, σ k ∉ Sb) (hinj : Set.InjOn σ (Set.Ico 0 m))
    {Zp Zb : Finset V} {Y' : Finset ℕ} (hZp : Zp ⊆ unionS S 0 m) (hZb : Zb ⊆ Sb)
    (hY' : Y' ⊆ Finset.Ico 0 m) :
    (Zp ∪ Zb ∪ Y'.image σ) ∩ unionS S 0 m = Zp ∧ (Zp ∪ Zb ∪ Y'.image σ) ∩ Sb = Zb ∧
      (Finset.Ico 0 m).filter (fun j => σ j ∈ Zp ∪ Zb ∪ Y'.image σ) = Y' := by
  have hY'I : ∀ k ∈ Y', k ∈ Set.Ico 0 m := fun k hk => by
    have := hY' hk; simpa [Finset.mem_Ico] using this
  have hUb : ∀ v ∈ unionS S 0 m, v ∉ Sb := fun v hv hb => by
    obtain ⟨j, hj, hvS⟩ := mem_unionS_zero.1 hv
    exact Finset.disjoint_left.1 (hSb j hj) hvS hb
  have hσU : ∀ k ∈ Set.Ico 0 m, σ k ∉ unionS S 0 m := fun k hk hv => by
    obtain ⟨j, hj, hvS⟩ := mem_unionS_zero.1 hv
    exact hσS j hj k hk hvS
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨(h | h) | ⟨k, hk, rfl⟩, hv⟩
      · exact h
      · exact absurd (hZb h) (hUb v hv)
      · exact absurd hv (hσU k (hY'I k hk))
    · intro h
      exact ⟨Or.inl (Or.inl h), hZp h⟩
  · ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨(h | h) | ⟨k, hk, rfl⟩, hv⟩
      · exact absurd hv (hUb v (hZp h))
      · exact h
      · exact absurd hv (hσb k (hY'I k hk))
    · intro h
      exact ⟨Or.inl (Or.inr h), hZb h⟩
  · ext j
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hj, (h | h) | ⟨k, hk, hkj⟩⟩
      · exact absurd (hZp h) (hσU j (by simpa [Finset.mem_Ico] using hj))
      · exact absurd (hZb h) (hσb j (by simpa [Finset.mem_Ico] using hj))
      · rwa [← hinj (hY'I k hk) (by simpa [Finset.mem_Ico] using hj) hkj]
    · intro h
      exact ⟨hY' h, Or.inr ⟨j, h, rfl⟩⟩

end Count

section Chain

variable {V : Type} [DecidableEq V]

theorem Nchain_nonneg {θ a b : ℝ} {c : LegalCode} {N : ℕ → ℝ} {Nb : ℝ}
    (hN : ∀ j ∈ Set.Ico 0 c.size, 0 ≤ N j) (hNb : 0 ≤ Nb) : 0 ≤ Nchain θ a b c N Nb := by
  have hK := KH_nonneg θ a b
  have hC : 0 ≤ C510 θ ^ c.size := by unfold C510; positivity
  have hT := NT_nonneg (NP := fun j => (1 + KPD a b) * N j) c 0 fun j hj =>
    mul_nonneg (by linarith [KPD_nonneg a b]) (hN j (by simpa using hj))
  unfold Nchain
  positivity

/-- The index set of the terms of `MCExp.chain`. -/
abbrev ChainIdx : Type := Finset V × Finset V × (Σ _ : Finset ℕ, Finset ℕ) × Bool

/-- **A chain with a bottom coefficient has the expansion (maincoef3)** (DH21 Proposition 5.1,
Case 2, L1121–L1150, (newexp4)). -/
theorem MCExp.chain {θ a b A : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A)
    {σ : ℕ → V} {ε : ℕ → ℤ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) {ζ : V → ℤ} {c : LegalCode}
    (hζ : ∀ j ∈ Set.Ico 0 c.size, ζ (σ j) = ε j) (hc : c ≠ .nil)
    (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {S : ℕ → Finset V} {N : ℕ → ℝ} {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : ∀ j ∈ Set.Ico 0 c.size, MCExp θ a b A (N j) ζ (S j) (F j))
    {Sb : Finset V} {Nb : ℝ} {G : (V → ℝ) → ℝ → ℝ → ℂ} (hG : MCExp θ a b A Nb ζ Sb G)
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    (hSb : ∀ j ∈ Set.Ico 0 c.size, Disjoint (S j) Sb)
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j)
    (hσb : ∀ k ∈ Set.Ico 0 c.size, σ k ∉ Sb) :
    MCExp θ a b A (2 ^ (c.size + 1) * Nchain θ a b c N Nb) ζ
      (unionS S 0 c.size ∪ Sb ∪ (Finset.Ico 0 c.size).image σ)
      (fun α t s => chainT σ ε c 0 F α t (fun t' => G α t' s)) := by
  classical
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  -- the expansions of the pairs and of the bottom
  have hFex : ∀ j, ∃ Gj : Finset V → (V → ℝ) → ℝ → ℝ → ℂ, j ∈ Set.Ico 0 c.size →
      (∀ Z ⊆ S j, MCRep θ a b A (N j) (↑(S j \ Z)) (Gj Z)) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        F j α t s = ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, PhiZ ζ z (α z)) * Gj Z α t s := by
    intro j
    by_cases hj : j ∈ Set.Ico 0 c.size
    · obtain ⟨Gj, h1, h2⟩ := hF j hj
      exact ⟨Gj, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ _ _ => 0, fun h => absurd h hj⟩
  choose Gp hGp using hFex
  obtain ⟨Gb, hGb, hGbe⟩ := hG
  have hN : ∀ j ∈ Set.Ico 0 c.size, 0 ≤ N j := fun j hj =>
    ((hGp j hj).1 ∅ (Finset.empty_subset _)).nonneg
  have hNb : 0 ≤ Nb := (hGb ∅ (Finset.empty_subset _)).nonneg
  -- the fixed-mask theorem for every pair of masks
  have hT1 : ∀ p : Finset V × Finset V,
      ∃ T : Finset ℕ → Finset ℕ → Bool → (V → ℝ) → ℝ → ℝ → ℂ,
        (∀ Y ⊆ adjSet c 0, ∀ Y' ⊆ Y, ∀ pc, MCRep θ a b A (Nchain θ a b c N Nb)
          ((⋃ j ∈ Set.Ico 0 c.size, (↑(S j \ (p.1 ∩ S j)) : Set V)) ∪ ↑(Sb \ (p.2 ∩ Sb)) ∪
            σ '' (Set.Ico 0 c.size \ ↑Y')) (T Y Y' pc)) ∧
        ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
          chainT σ ε c 0 (fun j => Gp j (p.1 ∩ S j)) α t (fun t' => Gb (p.2 ∩ Sb) α t' s) =
            ∑ Y ∈ (adjSet c 0).powerset, ∑ Y' ∈ Y.powerset,
              (∏ j ∈ Y', PhiZ ζ (σ j) (α (σ j))) * (T Y Y' true α t s + T Y Y' false α t s) :=
    fun p => MCRep.chainOne hθ0 hθ1 ha hb hab1 hab hA hε hζ hc hinj
      (S := fun j => ↑(S j \ (p.1 ∩ S j))) (N := N) (R := fun j => Gp j (p.1 ∩ S j))
      (fun j hj => (hGp j hj).1 _ Finset.inter_subset_right) (hGb _ Finset.inter_subset_right)
      (fun j hj k hk hjk => Finset.disjoint_coe.2
        ((hSS j hj k hk hjk).mono Finset.sdiff_subset Finset.sdiff_subset))
      (fun j hj => Finset.disjoint_coe.2 ((hSb j hj).mono Finset.sdiff_subset
        Finset.sdiff_subset))
      (fun j hj k hk h => hσS j hj k hk (Finset.mem_sdiff.1 (Finset.mem_coe.1 h)).1)
      (fun k hk h => hσb k hk (Finset.mem_sdiff.1 (Finset.mem_coe.1 h)).1)
  choose T hTr hTe using hT1
  -- the index set
  set U := unionS S 0 c.size with hU
  set K : Finset (ChainIdx (V := V)) := U.powerset ×ˢ (Sb.powerset ×ˢ
    (((adjSet c 0).powerset.sigma fun Y => Y.powerset) ×ˢ (Finset.univ : Finset Bool)))
    with hK
  have hmemK : ∀ k : ChainIdx (V := V), k ∈ K ↔ k.1 ⊆ U ∧ k.2.1 ⊆ Sb ∧
      k.2.2.1.1 ⊆ adjSet c 0 ∧ k.2.2.1.2 ⊆ k.2.2.1.1 := by
    intro k
    simp [hK, Finset.mem_product, Finset.mem_sigma]
  have hadjI : ∀ {Y : Finset ℕ}, Y ⊆ adjSet c 0 → Y ⊆ Finset.Ico 0 c.size := fun hY j hj => by
    have := mem_adjSet c 0 j (hY hj)
    simp only [Finset.mem_Ico]; omega
  refine MCExp.of_sum K (fun k => k.1 ∪ k.2.1 ∪ k.2.2.1.2.image σ)
    (T := fun k => T (k.1, k.2.1) k.2.2.1.1 k.2.2.1.2 k.2.2.2) (N₀ := Nchain θ a b c N Nb)
    ?_ ?_ ?_ hθ0 hA0 ?_
  · -- the sets are subsets
    intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := (hmemK k).1 hk
    refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
    · exact h1.trans (Finset.subset_union_left.trans Finset.subset_union_left)
    · exact h2.trans (Finset.subset_union_right.trans Finset.subset_union_left)
    · exact (Finset.image_subset_image (h4.trans (hadjI h3))).trans Finset.subset_union_right
  · -- the terms
    intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := (hmemK k).1 hk
    have h := hTr (k.1, k.2.1) k.2.2.1.1 h3 k.2.2.1.2 h4 k.2.2.2
    rw [chainVars_eq hSb hσS hσb hinj h1 h2 (h4.trans (hadjI h3))] at h
    exact h
  · -- the count
    intro Z
    have hcard : (K.filter fun k => k.1 ∪ k.2.1 ∪ k.2.2.1.2.image σ = Z).card ≤
        ((adjSet c 0).powerset ×ˢ (Finset.univ : Finset Bool)).card := by
      refine Finset.card_le_card_of_injOn (fun k => (k.2.2.1.1, k.2.2.2)) (fun k hk => ?_)
        (fun k hk k' hk' hkk' => ?_)
      · obtain ⟨hk, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
        obtain ⟨-, -, h3, -⟩ := (hmemK k).1 hk
        simp [h3]
      · obtain ⟨hkK, hkZ⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
        obtain ⟨hkK', hkZ'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk')
        obtain ⟨a1, a2, a3, a4⟩ := (hmemK k).1 hkK
        obtain ⟨b1, b2, b3, b4⟩ := (hmemK k').1 hkK'
        obtain ⟨e1, e2, e3⟩ := chainMasks_eq hSb hσS hσb hinj a1 a2 (a4.trans (hadjI a3))
        obtain ⟨f1, f2, f3⟩ := chainMasks_eq hSb hσS hσb hinj b1 b2 (b4.trans (hadjI b3))
        rw [hkZ] at e1 e2 e3
        rw [hkZ'] at f1 f2 f3
        simp only [Prod.mk.injEq] at hkk'
        obtain ⟨k1, k2, ⟨Y, Y'⟩, k4⟩ := k
        obtain ⟨l1, l2, ⟨L, L'⟩, l4⟩ := k'
        simp only at e1 e2 e3 f1 f2 f3 hkk'
        obtain ⟨rfl, rfl⟩ := hkk'
        rw [← e1, ← e2, ← e3, f1, f2, f3]
    have hpow : ((adjSet c 0).powerset ×ˢ (Finset.univ : Finset Bool)).card ≤ 2 ^ (c.size + 1) := by
      rw [Finset.card_product, Finset.card_powerset, Finset.card_univ, Fintype.card_bool,
        pow_succ]
      exact Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by norm_num) (card_adjSet_le c 0))
    have hNc := Nchain_nonneg (θ := θ) (a := a) (b := b) hN hNb
    calc ((K.filter fun k => k.1 ∪ k.2.1 ∪ k.2.2.1.2.image σ = Z).card : ℝ) *
          Nchain θ a b c N Nb ≤ ((2 ^ (c.size + 1) : ℕ) : ℝ) * Nchain θ a b c N Nb :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard.trans hpow) hNc
      _ = 2 ^ (c.size + 1) * Nchain θ a b c N Nb := by push_cast; ring
  · -- the identity
    intro α t s ht hs
    set w : V → ℂ := fun z => PhiZ ζ z (α z) with hw
    -- continuous representatives at `α`
    have hRc : ∀ (j : ℕ) (Z : Finset V), ∃ Rj : ℝ → ℝ → ℂ,
        Continuous (fun p : ℝ × ℝ => Rj p.1 p.2) ∧ (j ∈ Set.Ico 0 c.size → Z ⊆ S j →
          ∀ t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → Gp j Z α t s = Rj t s) := by
      intro j Z
      by_cases h : j ∈ Set.Ico 0 c.size ∧ Z ⊆ S j
      · obtain ⟨Rj, hcj, hej⟩ := ((hGp j h.1).1 Z h.2).exists_continuous α
        exact ⟨Rj, hcj, fun _ _ => hej⟩
      · exact ⟨fun _ _ => 0, continuous_const, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
    choose Rc hRcc hRce using hRc
    have hRb : ∀ Zb : Finset V, ∃ Rj : ℝ → ℝ → ℂ,
        Continuous (fun p : ℝ × ℝ => Rj p.1 p.2) ∧ (Zb ⊆ Sb →
          ∀ t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → Gb Zb α t s = Rj t s) := by
      intro Zb
      by_cases h : Zb ⊆ Sb
      · obtain ⟨Rj, hcj, hej⟩ := (hGb Zb h).exists_continuous α
        exact ⟨Rj, hcj, fun _ => hej⟩
      · exact ⟨fun _ _ => 0, continuous_const, fun h1 => absurd h1 h⟩
    choose Rb hRbc hRbe using hRb
    have hRbs : ∀ Zb, Continuous fun t' => Rb Zb t' s := fun Zb =>
      (hRbc Zb).comp (continuous_id.prodMk continuous_const)
    -- step 1: the continuous representatives
    have h1 : chainT σ ε c 0 F α t (fun t' => G α t' s) =
        chainT σ ε c 0 (fun j (_ : V → ℝ) t s => ∑ Z ∈ (S j).powerset,
          (∏ z ∈ Z, w z) * Rc j Z t s) α t
          (fun t' => ∑ Zb ∈ Sb.powerset, (∏ z ∈ Zb, w z) * Rb Zb t' s) := by
      refine chainT_congr' c 0 α (fun j hj t s ht hs => ?_) (fun t' ht' => ?_) ht
      · have hj' : j ∈ Set.Ico 0 c.size := by simpa using hj
        rw [(hGp j hj').2 α t s ht hs]
        exact Finset.sum_congr rfl fun Z hZ => by
          rw [hRce j Z hj' (Finset.mem_powerset.1 hZ) t s ht hs]
      · rw [hGbe α t' s ht' hs]
        exact Finset.sum_congr rfl fun Zb hZb => by
          rw [hRbe Zb (Finset.mem_powerset.1 hZb) t' s ht' hs]
    have hgc : Continuous fun t' => ∑ Zb ∈ Sb.powerset, (∏ z ∈ Zb, w z) * Rb Zb t' s :=
      continuous_finsetSum _ fun Zb _ => continuous_const.mul (hRbs Zb)
    -- step 2: the pair masks
    have h2 := chainT_expand (σ := σ) (ε := ε) α w (S := S)
      (R := fun j Z (_ : V → ℝ) t s => Rc j Z t s) (fun j Z => hRcc j Z) c 0
      (fun j hj k hk hjk => hSS j (by simpa using hj) k (by simpa using hk) hjk) hgc t
    -- step 3: the bottom masks
    have h3 : ∀ Zp : Finset V, chainT σ ε c 0 (fun j (_ : V → ℝ) t s => Rc j (Zp ∩ S j) t s) α t
        (fun t' => ∑ Zb ∈ Sb.powerset, (∏ z ∈ Zb, w z) * Rb Zb t' s) =
        ∑ Zb ∈ Sb.powerset, (∏ z ∈ Zb, w z) *
          chainT σ ε c 0 (fun j (_ : V → ℝ) t s => Rc j (Zp ∩ S j) t s) α t
            (fun t' => Rb Zb t' s) := fun Zp =>
      chainT_finsum c 0 α (fun j => hRcc j (Zp ∩ S j)) Sb.powerset (fun Zb => ∏ z ∈ Zb, w z)
        (h := fun Zb t' => Rb Zb t' s) hRbs t
    -- step 4: back to the coefficients
    have h4 : ∀ Zp, ∀ Zb ∈ Sb.powerset,
        chainT σ ε c 0 (fun j (_ : V → ℝ) t s => Rc j (Zp ∩ S j) t s) α t
          (fun t' => Rb Zb t' s) =
        chainT σ ε c 0 (fun j => Gp j (Zp ∩ S j)) α t (fun t' => Gb (Zb ∩ Sb) α t' s) := by
      intro Zp Zb hZb
      have hZb' := Finset.mem_powerset.1 hZb
      refine chainT_congr' c 0 α (fun j hj t s ht hs => (hRce j _ (by simpa using hj)
        Finset.inter_subset_right t s ht hs).symm) (fun t' ht' => ?_) ht
      rw [Finset.inter_eq_left.2 hZb']
      exact (hRbe Zb hZb' t' s ht' hs).symm
    -- step 5: assemble
    have hprod : ∀ k ∈ K, ∏ z ∈ k.1 ∪ k.2.1 ∪ k.2.2.1.2.image σ, w z =
        (∏ z ∈ k.1, w z) * (∏ z ∈ k.2.1, w z) * ∏ j ∈ k.2.2.1.2, w (σ j) := by
      intro k hk
      obtain ⟨k1, k2, k3, k4⟩ := (hmemK k).1 hk
      have hk4 := k4.trans (hadjI k3)
      have hY'I : ∀ j ∈ k.2.2.1.2, j ∈ Set.Ico 0 c.size := fun j hj => by
        have := hk4 hj; simpa [Finset.mem_Ico] using this
      obtain ⟨e1, e2, -⟩ := chainMasks_eq hSb hσS hσb hinj k1 k2 hk4
      have hd1 : Disjoint k.1 k.2.1 := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        obtain ⟨j, hj, hvS⟩ := mem_unionS_zero.1 (k1 hv1)
        exact Finset.disjoint_left.1 (hSb j hj) hvS (k2 hv2)
      have hd2 : Disjoint (k.1 ∪ k.2.1) (k.2.2.1.2.image σ) := by
        rw [Finset.disjoint_right]
        intro v hv hv'
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
        rcases Finset.mem_union.1 hv' with h | h
        · obtain ⟨i, hi, hvS⟩ := mem_unionS_zero.1 (k1 h)
          exact hσS i hi j (hY'I j hj) hvS
        · exact hσb j (hY'I j hj) (k2 h)
      rw [Finset.prod_union hd2, Finset.prod_union hd1,
        Finset.prod_image fun x hx y hy h => hinj (hY'I x hx) (hY'I y hy) h]
    show chainT σ ε c 0 F α t (fun t' => G α t' s) = _
    rw [h1, h2, hK, Finset.sum_product]
    refine Finset.sum_congr rfl fun Zp hZp => ?_
    rw [h3 Zp, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Zb hZb => ?_
    rw [h4 Zp Zb hZb]
    have e := hTe (Zp, Zb) α t s ht hs
    simp only at e
    rw [e, Finset.sum_product, Finset.sum_sigma]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y hY => Finset.sum_congr rfl fun Y' hY' => ?_
    have hmem : ∀ pc : Bool, ((Zp, Zb, ⟨Y, Y'⟩, pc) : ChainIdx (V := V)) ∈ K := fun pc =>
      (hmemK _).2 ⟨Finset.mem_powerset.1 hZp, Finset.mem_powerset.1 hZb,
        Finset.mem_powerset.1 hY, Finset.mem_powerset.1 hY'⟩
    rw [Fintype.sum_bool, hprod _ (hmem true)]
    simp only [hw]
    ring

end Chain

end WaveTurbulence.ClassJR
