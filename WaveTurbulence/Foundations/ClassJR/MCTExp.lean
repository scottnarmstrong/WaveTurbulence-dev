/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCTOne
public import WaveTurbulence.Foundations.ClassJR.MCChainExp

/-!
# A tree chain has the expansion (maincoef3) for `t > s` (DH21 Proposition 6.10)

DH21 Proposition 6.10 (L1705–L1708): the coefficient of a regular tree "has form (maincoef1) that
satisfies (maincoef2)–(maincoef2.5), for `t > s`", with the weights `(⟨λ₁⟩ + ⟨λ₂⟩)`. `MCExpT` is the
expansion (maincoef3) with the identity required for `0 ≤ s < t ≤ 1` only (the coefficients `G_Z` are
coefficient representations on `[0, 1]²`, with the DH23 weights `⟨max(λ₁,λ₂)⟩`).

`MCExpT.chain`: if the pair coefficients of a chain have the expansion (maincoef3) (`MCExp`) with the
exponents `(θ', a', b)`, the chain integral with the lone-leaf condition `1{t_{2m} > s}` as bottom has
`MCExpT` with the exponents `(θ, a, b)`. The proof rebases the chain at `s` (`chainT_rebase`), expands
the masks of the pairs (`chainT_expand`), applies the fixed-mask theorem `MCRep.treeOne` to the rebased
chain, rebases every term back (`MCRep.sub_time`), and regroups the terms by their set `Z`
(`MCExpT.of_sum`). The strict inequality `s < t` is used for the continuation `1{u > 0}` of the
rebased chain (`chainT_congr_pos`) and for the trivial tree.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Def

variable {V : Type} [DecidableEq V] {θ a b A : ℝ}

/-- **The expansion of DH21 (maincoef3) for `t > s`** (DH21 Proposition 6.10, L1705–L1708). -/
@[expose] def MCExpT (θ a b A N : ℝ) (ζ : V → ℤ) (S : Finset V) (F : (V → ℝ) → ℝ → ℝ → ℂ) :
    Prop :=
  ∃ G : Finset V → (V → ℝ) → ℝ → ℝ → ℂ,
    (∀ Z ⊆ S, MCRep θ a b A N (↑(S \ Z)) (G Z)) ∧
    ∀ α t s, 0 ≤ s → s < t → t ≤ 1 →
      F α t s = ∑ Z ∈ S.powerset, (∏ z ∈ Z, PhiZ ζ z (α z)) * G Z α t s

theorem MCExpT.mono {N N' : ℝ} {ζ : V → ℤ} {S : Finset V} {F : (V → ℝ) → ℝ → ℝ → ℂ}
    (h : MCExpT θ a b A N ζ S F) (hN : N ≤ N') (hA : 0 ≤ A) : MCExpT θ a b A N' ζ S F := by
  obtain ⟨G, hG, hF⟩ := h
  exact ⟨G, fun Z hZ => (hG Z hZ).mono hN hA, hF⟩

theorem MCExpT.congr {N : ℝ} {ζ : V → ℤ} {S : Finset V} {F F' : (V → ℝ) → ℝ → ℝ → ℂ}
    (h : MCExpT θ a b A N ζ S F)
    (he : ∀ α t s, 0 ≤ s → s < t → t ≤ 1 → F' α t s = F α t s) : MCExpT θ a b A N ζ S F' := by
  obtain ⟨G, hG, hF⟩ := h
  exact ⟨G, hG, fun α t s hs hst ht => (he α t s hs hst ht).trans (hF α t s hs hst ht)⟩

/-- An expansion on `[0, 1]²` is one for `t > s`. -/
theorem MCExp.toMCExpT {N : ℝ} {ζ : V → ℤ} {S : Finset V} {F : (V → ℝ) → ℝ → ℝ → ℂ}
    (h : MCExp θ a b A N ζ S F) : MCExpT θ a b A N ζ S F := by
  obtain ⟨G, hG, hF⟩ := h
  exact ⟨G, hG, fun α t s hs hst ht => hF α t s ⟨by linarith, ht⟩ ⟨hs, by linarith⟩⟩

/-- **Regrouping terms by their set `Z`**, for `t > s` (as `MCExp.of_sum`). -/
theorem MCExpT.of_sum {ζ : V → ℤ} {S : Finset V} {κ : Type*} (K : Finset κ)
    (Zof : κ → Finset V) (hZ : ∀ k ∈ K, Zof k ⊆ S) {T : κ → (V → ℝ) → ℝ → ℝ → ℂ} {N₀ N : ℝ}
    (hT : ∀ k ∈ K, MCRep θ a b A N₀ (↑(S \ Zof k)) (T k))
    (hcount : ∀ Z, ((K.filter fun k => Zof k = Z).card : ℝ) * N₀ ≤ N) (hθ : 0 ≤ θ)
    (hA : 0 ≤ A) {F : (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : ∀ α t s, 0 ≤ s → s < t → t ≤ 1 →
      F α t s = ∑ k ∈ K, (∏ z ∈ Zof k, PhiZ ζ z (α z)) * T k α t s) :
    MCExpT θ a b A N ζ S F := by
  classical
  refine ⟨fun Z α t s => ∑ k ∈ K.filter fun k => Zof k = Z, T k α t s, fun Z hZS => ?_,
    fun α t s hs hst ht => ?_⟩
  · have h := MCRep.finsum (K.filter fun k => Zof k = Z) (N := fun _ => N₀)
      (S := ↑(S \ Z)) (fun k hk => by
        rw [Finset.mem_filter] at hk
        rw [← hk.2]
        exact hT k hk.1) hθ hA
      ⟨↥(S \ Z), inferInstance, Subtype.val, Subtype.val_injective, by ext; simp⟩
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h.mono (hcount Z) hA
  · rw [hF α t s hs hst ht]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Zof) (t := S.powerset)
      fun k hk => Finset.mem_powerset.2 (hZ k hk)]
    refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]

end Def

section CongrPos

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

/-- At a positive time, `chainT` only sees the continuation at positive times. -/
theorem chainT_congr_pos : ∀ (c : LegalCode) (q : ℕ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (α : V → ℝ)
    {g g' : ℝ → ℂ} (_ : ∀ u, 0 < u → g u = g' u) {t : ℝ} (_ : 0 < t),
    chainT σ ε c q F α t g = chainT σ ε c q F α t g'
  | .nil, _, _, _, _, _, hg, t, ht => hg t ht
  | .node i r, q, F, α, g, g', hg, t, ht => by
    rw [chainT_node, chainT_node]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun ta hta => ?_)
    rw [Set.uIoc_of_le ht.le] at hta
    congr 1
    refine chainT_congr_pos i (q + 1) F α (fun t' ht' => ?_) hta.1
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun tb htb => ?_)
    rw [Set.uIoc_of_le ht'.le] at htb
    rw [chainT_congr_pos r _ F α hg htb.1]

end CongrPos

section Tree

variable {V : Type} [DecidableEq V]

/-- **A tree chain has the expansion (maincoef3) for `t > s`** (DH21 Proposition 6.10, with
Proposition 5.1, Case 2): for a chain whose pair coefficients have the expansion with the exponents
`(θ', a', b)`, the chain integral with the lone-leaf condition `1{t_{2m} > s}` has the expansion with
the exponents `(θ, a, b)`, for `t > s`. -/
theorem MCExpT.chain {θ a b A θ' a' δ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A) (ha' : 0 < a') (hab' : a' + b ≤ θ')
    (hθ'1 : θ' ≤ 1) (hδ : 0 < δ) (hδθ : δ + θ ≤ θ') (hδa : δ + a ≤ a') (hδb : δ + b ≤ 1)
    {σ : ℕ → V} {ε : ℕ → ℤ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) {ζ : V → ℤ} {c : LegalCode}
    (hζ : ∀ j ∈ Set.Ico 0 c.size, ζ (σ j) = ε j) (hc : c ≠ .nil)
    (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {S : ℕ → Finset V} {N : ℕ → ℝ} {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : ∀ j ∈ Set.Ico 0 c.size, MCExp θ' a' b A (N j) ζ (S j) (F j))
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j) :
    MCExpT θ a b A (2 ^ (c.size + 1) * (2 * Ntree θ a b a' δ c N (N1 θ))) ζ
      (unionS S 0 c.size ∪ (Finset.Ico 0 c.size).image σ)
      (fun α t s => chainT σ ε c 0 F α t (fun t' => if s < t' then 1 else 0)) := by
  classical
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  -- the expansions of the pairs
  have hFex : ∀ j, ∃ Gj : Finset V → (V → ℝ) → ℝ → ℝ → ℂ, j ∈ Set.Ico 0 c.size →
      (∀ Z ⊆ S j, MCRep θ' a' b A (N j) (↑(S j \ Z)) (Gj Z)) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        F j α t s = ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, PhiZ ζ z (α z)) * Gj Z α t s := by
    intro j
    by_cases hj : j ∈ Set.Ico 0 c.size
    · obtain ⟨Gj, h1, h2⟩ := hF j hj
      exact ⟨Gj, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ _ _ => 0, fun h => absurd h hj⟩
  choose Gp hGp using hFex
  have hN : ∀ j ∈ Set.Ico 0 c.size, 0 ≤ N j := fun j hj =>
    ((hGp j hj).1 ∅ (Finset.empty_subset _)).nonneg
  -- the symbols of the pair masks
  have hPex : ∀ (j : ℕ) (Z : Finset V), ∃ Pj : PSym V, SymReg Pj.C ∧
      (j ∈ Set.Ico 0 c.size → Z ⊆ S j →
        (Function.Injective Pj.f ∧ Set.range Pj.f = ↑(S j \ Z) ∧ SRep θ' a' b A (N j) Pj.C) ∧
        ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
          Gp j Z α t s = ∫ lam, Pj.C (α ∘ Pj.f) lam * e2 lam t s) := by
    intro j Z
    by_cases h : j ∈ Set.Ico 0 c.size ∧ Z ⊆ S j
    · obtain ⟨ι, hι, f, C, hf, hr, hS, he⟩ := ((hGp j h.1).1 Z h.2).exists_srep
      exact ⟨⟨ι, f, C⟩, hS.reg, fun _ _ => ⟨⟨hf, hr, hS⟩, he⟩⟩
    · exact ⟨⟨Empty, fun e => Empty.elim e, fun _ _ => 0⟩, symReg_zero,
        fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose P hPreg hP using hPex
  -- the fixed-mask theorem for every mask of the pairs
  have hT1 : ∀ Zp : Finset V, ∃ T : Finset ℕ → Finset ℕ → Bool → (V → ℝ) → ℝ → ℝ → ℂ,
      (∀ Y ⊆ adjSet c 0, ∀ Y' ⊆ Y, ∀ pc, MCRep θ a b A (Ntree θ a b a' δ c N (N1 θ))
        ((⋃ j ∈ Set.Ico 0 c.size, (↑(S j \ (Zp ∩ S j)) : Set V)) ∪ ∅ ∪
          σ '' (Set.Ico 0 c.size \ ↑Y')) (T Y Y' pc)) ∧
      ∀ α τ s, τ ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        chainT σ ε c 0 (fun j β u v => ∫ lam, (P j (Zp ∩ S j)).C (β ∘ (P j (Zp ∩ S j)).f) lam *
          e2 lam (u + s) (v + s)) α τ (fun _ => 1) =
          ∑ Y ∈ (adjSet c 0).powerset, ∑ Y' ∈ Y.powerset,
            (∏ j ∈ Y', PhiZ ζ (σ j) (α (σ j))) * (T Y Y' true α τ s + T Y Y' false α τ s) :=
    fun Zp => MCRep.treeOne hθ0 hθ1 ha hb hab1 hab hA ha' hab' hθ'1 hδ hδθ hδa hδb hε hζ hc hinj
      (S := fun j => ↑(S j \ (Zp ∩ S j))) (N := N) (P := fun j => P j (Zp ∩ S j))
      (fun j => hPreg j _) (fun j hj => (hP j _ hj Finset.inter_subset_right).1)
      (fun j hj k hk hjk => Finset.disjoint_coe.2
        ((hSS j hj k hk hjk).mono Finset.sdiff_subset Finset.sdiff_subset))
      (fun j hj k hk h => hσS j hj k hk (Finset.mem_sdiff.1 (Finset.mem_coe.1 h)).1)
  choose T hTr hTe using hT1
  -- every term rebased back to `(t, s)`
  have hT2 : ∀ (Zp : Finset V) (Y Y' : Finset ℕ) (pc : Bool), ∃ T' : (V → ℝ) → ℝ → ℝ → ℂ,
      (Y ⊆ adjSet c 0 → Y' ⊆ Y → MCRep θ a b A (2 * Ntree θ a b a' δ c N (N1 θ))
        ((⋃ j ∈ Set.Ico 0 c.size, (↑(S j \ (Zp ∩ S j)) : Set V)) ∪ ∅ ∪
          σ '' (Set.Ico 0 c.size \ ↑Y')) T') ∧
      (Y ⊆ adjSet c 0 → Y' ⊆ Y → ∀ α t s, 0 ≤ s → s ≤ t → t ≤ 1 →
        T' α t s = T Zp Y Y' pc α (t - s) s) := by
    intro Zp Y Y' pc
    by_cases h : Y ⊆ adjSet c 0 ∧ Y' ⊆ Y
    · obtain ⟨T', h1, h2⟩ := (hTr Zp Y h.1 Y' h.2 pc).sub_time hθ0 hθ1.le ha.le (by linarith)
      exact ⟨T', fun _ _ => h1, fun _ _ => h2⟩
    · exact ⟨fun _ _ _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ h, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose T' hT'r hT'e using hT2
  -- the index set
  set U := unionS S 0 c.size with hU
  set K : Finset (Finset V × (Σ _ : Finset ℕ, Finset ℕ) × Bool) :=
    U.powerset ×ˢ (((adjSet c 0).powerset.sigma fun Y => Y.powerset) ×ˢ
      (Finset.univ : Finset Bool)) with hK
  have hmemK : ∀ k : Finset V × (Σ _ : Finset ℕ, Finset ℕ) × Bool, k ∈ K ↔
      k.1 ⊆ U ∧ k.2.1.1 ⊆ adjSet c 0 ∧ k.2.1.2 ⊆ k.2.1.1 := by
    intro k
    simp [hK, Finset.mem_product, Finset.mem_sigma]
  have hadjI : ∀ {Y : Finset ℕ}, Y ⊆ adjSet c 0 → Y ⊆ Finset.Ico 0 c.size := fun hY j hj => by
    have := mem_adjSet c 0 j (hY hj)
    simp only [Finset.mem_Ico]; omega
  have hSb0 : ∀ j ∈ Set.Ico 0 c.size, Disjoint (S j) (∅ : Finset V) :=
    fun _ _ => Finset.disjoint_empty_right _
  have hσb0 : ∀ k ∈ Set.Ico 0 c.size, σ k ∉ (∅ : Finset V) := fun _ _ => Finset.notMem_empty _
  refine MCExpT.of_sum K (fun k => k.1 ∪ k.2.1.2.image σ)
    (T := fun k => T' k.1 k.2.1.1 k.2.1.2 k.2.2) (N₀ := 2 * Ntree θ a b a' δ c N (N1 θ))
    ?_ ?_ ?_ hθ0 hA0 ?_
  · -- the sets are subsets
    intro k hk
    obtain ⟨h1, h3, h4⟩ := (hmemK k).1 hk
    refine Finset.union_subset ?_ ?_
    · exact h1.trans Finset.subset_union_left
    · exact (Finset.image_subset_image (h4.trans (hadjI h3))).trans Finset.subset_union_right
  · -- the terms
    intro k hk
    obtain ⟨h1, h3, h4⟩ := (hmemK k).1 hk
    have h := hT'r k.1 k.2.1.1 k.2.1.2 k.2.2 h3 h4
    have e := chainVars_eq (Sb := ∅) hSb0 hσS hσb0 hinj h1 (Finset.empty_subset _)
      (h4.trans (hadjI h3))
    simp only [Finset.empty_sdiff, Finset.coe_empty, Finset.union_empty] at e
    rw [e] at h
    exact h
  · -- the count
    intro Z
    have hcard : (K.filter fun k => k.1 ∪ k.2.1.2.image σ = Z).card ≤
        ((adjSet c 0).powerset ×ˢ (Finset.univ : Finset Bool)).card := by
      refine Finset.card_le_card_of_injOn (fun k => (k.2.1.1, k.2.2)) (fun k hk => ?_)
        (fun k hk k' hk' hkk' => ?_)
      · obtain ⟨hk, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
        obtain ⟨-, h3, -⟩ := (hmemK k).1 hk
        simp [h3]
      · obtain ⟨hkK, hkZ⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
        obtain ⟨hkK', hkZ'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk')
        obtain ⟨a1, a3, a4⟩ := (hmemK k).1 hkK
        obtain ⟨b1, b3, b4⟩ := (hmemK k').1 hkK'
        obtain ⟨e1, -, e3⟩ := chainMasks_eq (Sb := ∅) hSb0 hσS hσb0 hinj a1
          (Finset.empty_subset _) (a4.trans (hadjI a3))
        obtain ⟨f1, -, f3⟩ := chainMasks_eq (Sb := ∅) hSb0 hσS hσb0 hinj b1
          (Finset.empty_subset _) (b4.trans (hadjI b3))
        simp only [Finset.union_empty] at e1 e3 f1 f3
        rw [hkZ] at e1 e3
        rw [hkZ'] at f1 f3
        simp only [Prod.mk.injEq] at hkk'
        obtain ⟨k1, ⟨Y, Y'⟩, k4⟩ := k
        obtain ⟨l1, ⟨L, L'⟩, l4⟩ := k'
        simp only at e1 e3 f1 f3 hkk'
        obtain ⟨rfl, rfl⟩ := hkk'
        rw [← e1, ← e3, f1, f3]
    have hpow : ((adjSet c 0).powerset ×ˢ (Finset.univ : Finset Bool)).card ≤ 2 ^ (c.size + 1) := by
      rw [Finset.card_product, Finset.card_powerset, Finset.card_univ, Fintype.card_bool,
        pow_succ]
      exact Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by norm_num) (card_adjSet_le c 0))
    have hNt : 0 ≤ 2 * Ntree θ a b a' δ c N (N1 θ) :=
      ((hT'r ∅ ∅ ∅ true (Finset.empty_subset _) (Finset.empty_subset _))).nonneg
    calc ((K.filter fun k => k.1 ∪ k.2.1.2.image σ = Z).card : ℝ) *
          (2 * Ntree θ a b a' δ c N (N1 θ)) ≤
          ((2 ^ (c.size + 1) : ℕ) : ℝ) * (2 * Ntree θ a b a' δ c N (N1 θ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard.trans hpow) hNt
      _ = 2 ^ (c.size + 1) * (2 * Ntree θ a b a' δ c N (N1 θ)) := by push_cast; ring
  · -- the identity
    intro α t s hs hst ht1
    set w : V → ℂ := fun z => PhiZ ζ z (α z) with hw
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht1⟩
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs, by linarith⟩
    have hτ : t - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    -- the integral forms of the pair masks, at `α`
    set Rint : ℕ → Finset V → ℝ → ℝ → ℂ := fun j Z u v =>
      ∫ lam, (P j Z).C (α ∘ (P j Z).f) lam * e2 lam u v with hRint
    have hRc : ∀ j Z, Continuous fun p : ℝ × ℝ => Rint j Z (p.1 + s) (p.2 + s) := by
      intro j Z
      have h := continuous_e2_rep ((hPreg j Z).integrable (α ∘ (P j Z).f))
      exact h.comp ((continuous_fst.add continuous_const).prodMk
        (continuous_snd.add continuous_const))
    -- step 1: the integral forms
    have h1 : chainT σ ε c 0 F α t (fun t' => if s < t' then 1 else 0) =
        chainT σ ε c 0 (fun j (_ : V → ℝ) u v => ∑ Z ∈ (S j).powerset,
          (∏ z ∈ Z, w z) * Rint j Z u v) α t (fun t' => if s < t' then 1 else 0) := by
      refine chainT_congr' c 0 α (fun j hj u v hu hv => ?_) (fun _ _ => rfl) ht
      have hj' : j ∈ Set.Ico 0 c.size := by simpa using hj
      rw [(hGp j hj').2 α u v hu hv]
      exact Finset.sum_congr rfl fun Z hZ => by
        rw [(hP j Z hj' (Finset.mem_powerset.1 hZ)).2 α u v hu hv]
    -- step 2: rebase at `s`
    have h2 := chainT_rebase (σ := σ) (ε := ε) c 0 (fun j (_ : V → ℝ) u v =>
      ∑ Z ∈ (S j).powerset, (∏ z ∈ Z, w z) * Rint j Z u v) α hs
      (g := fun t' => if s < t' then 1 else 0) (fun t' ht' => by simp [not_lt.2 ht']) hst.le
    -- step 3: the continuation of the rebased chain is `1` at positive times
    have h3 : chainT σ ε c 0 (fun j (_ : V → ℝ) u v => ∑ Z ∈ (S j).powerset,
          (∏ z ∈ Z, w z) * Rint j Z (u + s) (v + s)) α (t - s)
          (fun u => if s < u + s then (1 : ℂ) else 0) =
        chainT σ ε c 0 (fun j (_ : V → ℝ) u v => ∑ Z ∈ (S j).powerset,
          (∏ z ∈ Z, w z) * Rint j Z (u + s) (v + s)) α (t - s) (fun _ => 1) :=
      chainT_congr_pos c 0 _ α (fun u hu => by simp [hu]) (by linarith)
    -- step 4: the masks of the pairs
    have h4 := chainT_expand (σ := σ) (ε := ε) α w (S := S)
      (R := fun j Z (_ : V → ℝ) u v => Rint j Z (u + s) (v + s)) (fun j Z => hRc j Z) c 0
      (fun j hj k hk hjk => hSS j (by simpa using hj) k (by simpa using hk) hjk)
      (g := fun _ => (1 : ℂ)) continuous_const (t - s)
    -- step 5: each mask is the rebased chain of `MCRep.treeOne`
    have h5 : ∀ Zp, chainT σ ε c 0 (fun j (_ : V → ℝ) u v => Rint j (Zp ∩ S j) (u + s) (v + s)) α
        (t - s) (fun _ => 1) = chainT σ ε c 0 (fun j β u v =>
          ∫ lam, (P j (Zp ∩ S j)).C (β ∘ (P j (Zp ∩ S j)).f) lam * e2 lam (u + s) (v + s)) α
          (t - s) (fun _ => 1) := fun Zp =>
      chainT_congr' c 0 (F := fun j (_ : V → ℝ) u v => Rint j (Zp ∩ S j) (u + s) (v + s))
        (F' := fun j β u v => ∫ lam, (P j (Zp ∩ S j)).C (β ∘ (P j (Zp ∩ S j)).f) lam *
          e2 lam (u + s) (v + s)) α (fun _ _ _ _ _ _ => rfl) (fun _ _ => rfl) hτ
    -- step 6: assemble
    have hprod : ∀ k ∈ K, ∏ z ∈ k.1 ∪ k.2.1.2.image σ, w z =
        (∏ z ∈ k.1, w z) * ∏ j ∈ k.2.1.2, w (σ j) := by
      intro k hk
      obtain ⟨k1, k3, k4⟩ := (hmemK k).1 hk
      have hk4 := k4.trans (hadjI k3)
      have hY'I : ∀ j ∈ k.2.1.2, j ∈ Set.Ico 0 c.size := fun j hj => by
        have := hk4 hj; simpa [Finset.mem_Ico] using this
      have hd2 : Disjoint k.1 (k.2.1.2.image σ) := by
        rw [Finset.disjoint_right]
        intro v hv hv'
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
        obtain ⟨i, hi, hvS⟩ := mem_unionS_zero.1 (k1 hv')
        exact hσS i hi j (hY'I j hj) hvS
      rw [Finset.prod_union hd2,
        Finset.prod_image fun x hx y hy h => hinj (hY'I x hx) (hY'I y hy) h]
    show chainT σ ε c 0 F α t (fun t' => if s < t' then 1 else 0) = _
    rw [h1, h2, h3, h4, hK, Finset.sum_product]
    refine Finset.sum_congr rfl fun Zp hZp => ?_
    rw [h5 Zp, hTe Zp α (t - s) s hτ hs1, Finset.sum_product, Finset.sum_sigma]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y hY => Finset.sum_congr rfl fun Y' hY' => ?_
    have hYa := Finset.mem_powerset.1 hY
    have hY'a := Finset.mem_powerset.1 hY'
    have hmem : ∀ pc : Bool, ((Zp, ⟨Y, Y'⟩, pc) : Finset V × (Σ _ : Finset ℕ, Finset ℕ) × Bool) ∈ K :=
      fun pc => (hmemK _).2 ⟨Finset.mem_powerset.1 hZp, hYa, hY'a⟩
    rw [Fintype.sum_bool, hprod _ (hmem true), hT'e Zp Y Y' true hYa hY'a α t s hs hst.le ht1,
      hT'e Zp Y Y' false hYa hY'a α t s hs hst.le ht1]
    simp only [hw]
    ring

/-- The constant of a tree chain, including the trivial tree. -/
@[expose] noncomputable def NtreeX (θ a b a' δ : ℝ) (c : LegalCode) (N : ℕ → ℝ) : ℝ :=
  max (N1 θ) (2 ^ (c.size + 1) * (2 * Ntree θ a b a' δ c N (N1 θ)))

/-- **A tree chain has the expansion (maincoef3) for `t > s`**, including the trivial tree (where
the chain integral is `1{t > s}`). -/
theorem MCExpT.chain' {θ a b A θ' a' δ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A) (ha' : 0 < a') (hab' : a' + b ≤ θ')
    (hθ'1 : θ' ≤ 1) (hδ : 0 < δ) (hδθ : δ + θ ≤ θ') (hδa : δ + a ≤ a') (hδb : δ + b ≤ 1)
    {σ : ℕ → V} {ε : ℕ → ℤ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) {ζ : V → ℤ} {c : LegalCode}
    (hζ : ∀ j ∈ Set.Ico 0 c.size, ζ (σ j) = ε j) (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {S : ℕ → Finset V} {N : ℕ → ℝ} {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : ∀ j ∈ Set.Ico 0 c.size, MCExp θ' a' b A (N j) ζ (S j) (F j))
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j) :
    MCExpT θ a b A (NtreeX θ a b a' δ c N) ζ
      (unionS S 0 c.size ∪ (Finset.Ico 0 c.size).image σ)
      (fun α t s => chainT σ ε c 0 F α t (fun t' => if s < t' then 1 else 0)) := by
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  by_cases hc : c = .nil
  · subst hc
    have e : unionS S 0 LegalCode.nil.size ∪ (Finset.Ico 0 LegalCode.nil.size).image σ = ∅ := by
      simp [unionS, LegalCode.size]
    rw [e]
    refine ((MCExp.one (V := V) (a := a) (b := b) (A := A) ζ hθ0 hθ1.le).toMCExpT.mono
      (le_max_left _ _) hA0).congr fun α t s _ hst _ => ?_
    simp [chainT_nil, hst]
  · exact (MCExpT.chain hθ0 hθ1 ha hb hab1 hab hA ha' hab' hθ'1 hδ hδθ hδa hδb hε hζ hc hinj hF
      hSS hσS).mono (le_max_right _ _) hA0

end Tree

end WaveTurbulence.ClassJR
