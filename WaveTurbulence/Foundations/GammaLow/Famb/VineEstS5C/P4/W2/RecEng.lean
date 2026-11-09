/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSpec
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBlock
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BadEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRegion
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEng
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecRegion
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecSpec
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEng` (sha256 73bfbabb79ec7e12…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 17, step 3): the engine parameters of a term with exceptional records

`bkVal`: the block kind of a record from `(kd, zc)` (`kd = 0` with `zc` (the summand vanishes) becomes kind `1`, which has no clause).  `recBk recs kd zc`: the block kinds (`bkVal` at a record block,
`canonBadKind` elsewhere); `recAdd recs addr`: the union of the order pairs of the records; `recG`: the native couple exponents, raised by `1` at the pair row of a `kd = 3` record (clause (d)).
`badClauseP_rec`: `BadClauseP` of the engine datum `engDatum .. (recBk ..) (consX .. Bex add) (recG ..) g'`.  `excOf_bj_lower`: the branch of a record is the lower joint of its block.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

variable {d : ℕ} {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)
variable
  (XE : ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (XB : ∀ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)

open Classical in
/-- **The block kinds of a term with records**: `bkVal` at a record block, `canonBadKind` elsewhere. -/
noncomputable def recBkΓ (hM9 : NormalChartSupply γF) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (zc : ExcRec G d → Prop) (i : Fin (assemblyShapeΓ hM9 B).I) : Fin 4 :=
  if h : ∃ r ∈ recs, r.blk = i.val then bkVal (kd h.choose) (zc h.choose) else canonBadKindΓ hM9 B RD hG layer i

theorem recBk_of_recΓ (hM9 : NormalChartSupply γF) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (zc : ExcRec G d → Prop)
    (huniq : ∀ r ∈ recs, ∀ r' ∈ recs, r.blk = r'.blk → r = r') {r : ExcRec G d} (hr : r ∈ recs)
    (i : Fin (assemblyShapeΓ hM9 B).I) (hi : r.blk = i.val) :
    recBkΓ B RD hG layer hM9 recs kd zc i = bkVal (kd r) (zc r) := by
  classical
  have h : ∃ r ∈ recs, r.blk = i.val := ⟨r, hr, hi⟩
  unfold recBkΓ
  rw [dif_pos h]
  have := huniq _ h.choose_spec.1 r hr (h.choose_spec.2.trans hi.symm)
  rw [this]

theorem recBk_of_notΓ (hM9 : NormalChartSupply γF) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (zc : ExcRec G d → Prop) (i : Fin (assemblyShapeΓ hM9 B).I) (hi : ∀ r ∈ recs, r.blk ≠ i.val) :
    recBkΓ B RD hG layer hM9 recs kd zc i = canonBadKindΓ hM9 B RD hG layer i := by
  classical
  unfold recBkΓ
  rw [dif_neg]
  rintro ⟨r, hr, h⟩
  exact hi r hr h

open Classical in
/-- The union of the order pairs of the records. -/
noncomputable def recAddΓ (hM9 : NormalChartSupply γF) (recs : List (ExcRec G d)) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) :
    Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar) :=
  recs.toFinset.biUnion fun r => if zc r then ∅ else addr r

theorem addr_subset_recAddΓ (hM9 : NormalChartSupply γF) (recs : List (ExcRec G d)) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) {r : ExcRec G d} (hr : r ∈ recs)
    (hz : ¬ zc r) : addr r ⊆ recAddΓ B hM9 recs zc addr := by
  classical
  intro x hx
  unfold recAddΓ
  exact Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hr, by simpa [hz] using hx⟩

open Classical in
/-- The couple exponents: native, raised by `1` at the pair row of a `kd = 3` record. -/
noncomputable def recGΓ (hM9 : NormalChartSupply γF) (hG : G.IsPlain) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (g : (assemblyShapeΓ hM9 B).VIdx → ℕ) (v : (assemblyShapeΓ hM9 B).VIdx) : ℕ :=
  if ∃ r ∈ recs, kd r = 3 ∧ (assemblyPairOfΓ hM9 B hG v).1 = r.p0 then g v + 1 else g v

/-- **The branch of a record is the lower joint of its block.** -/
theorem excOf_bj_lowerΓ (hM9 : NormalChartSupply γF) {V : Finset (GBranch G.tree)} {r : ExcRec G d}
    (h : ExcOfΓ B RD hG layer hLayer BE BX XE XB V r) (i : Fin (assemblyShapeΓ hM9 B).I) (hi : r.blk = i.val) :
    r.bj = (assemblyClockAtomEquivΓ hM9 B (.inl ⟨i, 0⟩)).1 := by
  rcases h with ⟨lv, pstar, hk, hop, c, f, hreal, hf, hp0, hbj', hblk, hrX⟩ | ⟨lv, pstar, h0, hop, hmax, c, f, hreal, hf, hp0, hbj', hblk, hrX⟩
  · have hi' : i = (lv.e pstar).1 := Fin.ext (hi.symm.trans hblk)
    rw [hbj', split_sb_bΓ B RD hG layer hLayer lv pstar hk, hi']
    exact (VineEstS3.clock_t0Γ hM9 B (lv.e pstar).1).symm
  · have hi' : i = (lv.e pstar).1 := Fin.ext (by rw [← hi, hblk, h0])
    rw [hbj', (LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0).trans (start_lowerΓ B RD hG layer hLayer (lv.e pstar)), hi']
    exact (VineEstS3.clock_t0Γ hM9 B (lv.e pstar).1).symm

theorem atom_ne_lowerΓ {hM9 : NormalChartSupply γF} (i j : Fin (assemblyShapeΓ hM9 B).I) (hij : i ≠ j)
    (c : (assemblyShapeΓ hM9 B).TVar) (hc : c = .inl ⟨i, 0⟩ ∨ (∃ (h : 0 < (assemblyShapeΓ hM9 B).m i), c = .inl ⟨i, ⟨1, by omega⟩⟩) ∨
      (∃ (h : 0 < (assemblyShapeΓ hM9 B).m i), c = .inr (.inl ⟨i, ⟨0, h⟩⟩))) :
    c ≠ .inl ⟨j, 0⟩ := by
  rcases hc with rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · intro h; simp at h; exact hij h.1
  · intro h'; simp at h'; exact hij h'.1
  · intro h'; simp at h'

open Classical in
/-- **`BadClauseP` of the engine datum of a term with records.** -/
theorem badClauseP_recΓ (hM9 : NormalChartSupply γF) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (zc : ExcRec G d → Prop) (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (huniq : ∀ r ∈ recs, ∀ r' ∈ recs, r.blk = r'.blk → r = r')
    (hkd : ∀ r ∈ recs, kd r ≤ 3)
    (hm2 : ∀ r ∈ recs, kd r = 2 → ∀ i : Fin (assemblyShapeΓ hM9 B).I, r.blk = i.val → 0 < (assemblyShapeΓ hM9 B).m i)
    (hbjl : ∀ r ∈ recs, ∃ j : Fin (assemblyShapeΓ hM9 B).I, r.blk = j.val ∧
      r.bj = (assemblyClockAtomEquivΓ hM9 B (.inl ⟨j, 0⟩)).1)
    (hclause : ∀ r ∈ recs, ∀ i : Fin (assemblyShapeΓ hM9 B).I, r.blk = i.val → RecClause0Γ B hM9 i (kd r) (zc r) (addr r))
    (hrow3 : ∀ r ∈ recs, kd r = 3 → ∃ v : (assemblyShapeΓ hM9 B).VIdx, (assemblyPairOfΓ hM9 B hG v).1 = r.p0 ∧ v.1.val = r.blk)
    (hd : ∀ i : Fin n, (∀ r ∈ recs, r.blk ≠ i.val) → (assemblyPieceAtΓ B i).label.IsBad = true → ¬ AClauseΓ hM9 B RD hG layer i →
      ∃ v : (assemblyShapeΓ hM9 B).VIdx, v.1 = i ∧
        1 ≤ max (rowCoupleGΓ hM9 B RD hG layer hLayer v) (rowTreeGΓ hM9 B RD hG layer hLayer v)) :
    BadClauseP (engDatumΓ hM9 B hG W wN wDec (recBkΓ B RD hG layer hM9 recs kd zc)
      (consXΓ hM9 B (layC RD hG layer) (bexOf recs) (recAddΓ B hM9 recs zc addr))
      (recGΓ B hM9 hG recs kd (rowCoupleGΓ hM9 B RD hG layer hLayer)) (rowTreeGΓ hM9 B RD hG layer hLayer)) := by
  have hnr : ∀ i : Fin (assemblyShapeΓ hM9 B).I, (∀ r ∈ recs, r.blk ≠ i.val) → ∀ c : (assemblyShapeΓ hM9 B).TVar,
      (c = .inl ⟨i, 0⟩ ∨ (∃ (h : 0 < (assemblyShapeΓ hM9 B).m i), c = .inl ⟨i, ⟨1, by omega⟩⟩) ∨
        (∃ (h : 0 < (assemblyShapeΓ hM9 B).m i), c = .inr (.inl ⟨i, ⟨0, h⟩⟩))) →
      (assemblyClockAtomEquivΓ hM9 B c).1 ∉ bexOf recs := by
    intro i hi c hc hmem
    obtain ⟨r, hr, hrb⟩ := mem_bexOf.mp hmem
    obtain ⟨j, hj1, hj2⟩ := hbjl r hr
    have hij : i ≠ j := fun h => hi r hr (hj1.trans (by rw [h]))
    have h1 : (assemblyClockAtomEquivΓ hM9 B c).1 = (assemblyClockAtomEquivΓ hM9 B (.inl ⟨j, 0⟩)).1 := hrb.symm.trans hj2
    have h2 : c = .inl ⟨j, 0⟩ := (assemblyClockAtomEquivΓ hM9 B).injective (Subtype.ext h1)
    exact atom_ne_lowerΓ B i j hij c hc h2
  refine badClauseP_engDatumΓ hM9 B hG W wN wDec _ _ _ _ ?_ ?_ ?_
  · intro i hnor h0
    by_cases hrec : ∃ r ∈ recs, r.blk = i.val
    · obtain ⟨r, hr, hri⟩ := hrec
      rw [recBk_of_recΓ B RD hG layer hM9 recs kd zc huniq hr i hri] at h0
      have hk0 : kd r = 0 ∧ ¬ zc r := by
        unfold bkVal at h0
        by_cases hk : kd r = 0
        · by_cases hz : zc r
          · simp [hk, hz] at h0
          · exact ⟨hk, hz⟩
        · by_cases hk1 : kd r = 1 <;> by_cases hk3 : kd r = 3 <;> simp [hk, hk1, hk3] at h0
      obtain ⟨h, hh⟩ := hclause r hr i hri hk0.1 hk0.2
      refine ⟨h, ?_⟩
      have hsub : addr r ⊆ consXΓ hM9 B (layC RD hG layer) (bexOf recs) (recAddΓ B hM9 recs zc addr) :=
        (addr_subset_recAddΓ B hM9 recs zc addr hr hk0.2).trans Finset.subset_union_right
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hsub h1, hsub h2⟩
      · exact Or.inr ⟨hsub h1, hsub h2⟩
    · have hnrec : ∀ r ∈ recs, r.blk ≠ i.val := fun r hr h => hrec ⟨r, hr, h⟩
      rw [recBk_of_notΓ B RD hG layer hM9 recs kd zc i hnrec] at h0
      have hA : AClauseΓ hM9 B RD hG layer i := by
        by_contra hn
        have : canonBadKindΓ hM9 B RD hG layer i = 3 := by unfold canonBadKindΓ; rw [if_neg hn]
        rw [this] at h0
        exact absurd h0 (by decide)
      obtain ⟨h, hh⟩ := hA
      refine ⟨h, ?_⟩
      have key : ∀ c : (assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar, c ∈ badConstrΓ hM9 B RD hG layer →
          (assemblyClockAtomEquivΓ hM9 B c.1).1 ∉ bexOf recs →
          c ∈ consXΓ hM9 B (layC RD hG layer) (bexOf recs) (recAddΓ B hM9 recs zc addr) := by
        intro c hc hne
        unfold consXΓ
        refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨?_, hne⟩)
        exact hc
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨key _ h1 (hnr i hnrec _ (Or.inr (Or.inr ⟨h, rfl⟩))), key _ h2 (hnr i hnrec _ (Or.inl rfl))⟩
      · exact Or.inr ⟨key _ h1 (hnr i hnrec _ (Or.inr (Or.inl ⟨h, rfl⟩))), key _ h2 (hnr i hnrec _ (Or.inl rfl))⟩
  · intro i hnor h2
    by_cases hrec : ∃ r ∈ recs, r.blk = i.val
    · obtain ⟨r, hr, hri⟩ := hrec
      rw [recBk_of_recΓ B RD hG layer hM9 recs kd zc huniq hr i hri] at h2
      have hle := hkd r hr
      have hk2 : kd r = 2 := by
        unfold bkVal at h2
        by_cases hk : kd r = 0
        · by_cases hz : zc r <;> simp [hk, hz] at h2
        · by_cases hk1 : kd r = 1
          · simp [hk, hk1] at h2
          · by_cases hk3 : kd r = 3
            · simp [hk, hk1, hk3] at h2
            · omega
      exact hm2 r hr hk2 i hri
    · have hnrec : ∀ r ∈ recs, r.blk ≠ i.val := fun r hr h => hrec ⟨r, hr, h⟩
      rw [recBk_of_notΓ B RD hG layer hM9 recs kd zc i hnrec] at h2
      rcases canonBadKind_casesΓ hM9 B RD hG layer i with h | h <;> rw [h] at h2 <;> exact absurd h2 (by decide)
  · intro i hnor h3
    by_cases hrec : ∃ r ∈ recs, r.blk = i.val
    · obtain ⟨r, hr, hri⟩ := hrec
      rw [recBk_of_recΓ B RD hG layer hM9 recs kd zc huniq hr i hri] at h3
      have hk3 : kd r = 3 := by
        unfold bkVal at h3
        by_cases hk : kd r = 0
        · by_cases hz : zc r <;> simp [hk, hz] at h3
        · by_cases hk1 : kd r = 1
          · simp [hk, hk1] at h3
          · by_cases hk3 : kd r = 3
            · exact hk3
            · simp [hk, hk1, hk3] at h3
      obtain ⟨v, hv1, hv2⟩ := hrow3 r hr hk3
      have hvi : v.1 = i := Fin.ext (hv2.trans hri)
      refine ⟨hvi ▸ v.2, ?_⟩
      have : (⟨i, hvi ▸ v.2⟩ : (assemblyShapeΓ hM9 B).VIdx) = v := by
        obtain ⟨v1, v2⟩ := v
        simp only at hvi
        subst hvi
        rfl
      rw [this]
      unfold recGΓ
      rw [if_pos ⟨r, hr, hk3, hv1⟩]
      exact le_trans (Nat.le_add_left 1 _) (le_max_left _ _)
    · have hnrec : ∀ r ∈ recs, r.blk ≠ i.val := fun r hr h => hrec ⟨r, hr, h⟩
      rw [recBk_of_notΓ B RD hG layer hM9 recs kd zc i hnrec] at h3
      have hnA : ¬ AClauseΓ hM9 B RD hG layer i := by
        intro hA
        have : canonBadKindΓ hM9 B RD hG layer i = 0 := by unfold canonBadKindΓ; rw [if_pos hA]
        rw [this] at h3
        exact absurd h3 (by decide)
      have hbad : (assemblyPieceAtΓ B i).label.IsBad = true := by
        have : (assemblyShapeΓ hM9 B).nor i = false := hnor
        simpa [assemblyShapeΓ, shapeFamily] using this
      obtain ⟨⟨i', j⟩, hi, hj⟩ := hd i hnrec hbad hnA
      have hi' : i' = i := hi
      subst hi'
      refine ⟨j, ?_⟩
      unfold recGΓ
      split_ifs
      · exact le_trans hj (max_le_max (Nat.le_add_right _ _) le_rfl)
      · exact hj

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
