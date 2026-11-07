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

/-! # P4-W2 (session 17, step 3): the engine parameters of a term with exceptional records

`bkVal`: the block kind of a record from `(kd, zc)` (`kd = 0` with `zc` (the summand vanishes) becomes kind `1`, which has no clause).  `recBk recs kd zc`: the block kinds (`bkVal` at a record block,
`canonBadKind` elsewhere); `recAdd recs addr`: the union of the order pairs of the records; `recG`: the native couple exponents, raised by `1` at the pair row of a `kd = 3` record (clause (d)).
`badClauseP_rec`: `BadClauseP` of the engine datum `engDatum .. (recBk ..) (consX .. Bex add) (recG ..) g'`.  `excOf_bj_lower`: the branch of a record is the lower joint of its block.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

variable {d : ℕ} {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)
variable
  (XE : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (XB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)


open Classical in
/-- The block kind of a record. -/
noncomputable def bkVal (k : ℕ) (z : Prop) : Fin 4 :=
  if k = 0 then (if z then 1 else 0) else if k = 1 then 1 else if k = 3 then 3 else 2

open Classical in
/-- **The block kinds of a term with records**: `bkVal` at a record block, `canonBadKind` elsewhere. -/
noncomputable def recBk (hM9 : VineParamContract.VINEPARAM) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (zc : ExcRec G d → Prop) (i : Fin (assemblyShape hM9 B).I) : Fin 4 :=
  if h : ∃ r ∈ recs, r.blk = i.val then bkVal (kd h.choose) (zc h.choose) else canonBadKind hM9 B RD hG layer i

theorem recBk_of_rec (hM9 : VineParamContract.VINEPARAM) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (zc : ExcRec G d → Prop)
    (huniq : ∀ r ∈ recs, ∀ r' ∈ recs, r.blk = r'.blk → r = r') {r : ExcRec G d} (hr : r ∈ recs)
    (i : Fin (assemblyShape hM9 B).I) (hi : r.blk = i.val) :
    recBk B RD hG layer hM9 recs kd zc i = bkVal (kd r) (zc r) := by
  classical
  have h : ∃ r ∈ recs, r.blk = i.val := ⟨r, hr, hi⟩
  unfold recBk
  rw [dif_pos h]
  have := huniq _ h.choose_spec.1 r hr (h.choose_spec.2.trans hi.symm)
  rw [this]

theorem recBk_of_not (hM9 : VineParamContract.VINEPARAM) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (zc : ExcRec G d → Prop) (i : Fin (assemblyShape hM9 B).I) (hi : ∀ r ∈ recs, r.blk ≠ i.val) :
    recBk B RD hG layer hM9 recs kd zc i = canonBadKind hM9 B RD hG layer i := by
  classical
  unfold recBk
  rw [dif_neg]
  rintro ⟨r, hr, h⟩
  exact hi r hr h

open Classical in
/-- The union of the order pairs of the records. -/
noncomputable def recAdd (hM9 : VineParamContract.VINEPARAM) (recs : List (ExcRec G d)) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) :
    Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar) :=
  recs.toFinset.biUnion fun r => if zc r then ∅ else addr r

theorem addr_subset_recAdd (hM9 : VineParamContract.VINEPARAM) (recs : List (ExcRec G d)) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) {r : ExcRec G d} (hr : r ∈ recs)
    (hz : ¬ zc r) : addr r ⊆ recAdd B hM9 recs zc addr := by
  classical
  intro x hx
  unfold recAdd
  exact Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hr, by simpa [hz] using hx⟩

open Classical in
/-- The couple exponents: native, raised by `1` at the pair row of a `kd = 3` record. -/
noncomputable def recG (hM9 : VineParamContract.VINEPARAM) (hG : G.IsPlain) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (g : (assemblyShape hM9 B).VIdx → ℕ) (v : (assemblyShape hM9 B).VIdx) : ℕ :=
  if ∃ r ∈ recs, kd r = 3 ∧ (assemblyPairOf hM9 B hG v).1 = r.p0 then g v + 1 else g v

/-- **The branch of a record is the lower joint of its block.** -/
theorem excOf_bj_lower (hM9 : VineParamContract.VINEPARAM) {V : Finset (GBranch G.tree)} {r : ExcRec G d}
    (h : ExcOf B RD hG layer hLayer BE BX XE XB V r) (i : Fin (assemblyShape hM9 B).I) (hi : r.blk = i.val) :
    r.bj = (assemblyClockAtomEquiv hM9 B (.inl ⟨i, 0⟩)).1 := by
  rcases h with ⟨lv, pstar, hk, hop, c, f, hreal, hf, hp0, hbj', hblk, hrX⟩ | ⟨lv, pstar, h0, hop, hmax, c, f, hreal, hf, hp0, hbj', hblk, hrX⟩
  · have hi' : i = (lv.e pstar).1 := Fin.ext (hi.symm.trans hblk)
    rw [hbj', split_sb_b B RD hG layer hLayer lv pstar hk, hi']
    exact (VineEstS3.clock_t0 hM9 B (lv.e pstar).1).symm
  · have hi' : i = (lv.e pstar).1 := Fin.ext (by rw [← hi, hblk, h0])
    rw [hbj', (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0).trans (start_lower B RD hG layer hLayer (lv.e pstar)), hi']
    exact (VineEstS3.clock_t0 hM9 B (lv.e pstar).1).symm


theorem atom_ne_lower {hM9 : VineParamContract.VINEPARAM} (i j : Fin (assemblyShape hM9 B).I) (hij : i ≠ j)
    (c : (assemblyShape hM9 B).TVar) (hc : c = .inl ⟨i, 0⟩ ∨ (∃ (h : 0 < (assemblyShape hM9 B).m i), c = .inl ⟨i, ⟨1, by omega⟩⟩) ∨
      (∃ (h : 0 < (assemblyShape hM9 B).m i), c = .inr (.inl ⟨i, ⟨0, h⟩⟩))) :
    c ≠ .inl ⟨j, 0⟩ := by
  rcases hc with rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · intro h; simp at h; exact hij h.1
  · intro h'; simp at h'; exact hij h'.1
  · intro h'; simp at h'

open Classical in
/-- **`BadClauseP` of the engine datum of a term with records.** -/
theorem badClauseP_rec (hM9 : VineParamContract.VINEPARAM) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ)
    (zc : ExcRec G d → Prop) (addr : ExcRec G d → Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar))
    (huniq : ∀ r ∈ recs, ∀ r' ∈ recs, r.blk = r'.blk → r = r')
    (hkd : ∀ r ∈ recs, kd r ≤ 3)
    (hm2 : ∀ r ∈ recs, kd r = 2 → ∀ i : Fin (assemblyShape hM9 B).I, r.blk = i.val → 0 < (assemblyShape hM9 B).m i)
    (hbjl : ∀ r ∈ recs, ∃ j : Fin (assemblyShape hM9 B).I, r.blk = j.val ∧
      r.bj = (assemblyClockAtomEquiv hM9 B (.inl ⟨j, 0⟩)).1)
    (hclause : ∀ r ∈ recs, ∀ i : Fin (assemblyShape hM9 B).I, r.blk = i.val → RecClause0 B hM9 i (kd r) (zc r) (addr r))
    (hrow3 : ∀ r ∈ recs, kd r = 3 → ∃ v : (assemblyShape hM9 B).VIdx, (assemblyPairOf hM9 B hG v).1 = r.p0 ∧ v.1.val = r.blk)
    (hd : ∀ i : Fin n, (∀ r ∈ recs, r.blk ≠ i.val) → (assemblyPieceAt B i).vineType.IsBad = true → ¬ AClause hM9 B RD hG layer i →
      ∃ v : (assemblyShape hM9 B).VIdx, v.1 = i ∧
        1 ≤ max (rowCoupleG hM9 B RD hG layer hLayer v) (rowTreeG hM9 B RD hG layer hLayer v)) :
    BadClauseP (engDatum hM9 B hG W wN wDec (recBk B RD hG layer hM9 recs kd zc)
      (consX hM9 B (layC RD hG layer) (bexOf recs) (recAdd B hM9 recs zc addr))
      (recG B hM9 hG recs kd (rowCoupleG hM9 B RD hG layer hLayer)) (rowTreeG hM9 B RD hG layer hLayer)) := by
  have hnr : ∀ i : Fin (assemblyShape hM9 B).I, (∀ r ∈ recs, r.blk ≠ i.val) → ∀ c : (assemblyShape hM9 B).TVar,
      (c = .inl ⟨i, 0⟩ ∨ (∃ (h : 0 < (assemblyShape hM9 B).m i), c = .inl ⟨i, ⟨1, by omega⟩⟩) ∨
        (∃ (h : 0 < (assemblyShape hM9 B).m i), c = .inr (.inl ⟨i, ⟨0, h⟩⟩))) →
      (assemblyClockAtomEquiv hM9 B c).1 ∉ bexOf recs := by
    intro i hi c hc hmem
    obtain ⟨r, hr, hrb⟩ := mem_bexOf.mp hmem
    obtain ⟨j, hj1, hj2⟩ := hbjl r hr
    have hij : i ≠ j := fun h => hi r hr (hj1.trans (by rw [h]))
    have h1 : (assemblyClockAtomEquiv hM9 B c).1 = (assemblyClockAtomEquiv hM9 B (.inl ⟨j, 0⟩)).1 := hrb.symm.trans hj2
    have h2 : c = .inl ⟨j, 0⟩ := (assemblyClockAtomEquiv hM9 B).injective (Subtype.ext h1)
    exact atom_ne_lower B i j hij c hc h2
  refine badClauseP_engDatum hM9 B hG W wN wDec _ _ _ _ ?_ ?_ ?_
  · intro i hnor h0
    by_cases hrec : ∃ r ∈ recs, r.blk = i.val
    · obtain ⟨r, hr, hri⟩ := hrec
      rw [recBk_of_rec B RD hG layer hM9 recs kd zc huniq hr i hri] at h0
      have hk0 : kd r = 0 ∧ ¬ zc r := by
        unfold bkVal at h0
        by_cases hk : kd r = 0
        · by_cases hz : zc r
          · simp [hk, hz] at h0
          · exact ⟨hk, hz⟩
        · by_cases hk1 : kd r = 1 <;> by_cases hk3 : kd r = 3 <;> simp [hk, hk1, hk3] at h0
      obtain ⟨h, hh⟩ := hclause r hr i hri hk0.1 hk0.2
      refine ⟨h, ?_⟩
      have hsub : addr r ⊆ consX hM9 B (layC RD hG layer) (bexOf recs) (recAdd B hM9 recs zc addr) :=
        (addr_subset_recAdd B hM9 recs zc addr hr hk0.2).trans Finset.subset_union_right
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hsub h1, hsub h2⟩
      · exact Or.inr ⟨hsub h1, hsub h2⟩
    · have hnrec : ∀ r ∈ recs, r.blk ≠ i.val := fun r hr h => hrec ⟨r, hr, h⟩
      rw [recBk_of_not B RD hG layer hM9 recs kd zc i hnrec] at h0
      have hA : AClause hM9 B RD hG layer i := by
        by_contra hn
        have : canonBadKind hM9 B RD hG layer i = 3 := by unfold canonBadKind; rw [if_neg hn]
        rw [this] at h0
        exact absurd h0 (by decide)
      obtain ⟨h, hh⟩ := hA
      refine ⟨h, ?_⟩
      have key : ∀ c : (assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar, c ∈ badConstr hM9 B RD hG layer →
          (assemblyClockAtomEquiv hM9 B c.1).1 ∉ bexOf recs →
          c ∈ consX hM9 B (layC RD hG layer) (bexOf recs) (recAdd B hM9 recs zc addr) := by
        intro c hc hne
        unfold consX
        refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨?_, hne⟩)
        exact hc
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨key _ h1 (hnr i hnrec _ (Or.inr (Or.inr ⟨h, rfl⟩))), key _ h2 (hnr i hnrec _ (Or.inl rfl))⟩
      · exact Or.inr ⟨key _ h1 (hnr i hnrec _ (Or.inr (Or.inl ⟨h, rfl⟩))), key _ h2 (hnr i hnrec _ (Or.inl rfl))⟩
  · intro i hnor h2
    by_cases hrec : ∃ r ∈ recs, r.blk = i.val
    · obtain ⟨r, hr, hri⟩ := hrec
      rw [recBk_of_rec B RD hG layer hM9 recs kd zc huniq hr i hri] at h2
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
      rw [recBk_of_not B RD hG layer hM9 recs kd zc i hnrec] at h2
      rcases canonBadKind_cases hM9 B RD hG layer i with h | h <;> rw [h] at h2 <;> exact absurd h2 (by decide)
  · intro i hnor h3
    by_cases hrec : ∃ r ∈ recs, r.blk = i.val
    · obtain ⟨r, hr, hri⟩ := hrec
      rw [recBk_of_rec B RD hG layer hM9 recs kd zc huniq hr i hri] at h3
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
      have : (⟨i, hvi ▸ v.2⟩ : (assemblyShape hM9 B).VIdx) = v := by
        obtain ⟨v1, v2⟩ := v
        simp only at hvi
        subst hvi
        rfl
      rw [this]
      unfold recG
      rw [if_pos ⟨r, hr, hk3, hv1⟩]
      exact le_trans (Nat.le_add_left 1 _) (le_max_left _ _)
    · have hnrec : ∀ r ∈ recs, r.blk ≠ i.val := fun r hr h => hrec ⟨r, hr, h⟩
      rw [recBk_of_not B RD hG layer hM9 recs kd zc i hnrec] at h3
      have hnA : ¬ AClause hM9 B RD hG layer i := by
        intro hA
        have : canonBadKind hM9 B RD hG layer i = 0 := by unfold canonBadKind; rw [if_pos hA]
        rw [this] at h3
        exact absurd h3 (by decide)
      have hbad : (assemblyPieceAt B i).vineType.IsBad = true := by
        have : (assemblyShape hM9 B).nor i = false := hnor
        simpa [assemblyShape, shapeFamily] using this
      obtain ⟨⟨i', j⟩, hi, hj⟩ := hd i hnrec hbad hnA
      have hi' : i' = i := hi
      subst hi'
      refine ⟨j, ?_⟩
      unfold recG
      split_ifs
      · exact le_trans hj (max_le_max (Nat.le_add_right _ _) le_rfl)
      · exact hj

end WaveTurbulence.VineEstS5C.P4.W2
