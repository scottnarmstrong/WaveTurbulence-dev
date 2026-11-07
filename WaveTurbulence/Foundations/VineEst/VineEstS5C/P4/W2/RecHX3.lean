/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecHX2

/-! # P4-W2 (session 18, step 3c): `hX_rec`, the product identity `hX` of `freeDict_rec`

For a record list with distinct pairs and branches and the per-record `PieceRepW` at the merged rows (`rows_merge`), the product of the exceptional weights over the pair rows is
`kind1Pref * k2c` times the product of the engine rows at the exceptional pair rows and branch rows, almost everywhere on the engine time domain (`hX_of_records` + `kind1Pref_k2c_eq`;
a kind-0 record with `zc` carries `kind 1`, its factor vanishing on both sides).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B
open scoped ENNReal

theorem bkVal_eq_one_iff (k : ℕ) (z : Prop) : bkVal k z = 1 ↔ (k = 1 ∨ (k = 0 ∧ z)) := by
  classical
  unfold bkVal
  by_cases h0 : k = 0
  · subst h0; by_cases hz : z <;> simp [hz]
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h3 : k = 3 <;> simp [h0, h1, h3]

open Classical in
theorem f0Of_eq_rho {S : WaveTurbulence.SumintShape} {d : ℕ} (η : ℝ) (i : Fin S.I) {kd : ℕ} {zc : Prop} (hkd : kd ≤ 3)
    (hz : ¬ (zc ∧ kd = 0)) (τ : S.TVar → ℝ) (rr : Mom d) :
    f0Of (S := S) (d := d) η i kd τ rr =
      (if bkVal kd zc = 1 then ((‖rr‖ : ℝ) : ℂ) else 1) * (if bkVal kd zc = 2 then k2f η i τ else 1) := by
  unfold f0Of bkVal
  by_cases h0 : kd = 0
  · subst h0
    have hz' : ¬ zc := fun h => hz ⟨h, rfl⟩
    simp [hz']
  · by_cases h1 : kd = 1
    · subst h1; simp
    · by_cases h2 : kd = 2
      · subst h2; simp
      · have h3 : kd = 3 := by omega
        subst h3; simp

theorem f0Of_of_zero {S : WaveTurbulence.SumintShape} {d : ℕ} (η : ℝ) (i : Fin S.I) {kd : ℕ} (hk : kd = 0)
    (τ : S.TVar → ℝ) (rr : Mom d) : f0Of (S := S) (d := d) η i kd τ rr = 1 := by
  classical
  unfold f0Of
  simp [hk]

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **`hX` of `freeDict_rec`** from the per-record representations. -/
theorem hX_rec (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {L : ℝ} (hL : L ≠ 0) (η : ℝ) (base : Mom P.d)
    (β : Fin 4 → (Fin P.d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (tt : Fin 3 → ℝ) (x : (assemblyShape hM9 B).VIdx → (Fin P.d → ℤ))
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Rw' : ∀ ρ : Row (engDatum hM9 B hG W wN wDec bk cons g g'), RowData (engDatum hM9 B hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (Bx : Set (Fin 3 → ℝ)) (htt : tt ∈ Bx)
    (hr1 : ‖sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
      sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1‖ ≤ 1)
    (recs : List (ExcRec G P.d)) (hnp : (recs.map ExcRec.p0).Nodup) (hnb : (recs.map ExcRec.bj).Nodup)
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (kd : ExcRec G P.d → ℕ) (zc : ExcRec G P.d → Prop)
    (blkf : ExcRec G P.d → Fin (assemblyShape hM9 B).I)
    (hinj : ∀ r ∈ recs, ∀ r' ∈ recs, blkf r = blkf r' → r = r')
    (hkd : ∀ r ∈ recs, kd r ≤ 3)
    (hbkr : ∀ r ∈ recs, bk (blkf r) = bkVal (kd r) (zc r))
    (hbkn : ∀ i, (∀ r ∈ recs, blkf r ≠ i) → bk i ≠ 1 ∧ bk i ≠ 2)
    (hnor : ∀ r ∈ recs, (assemblyShape hM9 B).nor (blkf r) = false)
    (vpf vbf : ExcRec G P.d → (assemblyShape hM9 B).VIdx)
    (hvp : ∀ r ∈ recs, (assemblyPairOf hM9 B hG (vpf r)).1 = r.p0)
    (hvb : ∀ r ∈ recs, (assemblyBranchOf hM9 B (vbf r)).1 = r.bj)
    (hrep : ∀ r ∈ recs, ∃ (ε : ℝ) (Xr : ((assemblyShape hM9 B).TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (bnd : ℝ≥0∞),
      PieceRepW (P := P) (assemblyShape_I_pos hM9 B) (Rw' (Sum.inl (vpf r))) (Rw' (Sum.inr (vbf r))) ε
        (f0Of η (blkf r) (kd r)) Xr bnd Bx ∧
      (zc r → ∀ tt ∈ Bx, ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
        τ ∈ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
          ∀ (rr k : Mom P.d), Xr τ tt rr k = 0) ∧
      ∀ (tt : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ),
        r.X (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) =
          Xr τ tt (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
            (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inl (vpf r))) ∧
        rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inr (vbf r)) =
          rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inl (vpf r)) +
          ε • (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)) :
    ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
      τ ∈ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      (∏ v ∈ vpSet hM9 B hG recs, xqOf recs (assemblyPairOf hM9 B hG v).1 tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)) =
        ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) * k2c bk η τ *
        (∏ v ∈ vpSet hM9 B hG recs, (allCR Rw').W (Sum.inl v) ((allCR Rw').clock τ tt (Sum.inl v))
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
          (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inl v))) *
        ∏ v ∈ vbSet hM9 B recs, (allCR Rw').W (Sum.inr v) ((allCR Rw').clock τ tt (Sum.inr v))
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
          (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inr v)) := by
  classical
  set E := sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) with hE
  have hnd : recs.Nodup := by
    refine List.Nodup.of_map ExcRec.p0 hnp
  have hall : ∀ r ∈ recs, ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
      τ ∈ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      r.X (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) =
        ((if bkVal (kd r) (zc r) = 1 then ((‖E 0 - E 1‖ : ℝ) : ℂ) else 1) *
            (if bkVal (kd r) (zc r) = 2 then k2f η (blkf r) τ else 1)) *
          ((allCR Rw').W (Sum.inl (vpf r)) ((allCR Rw').clock τ tt (Sum.inl (vpf r))) (E 0 - E 1)
            (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x E (Sum.inl (vpf r))) *
          (allCR Rw').W (Sum.inr (vbf r)) ((allCR Rw').clock τ tt (Sum.inr (vbf r))) (E 0 - E 1)
            (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x E (Sum.inr (vbf r)))) := by
    intro r hr
    obtain ⟨ε, Xr, bnd, hPW, hz, hlink⟩ := hrep r hr
    have hpw := hPW.2.2.2.2.2 tt htt
    by_cases hzk : zc r ∧ kd r = 0
    · filter_upwards [hpw, hz hzk.1 tt htt] with τ h1 h2 hmem
      have hx := h1 hmem (E 0 - E 1) (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x E (Sum.inl (vpf r))) hr1
      rw [h2 hmem _ _] at hx
      have hk1 : ¬ kd r = 1 := by omega
      replace hx : (0 : ℂ) = f0Of (S := assemblyShape hM9 B) η (blkf r) (kd r) τ (E 0 - E 1) * _ := hx
      rw [f0Of_of_zero η (blkf r) hzk.2, one_mul] at hx
      obtain ⟨hl1, hl2⟩ := hlink tt τ
      rw [hl1, h2 hmem _ _, hl2]
      have hb1 : bkVal (kd r) (zc r) = 1 := (bkVal_eq_one_iff _ _).2 (Or.inr ⟨hzk.2, hzk.1⟩)
      rw [if_pos hb1, if_neg (by rw [hb1]; decide), mul_one]
      have hx0 : (allCR Rw').W (Sum.inl (vpf r)) ((allCR Rw').clock τ tt (Sum.inl (vpf r))) (E 0 - E 1)
            (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x E (Sum.inl (vpf r))) *
          (allCR Rw').W (Sum.inr (vbf r)) ((allCR Rw').clock τ tt (Sum.inr (vbf r))) (E 0 - E 1)
            (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x E (Sum.inl (vpf r)) + ε • (E 0 - E 1)) = 0 := hx.symm
      rw [hx0, mul_zero]
    · filter_upwards [hpw] with τ h1 hmem
      have hx := h1 hmem (E 0 - E 1) (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x E (Sum.inl (vpf r))) hr1
      obtain ⟨hl1, hl2⟩ := hlink tt τ
      rw [hl1, hx, hl2]
      have hz2 : ¬ (zc r ∧ kd r = 0) := fun h => hzk ⟨h.1, h.2⟩
      show f0Of (S := assemblyShape hM9 B) η (blkf r) (kd r) τ (E 0 - E 1) * _ = _
      rw [f0Of_eq_rho η (blkf r) (hkd r hr) hz2]
      rfl
  have hall' := (Filter.eventually_all_finset recs.toFinset).2 (fun r hr => hall r (List.mem_toFinset.mp hr))
  filter_upwards [hall'] with τ hτ hmem
  have hX := hX_of_records hM9 B hG recs hnp hnb hreg tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
    (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) vpf vbf hvp hvb
    (fun v => (allCR Rw').W (Sum.inl v) ((allCR Rw').clock τ tt (Sum.inl v)) (E 0 - E 1)
      (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x E (Sum.inl v)))
    (fun v => (allCR Rw').W (Sum.inr v) ((allCR Rw').clock τ tt (Sum.inr v)) (E 0 - E 1)
      (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x E (Sum.inr v)))
    (fun r => (if bkVal (kd r) (zc r) = 1 then ((‖E 0 - E 1‖ : ℝ) : ℂ) else 1) *
      (if bkVal (kd r) (zc r) = 2 then k2f η (blkf r) τ else 1))
    ((recs.map fun r => (if bkVal (kd r) (zc r) = 1 then ((‖E 0 - E 1‖ : ℝ) : ℂ) else 1) *
      (if bkVal (kd r) (zc r) = 2 then k2f η (blkf r) τ else 1)).prod)
    (fun r hr => hτ r (List.mem_toFinset.mpr hr) hmem) rfl
  rw [hX, kind1Pref_k2c_eq hM9 B hG W wN wDec bk cons g g' η τ E recs kd zc blkf hinj hnd hbkr hbkn hnor]

end WaveTurbulence.VineEstS5C.P4.W2
