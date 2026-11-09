/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecContract
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecHX
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeRow
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecF0
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecHX2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecContract
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecHX2` (sha256 d9d438ee9de27569…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 18, step 3b): the constant `kind1Pref * k2c` of a term with records

`kind1Pref_k2c_eq`: for the block kinds of a record list (`bkVal` at the record blocks, no kind 1 or 2 elsewhere) the engine constant `kind1Pref * k2c` is the product over the records of
`‖E₀-E₁‖` (kind 1) or `1`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem kind1Pref_eq_prodΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (E : Fin 4 → Mom d)
    (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (blkf : ExcRec G d → Fin (assemblyShapeΓ hM9 B).I)
    (hinj : ∀ r ∈ recs, ∀ r' ∈ recs, blkf r = blkf r' → r = r') (hnd : recs.Nodup)
    (hbkr : ∀ r ∈ recs, bk (blkf r) = bkVal (kd r) (zc r))
    (hbkn : ∀ i, (∀ r ∈ recs, blkf r ≠ i) → bk i ≠ 1 ∧ bk i ≠ 2)
    (hnor : ∀ r ∈ recs, (assemblyShapeΓ hM9 B).nor (blkf r) = false) :
    ((kind1Pref (D := engDatumΓ hM9 B hG W wN wDec bk cons g g') E : ℝ) : ℂ) =
      (recs.map fun r => if bkVal (kd r) (zc r) = 1 then ((‖E 0 - E 1‖ : ℝ) : ℂ) else 1).prod := by
  classical
  have hset : (Finset.univ.filter fun i => (engDatumΓ hM9 B hG W wN wDec bk cons g g').S.nor i = false ∧
      (engDatumΓ hM9 B hG W wN wDec bk cons g g').badKind i = 1) =
      (recs.toFinset.filter fun r => bkVal (kd r) (zc r) = 1).image blkf := by
    ext i
    constructor
    · intro hi
      obtain ⟨-, hn, h1⟩ := Finset.mem_filter.mp hi
      by_cases h : ∃ r ∈ recs, blkf r = i
      · obtain ⟨r, hr, rfl⟩ := h
        exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, by rw [← hbkr r hr]; exact h1⟩, rfl⟩
      · have h' : ∀ r ∈ recs, blkf r ≠ i := fun r hr hh => h ⟨r, hr, hh⟩
        exact absurd h1 (hbkn i h').1
    · intro hi
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hr1, h1⟩ := Finset.mem_filter.mp hr
      have hr' := List.mem_toFinset.mp hr1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnor r hr', by
        rw [show (engDatumΓ hM9 B hG W wN wDec bk cons g g').badKind (blkf r) = bk (blkf r) from rfl, hbkr r hr']; exact h1⟩
  have hcard : (Finset.univ.filter fun i => (engDatumΓ hM9 B hG W wN wDec bk cons g g').S.nor i = false ∧
      (engDatumΓ hM9 B hG W wN wDec bk cons g g').badKind i = 1).card =
      (recs.toFinset.filter fun r => bkVal (kd r) (zc r) = 1).card := by
    rw [hset]
    have hinjOn : Set.InjOn blkf ↑(recs.toFinset.filter fun r => bkVal (kd r) (zc r) = 1) := by
      intro r hr r' hr' h
      exact hinj r (List.mem_toFinset.mp (Finset.mem_filter.mp hr).1) r' (List.mem_toFinset.mp (Finset.mem_filter.mp hr').1) h
    convert Finset.card_image_of_injOn hinjOn
    all_goals first | rfl | (congr 2; exact Subsingleton.elim _ _)
  unfold kind1Pref
  rw [hcard]
  rw [Complex.ofReal_pow, prod_map_ite_pow recs hnd]

theorem k2c_eq_recsΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4) (η : ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ)
    (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (blkf : ExcRec G d → Fin (assemblyShapeΓ hM9 B).I)
    (hinj : ∀ r ∈ recs, ∀ r' ∈ recs, blkf r = blkf r' → r = r') (hnd : recs.Nodup)
    (hbkr : ∀ r ∈ recs, bk (blkf r) = bkVal (kd r) (zc r))
    (hbkn : ∀ i, (∀ r ∈ recs, blkf r ≠ i) → bk i ≠ 1 ∧ bk i ≠ 2)
    (hnor : ∀ r ∈ recs, (assemblyShapeΓ hM9 B).nor (blkf r) = false) :
    k2c bk η τ = (recs.map fun r => if bkVal (kd r) (zc r) = 2 then k2f η (blkf r) τ else 1).prod := by
  classical
  rw [k2c_eq_prod, ← Finset.prod_filter, ← List.prod_toFinset _ hnd, ← Finset.prod_filter]
  have hset : (Finset.univ.filter fun i => (assemblyShapeΓ hM9 B).nor i = false ∧ bk i = 2) =
      (recs.toFinset.filter fun r => bkVal (kd r) (zc r) = 2).image blkf := by
    ext i
    constructor
    · intro hi
      obtain ⟨-, hn, h2⟩ := Finset.mem_filter.mp hi
      by_cases h : ∃ r ∈ recs, blkf r = i
      · obtain ⟨r, hr, rfl⟩ := h
        exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, by rw [← hbkr r hr]; exact h2⟩, rfl⟩
      · have h' : ∀ r ∈ recs, blkf r ≠ i := fun r hr hh => h ⟨r, hr, hh⟩
        exact absurd h2 (hbkn i h').2
    · intro hi
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hr1, h1⟩ := Finset.mem_filter.mp hr
      have hr' := List.mem_toFinset.mp hr1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnor r hr', by rw [hbkr r hr']; exact h1⟩
  rw [hset]
  have hinjOn : Set.InjOn blkf ↑(recs.toFinset.filter fun r => bkVal (kd r) (zc r) = 2) := by
    intro r hr r' hr' h
    exact hinj r (List.mem_toFinset.mp (Finset.mem_filter.mp hr).1) r' (List.mem_toFinset.mp (Finset.mem_filter.mp hr').1) h
  rw [Finset.prod_image hinjOn]

theorem kind1Pref_k2c_eqΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (η : ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) (E : Fin 4 → Mom d)
    (recs : List (ExcRec G d)) (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (blkf : ExcRec G d → Fin (assemblyShapeΓ hM9 B).I)
    (hinj : ∀ r ∈ recs, ∀ r' ∈ recs, blkf r = blkf r' → r = r') (hnd : recs.Nodup)
    (hbkr : ∀ r ∈ recs, bk (blkf r) = bkVal (kd r) (zc r))
    (hbkn : ∀ i, (∀ r ∈ recs, blkf r ≠ i) → bk i ≠ 1 ∧ bk i ≠ 2)
    (hnor : ∀ r ∈ recs, (assemblyShapeΓ hM9 B).nor (blkf r) = false) :
    ((kind1Pref (D := engDatumΓ hM9 B hG W wN wDec bk cons g g') E : ℝ) : ℂ) * k2c bk η τ =
      (recs.map fun r => (if bkVal (kd r) (zc r) = 1 then ((‖E 0 - E 1‖ : ℝ) : ℂ) else 1) *
        (if bkVal (kd r) (zc r) = 2 then k2f η (blkf r) τ else 1)).prod := by
  rw [kind1Pref_eq_prodΓ hM9 B hG W wN wDec bk cons g g' E recs kd zc blkf hinj hnd hbkr hbkn hnor,
    k2c_eq_recsΓ hM9 B bk η τ recs kd zc blkf hinj hnd hbkr hbkn hnor, List.prod_map_mul]

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
