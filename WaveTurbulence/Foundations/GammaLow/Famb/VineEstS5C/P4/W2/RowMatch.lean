/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeRow
public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowMatch
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.FreeRow
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowMatch` (sha256 2e05299ec517979a…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (N2(b)): moving the pair and branch products onto the `sumint` rows

* `prod_pairs_rows`, `prod_interior_rows`: the products over the regional pairs and over the interior branches `U ∖ {a}` are products over
  the `sumint` rows (`Equiv.prod_comp` with `assemblyPairOrder` / `assemblyIntOrder`, as in `clLocalStarProduct_eq_weights`).
* `hrow_of_rowwise`: if the weight of the pair of row `v` is `cK v ·` (row `inl v`) and the weight of the branch of row `v` is
  `cL v ·` (row `inr v`), then the product of the row-form weights is `(∏ cK)(∏ cL) · ∏_ρ (row ρ)`.
* `pairMom_eq`, `branchMom_eq`: the row momenta of the engine datum are the decoration momenta of the first leaf of the pair, resp. of the
  branch, of the row (`assembly_pair_momentum`, `assembly_branch_momentum`).
* `natCR3`: the native rows of the region (the starred kernels `K_Q^*`, `K_T^*` at their parent clocks, as `VineEstS3.assemblyClockedS`)
  as three-clock rows of the engine datum (third clock: a repetition, mode `0`); `qRow_eq_natCR3`, `tRow_eq_natCR3`: at the region's
  clocks `u = clLocalClock R tt (assemblyClockEquiv τ)` and the top clock `tt 0`, the native rows `qRow`, `tRow` of the row form are the rows
  of `natCR3`.
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
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The product over the regional pairs is a product over the `sumint` rows. -/
theorem prod_pairs_rowsΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) {M : Type*} [CommMonoid M]
    (f : SourcePair G → M) :
    ∏ p ∈ clRegionalPairs hG U, f p = ∏ v : (assemblyShapeΓ hM9 B).VIdx, f (assemblyPairOfΓ hM9 B hG v).1 := by
  rw [← Finset.prod_coe_sort]
  exact (Equiv.prod_comp ((assemblyRowEquivΓ hM9 B).symm.trans (assemblyPairOrderΓ hG B hM9).symm) (fun p => f p.1)).symm

/-- The product over the interior branches is a product over the `sumint` rows. -/
theorem prod_interior_rowsΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) {M : Type*} [CommMonoid M]
    (f : GBranch G.tree → M) :
    ∏ v ∈ U.erase a, f v = ∏ v : (assemblyShapeΓ hM9 B).VIdx, f (assemblyBranchOfΓ hM9 B v).1 := by
  change ∏ v ∈ clInteriorBranches R, f v = _
  rw [← Finset.prod_coe_sort]
  exact (Equiv.prod_comp ((assemblyRowEquivΓ hM9 B).symm.trans (assemblyIntOrderΓ hM9 B).e.symm) (fun v => f v.1)).symm

section Mom
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)

/-- The momentum of the `K` row `v` of the engine datum is the decoration momentum at the first leaf of the pair of `v`. -/
theorem pairMom_eqΓ {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ))
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    rowMom (engDatumΓ hM9 B hG W wN wDec bk cons g g') L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inl v) =
      cosetDecoration G L base (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)
        ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode :=
  (assembly_pair_momentumΓ hM9 B hG W hL base β hβ x v).symm

/-- The momentum of the `ℒ` row `v` of the engine datum is the decoration momentum at the branch of `v`. -/
theorem branchMom_eqΓ {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ))
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    rowMom (engDatumΓ hM9 B hG W wN wDec bk cons g g') L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inr v) =
      cosetDecoration G L base (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)
        (assemblyBranchOfΓ hM9 B v).1.toNode :=
  (assembly_branch_momentumΓ hM9 B hG W hL base β hβ x v).symm

/-- The slot of the first clock of row `ρ` (parent clock of the first leaf, resp. of the branch). -/
noncomputable def natSlotΓ : (assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx → Fin 3 →
    (assemblyShapeΓ hM9 B).TVar ⊕ Fin 3
  | Sum.inl v => ![nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode,
      nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.secondLeaf hG).toNode,
      nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode]
  | Sum.inr v => ![nodeSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v).1.toNode, Sum.inl (branchSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v)),
      nodeSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v).1.toNode]

variable (RD : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer)

/-- **The native rows of the region as three-clock engine rows.** -/
noncomputable def natCR3Γ : ClockedRows3 (engDatumΓ hM9 B hG W wN wDec bk cons g g') where
  W := fun ρ c _ k => match ρ with
    | Sum.inl v => VineEst.selCoupleRow L γ δ F RD hG layer hLayer (assemblyPairOfΓ hM9 B hG v).1 (c 0) (c 1) k
    | Sum.inr v => VineEst.selTreeRow L γ δ F RD hG layer hLayer (assemblyBranchOfΓ hM9 B v).1 (c 0) (c 1) k
  slot := natSlotΓ hM9 B hG
  W_indep := fun _ _ _ _ _ => rfl

theorem qRow_eq_natCR3Γ (base : Mom d) (X : GNode G.tree → (Fin d → ℤ)) (tt : Fin 3 → ℝ)
    (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) (r : Mom d) (v : (assemblyShapeΓ hM9 B).VIdx) :
    qRow RD hG L γ δ F layer hLayer base (tt 0) X (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ))
        (assemblyPairOfΓ hM9 B hG v).1 =
      (natCR3Γ hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W (Sum.inl v)
        ((natCR3Γ hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt (Sum.inl v)) r
        (cosetDecoration G L base X ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode) := by
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOfΓ hM9 B hG v)
  have h1 := nodeSlot_specΓ hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOfΓ hM9 B hG v).2).1 hp.1 tt τ
  have h2 := nodeSlot_specΓ hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOfΓ hM9 B hG v).2).2 hp.2 tt τ
  simp only [qRow, natCR3Γ, ClockedRows3.clock, natSlotΓ, slotVal]
  rw [h1, h2]
  rfl

theorem tRow_eq_natCR3Γ (base : Mom d) (X : GNode G.tree → (Fin d → ℤ)) (tt : Fin 3 → ℝ)
    (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) (r : Mom d) (v : (assemblyShapeΓ hM9 B).VIdx) :
    tRow RD hG L γ δ F layer hLayer base (tt 0) X (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ))
        (assemblyBranchOfΓ hM9 B v).1 =
      (natCR3Γ hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W (Sum.inr v)
        ((natCR3Γ hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt (Sum.inr v)) r
        (cosetDecoration G L base X (assemblyBranchOfΓ hM9 B v).1.toNode) := by
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOfΓ hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOfΓ hM9 B v).2).2
  have h3 := nodeSlot_specΓ hM9 B _ hbr (interior_ne (assemblyBranchOfΓ hM9 B v)) tt τ
  have h4 := branchSlot_specΓ hM9 B (assemblyBranchOfΓ hM9 B v) tt τ
  simp only [tRow, natCR3Γ, ClockedRows3.clock, natSlotΓ, slotVal]
  rw [h3, h4]
  rfl

end Mom

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
