/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeRow
public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked

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
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The product over the regional pairs is a product over the `sumint` rows. -/
theorem prod_pairs_rows (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) {M : Type*} [CommMonoid M]
    (f : SourcePair G → M) :
    ∏ p ∈ clRegionalPairs hG U, f p = ∏ v : (assemblyShape hM9 B).VIdx, f (assemblyPairOf hM9 B hG v).1 := by
  rw [← Finset.prod_coe_sort]
  exact (Equiv.prod_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyPairOrder hG B hM9).symm) (fun p => f p.1)).symm

/-- The product over the interior branches is a product over the `sumint` rows. -/
theorem prod_interior_rows (hM9 : VINEPARAM) (B : CLChainAssembly G R n) {M : Type*} [CommMonoid M]
    (f : GBranch G.tree → M) :
    ∏ v ∈ U.erase a, f v = ∏ v : (assemblyShape hM9 B).VIdx, f (assemblyBranchOf hM9 B v).1 := by
  change ∏ v ∈ clInteriorBranches R, f v = _
  rw [← Finset.prod_coe_sort]
  exact (Equiv.prod_comp ((assemblyRowEquiv hM9 B).symm.trans (assemblyIntOrder hM9 B).e.symm) (fun v => f v.1)).symm

section Mom
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)

/-- The momentum of the `K` row `v` of the engine datum is the decoration momentum at the first leaf of the pair of `v`. -/
theorem pairMom_eq {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (v : (assemblyShape hM9 B).VIdx) :
    rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inl v) =
      cosetDecoration G L base (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode :=
  (assembly_pair_momentum hM9 B hG W hL base β hβ x v).symm

/-- The momentum of the `ℒ` row `v` of the engine datum is the decoration momentum at the branch of `v`. -/
theorem branchMom_eq {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (v : (assemblyShape hM9 B).VIdx) :
    rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (Sum.inr v) =
      cosetDecoration G L base (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        (assemblyBranchOf hM9 B v).1.toNode :=
  (assembly_branch_momentum hM9 B hG W hL base β hβ x v).symm

/-- The slot of the first clock of row `ρ` (parent clock of the first leaf, resp. of the branch). -/
noncomputable def natSlot : (assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx → Fin 3 →
    (assemblyShape hM9 B).TVar ⊕ Fin 3
  | Sum.inl v => ![nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode,
      nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode,
      nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode]
  | Sum.inr v => ![nodeSlot hM9 B (assemblyBranchOf hM9 B v).1.toNode, Sum.inl (branchSlot hM9 B (assemblyBranchOf hM9 B v)),
      nodeSlot hM9 B (assemblyBranchOf hM9 B v).1.toNode]

variable (RD : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
  (hLayer : IsLayering (RD.garden hG) layer)

/-- **The native rows of the region as three-clock engine rows.** -/
noncomputable def natCR3 : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g') where
  W := fun ρ c _ k => match ρ with
    | Sum.inl v => VineEst.selCoupleRow L γ δ F RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 (c 0) (c 1) k
    | Sum.inr v => VineEst.selTreeRow L γ δ F RD hG layer hLayer (assemblyBranchOf hM9 B v).1 (c 0) (c 1) k
  slot := natSlot hM9 B hG
  W_indep := fun _ _ _ _ _ => rfl

theorem qRow_eq_natCR3 (base : Mom d) (X : GNode G.tree → (Fin d → ℤ)) (tt : Fin 3 → ℝ)
    (τ : (assemblyShape hM9 B).TVar → ℝ) (r : Mom d) (v : (assemblyShape hM9 B).VIdx) :
    qRow RD hG L γ δ F layer hLayer base (tt 0) X (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
        (assemblyPairOf hM9 B hG v).1 =
      (natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W (Sum.inl v)
        ((natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt (Sum.inl v)) r
        (cosetDecoration G L base X ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode) := by
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOf hM9 B hG v)
  have h1 := nodeSlot_spec hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).1 hp.1 tt τ
  have h2 := nodeSlot_spec hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).2 hp.2 tt τ
  simp only [qRow, natCR3, ClockedRows3.clock, natSlot, slotVal]
  rw [h1, h2]
  rfl

theorem tRow_eq_natCR3 (base : Mom d) (X : GNode G.tree → (Fin d → ℤ)) (tt : Fin 3 → ℝ)
    (τ : (assemblyShape hM9 B).TVar → ℝ) (r : Mom d) (v : (assemblyShape hM9 B).VIdx) :
    tRow RD hG L γ δ F layer hLayer base (tt 0) X (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
        (assemblyBranchOf hM9 B v).1 =
      (natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W (Sum.inr v)
        ((natCR3 hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).clock τ tt (Sum.inr v)) r
        (cosetDecoration G L base X (assemblyBranchOf hM9 B v).1.toNode) := by
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOf hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOf hM9 B v).2).2
  have h3 := nodeSlot_spec hM9 B _ hbr (interior_ne (assemblyBranchOf hM9 B v)) tt τ
  have h4 := branchSlot_spec hM9 B (assemblyBranchOf hM9 B v) tt τ
  simp only [tRow, natCR3, ClockedRows3.clock, natSlot, slotVal]
  rw [h3, h4]
  rfl

end Mom

end WaveTurbulence.VineEstS5C.P4.W2
