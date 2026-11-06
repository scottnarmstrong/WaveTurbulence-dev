/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.TopSplit

/-!
# X2E-3, step 2: the top factor of a flower forest

For non-trivial flower trees `tops`, a pattern `pat`, `†` labels, cutoffs, and times `p ≤ s, t ≤ p + 1`:
- `fixFl`: the designated top times (each flower parent `↦ s`; for `dRoot`, each root `↦ t`), tree by tree X3's
  `treeFixPat`;
- `offFl`: the removed phases (the flower parents, if `†`);
- `wtopFl`: the top weight (cutoffs and sibling labels) on real decorations, tree by tree X2's `treeWeight`.

**Statement** (`prefactor_mul_topGenFactor_flower`). The garden prefactor times graftgen's top factor
`topGenFactor` with these data is `∏_j σ_j fkCoef_j(κ_j)`, the product of the signed coefficients of X2E-1.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped Classical

/-! ## The tree weight on real decorations -/

section Weight

variable (L : ℝ) {d : ℕ}

/-- `treeCut1` on real decorations. -/
noncomputable def treeCut1K (F : FTree) (j₁ : ℕ) (k : GNode (single F.toTree) → Mom d) : ℝ :=
  prodDyadicCut L j₁ (univ.erase F.flowerLeaf) (fun ℓ => ‖k ℓ.toNode‖)

/-- `treeCut2` on real decorations. -/
noncomputable def treeCut2K (F : FTree) (hF : F ≠ FTree.flower) (j₂ : ℕ) (k : GNode (single F.toTree) → Mom d) :
    ℝ :=
  prodDyadicCut L j₂ (univ.filter fun b : GBranch (single F.toTree) => OnStemT F b ∧ b ≠ F.flowerParent hF)
    (fun b => |resFactor (k (b.child 0)) (k (b.child 1)) (k (b.child 2)) (k b.toNode)|)

/-- `treeSib` on real decorations. -/
noncomputable def treeSibK (F : FTree) (hF : F ≠ FTree.flower) (c : Fin 3 → Mom d)
    (k : GNode (single F.toTree) → Mom d) : ℝ :=
  ∏ i : Fin 3, if ((F.flowerParent hF).child i).1.2 = F.flowerPath then 1 else
    if k ((F.flowerParent hF).child i) = c i then 1 else 0

/-- `treeWeight` on real decorations. -/
noncomputable def treeWeightK (F : FTree) (hF : F ≠ FTree.flower) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (k : GNode (single F.toTree) → Mom d) : ℝ :=
  (cut1.elim 1 fun j₁ => treeCut1K L F j₁ k) * (cut2.elim 1 fun j₂ => treeCut2K L F hF j₂ k) *
    (dagger.elim 1 fun c => treeSibK F hF c k)

theorem treeWeightK_lattice (F : FTree) (hF : F ≠ FTree.flower) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    treeWeightK L F hF dagger cut1 cut2 (fun a => latticePoint L (κ a)) = treeWeight L F hF dagger cut1 cut2 κ := rfl

end Weight

/-! ## The top data -/

section TopData

variable {w : ℕ} (tops : Fin w → FTree) (hF : ∀ j, tops j ≠ FTree.flower)

/-- The branch of tree `j` in the single tree. -/
def toSingle (b : GBranch (ftop tops)) : GBranch (single (tops b.1.1).toTree) := ⟨(0, b.1.2), b.2⟩

theorem toSingle_single (j : Fin w) (b : GBranch (single (tops j).toTree)) :
    toSingle tops (singleBranchToForest (ftop tops) j b) = b :=
  Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)

/-- The designated top times. -/
noncomputable def fixFl (pat : FixPat) (t s : ℝ) (b : GBranch (ftop tops)) : Option ℝ :=
  treeFixPat (tops b.1.1) (hF b.1.1) pat t s (toSingle tops b)

/-- The removed top phases. -/
noncomputable def offFl {d : ℕ} (dagger : Option (Fin 3 → Mom d)) : Finset (GBranch (ftop tops)) :=
  if dagger.isSome then univ.filter fun b => b.1.2 = ((tops b.1.1).flowerParent (hF b.1.1)).1.2 else ∅

/-- The top weight. -/
noncomputable def wtopFl (L : ℝ) {d : ℕ} (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (k : GNode (ftop tops) → Mom d) : ℝ :=
  ∏ j, treeWeightK L (tops j) (hF j) dagger cut1 cut2 (fun a => k (singleNodeToForest (ftop tops) j a))

theorem treeFix_fixFl (pat : FixPat) (t s : ℝ) (j : Fin w) :
    treeFix (ftop tops) (fixFl tops hF pat t s) j = treeFixPat (tops j) (hF j) pat t s := by
  funext b
  exact congrArg (treeFixPat (tops j) (hF j) pat t s) (toSingle_single tops j b)

theorem mem_offFl {d : ℕ} (dagger : Option (Fin 3 → Mom d)) (b : GBranch (ftop tops)) :
    b ∈ offFl tops hF dagger ↔ dagger.isSome ∧ b.1.2 = ((tops b.1.1).flowerParent (hF b.1.1)).1.2 := by
  unfold offFl
  by_cases h : dagger.isSome <;> simp [h]

theorem mem_treeOff_offFl {d : ℕ} (dagger : Option (Fin 3 → Mom d)) (j : Fin w)
    (c : GBranch (single (tops j).toTree)) :
    c ∈ treeOff (ftop tops) (offFl tops hF dagger) j ↔ dagger.isSome ∧ c = (tops j).flowerParent (hF j) := by
  rw [mem_treeOff, mem_offFl]
  constructor
  · rintro ⟨h, hc⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    apply Prod.ext (Subsingleton.elim _ _)
    exact hc
  · rintro ⟨h, rfl⟩
    exact ⟨h, rfl⟩

end TopData

/-! ## The top factor -/

section Factor

variable (L γ δ : ℝ) {d w : ℕ} (p : ℕ) (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
  (t s : ℝ) (tops : Fin w → FTree) (hF : ∀ j, tops j ≠ FTree.flower) (sig : Fin w → ℤˣ)

theorem treeFixIntegral_congr_off {T : TTree} (fix : GBranch (single T) → Option ℝ)
    {off₁ off₂ : Finset (GBranch (single T))} (h : ∀ c, c ∈ off₁ ↔ c ∈ off₂) (κ : GNode (single T) → (Fin d → ℤ))
    (t : ℝ) : treeFixIntegral L γ δ p T fix off₁ κ t = treeFixIntegral L γ δ p T fix off₂ κ t := by
  have he : off₁ = off₂ := Finset.ext h
  rw [he]

theorem mem_ite_singleton {α : Type*} (c a : α) (b : Bool) :
    c ∈ (if b then ({a} : Finset α) else ∅) ↔ b ∧ c = a := by
  split_ifs with h <;> simp [h]

theorem zpowSign_ofReal (σ : ℤˣ) (r : ℝ) : zpowSign σ (r : ℂ) = r := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact Complex.conj_ofReal r

/-- **The flower top factor** is the product of the signed flower coefficients. -/
theorem prefactor_mul_topGenFactor_flower {n : Fin w → (Fin d → ℤ)} (kt : ForestDecoration (ftop tops) d n) :
    ((coupling d L γ δ : ℂ) ^ (∑ j, (ftop tops j).order) *
        ∏ b : GBranch (ftop tops), Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
      GraftGen.topGenFactor L γ δ sig (ftop tops) (fixFl tops hF pat t s) (offFl tops hF dagger)
        (wtopFl tops hF L dagger cut1 cut2) kt.1 0 p t =
    ∏ j, zpowSign (sig j) (fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j)
      (fun a => kt.1 (singleNodeToForest (ftop tops) j a))) := by
  have hj : ∀ j, zpowSign (sig j) (fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j)
      (fun a => kt.1 (singleNodeToForest (ftop tops) j a))) =
      zpowSign (sig j) (treePrefactor L γ δ d (ftop tops j)) *
        (epsProd (ftop tops j) (fun a => kt.1 (singleNodeToForest (ftop tops) j a)) *
          ((treeWeight L (tops j) (hF j) dagger cut1 cut2
            (fun a => kt.1 (singleNodeToForest (ftop tops) j a)) : ℝ) : ℂ) *
          zpowSign (sig j) (treeFixIntegral L γ δ p (ftop tops j) (treeFix (ftop tops) (fixFl tops hF pat t s) j)
            (treeOff (ftop tops) (offFl tops hF dagger) j)
            (fun a => kt.1 (singleNodeToForest (ftop tops) j a)) t)) := by
    intro j
    unfold fkCoef
    rw [dite_eq_right (hF j), zpowSign_mul, zpowSign_mul, zpowSign_mul, zpowSign_epsProd, zpowSign_ofReal,
      treeFix_fixFl, treeFixIntegral_congr_off L γ δ p (T := ftop tops j) _
        (off₂ := if dagger.isSome then {(tops j).flowerParent (hF j)} else ∅)
        (fun c => (mem_treeOff_offFl tops hF dagger j c).trans
          (mem_ite_singleton c ((tops j).flowerParent (hF j)) dagger.isSome).symm)]
    rfl
  rw [← prod_signed_treePrefactor_eq L γ δ (ftop tops) sig, prod_congr rfl fun j _ => hj j]
  unfold GraftGen.topGenFactor
  rw [forest_epsProd_eq_roots (ftop tops) kt.1, topFixIntegral_eq_prod L γ δ sig (ftop tops)]
  simp only [single_topFixIntegral_eq]
  simp only [zero_add]
  have hw : (wtopFl tops hF L dagger cut1 cut2 (fun a => latticePoint L (kt.1 a)) : ℂ) =
      ∏ j, ((treeWeight L (tops j) (hF j) dagger cut1 cut2
        (fun a => kt.1 (singleNodeToForest (ftop tops) j a)) : ℝ) : ℂ) := by
    unfold wtopFl
    rw [Complex.ofReal_prod]
    rfl
  rw [hw]
  simp only [prod_mul_distrib]

end Factor

end WaveTurbulence.X2E
