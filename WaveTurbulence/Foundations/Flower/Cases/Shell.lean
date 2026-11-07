/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Cases.Defs
public import WaveTurbulence.Foundations.XChain.ProductCut.ProdCut
/-! # Shell identities for the `M₂` cutoff weight, and `|stemFilter| ≤ 1`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Cases
open Finset

theorem stemFilter_abs_le_one {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (σ : Fin w → Option ℕ)
    (k : GNode LG.garden.tree → Mom d) : |stemFilter LG L σ k| ≤ 1 := by
  unfold stemFilter
  rw [abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => ?_
  cases σ j with
  | none => simp
  | some i => exact XChain.ProductCut.abs_prodDyadicCut_le_one _ _ _ _

theorem cutWeight2P_abs_le_one {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (j₂ : ℕ)
    (k : GNode LG.garden.tree → Mom d) : |LG.cutWeight2P L j₂ k| ≤ 1 := by
  unfold LayeredGarden.cutWeight2P
  rw [abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ =>
    XChain.ProductCut.abs_prodDyadicCut_le_one _ _ _ _

theorem cutWeight1P_abs_le_one {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (L : ℝ) (j₁ : ℕ)
    (k : GNode LG.garden.tree → Mom d) : |LG.cutWeight1P p L j₁ k| ≤ 1 := by
  unfold LayeredGarden.cutWeight1P
  rw [abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ =>
    XChain.ProductCut.abs_prodDyadicCut_le_one _ _ _ _

theorem stemFilter_none {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (k : GNode LG.garden.tree → Mom d) :
    stemFilter LG L (fun _ => none) k = 1 := by
  simp [stemFilter]

theorem cutWeight2P_zero {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (k : GNode LG.garden.tree → Mom d) :
    LG.cutWeight2P L 0 k = stemFilter LG L (fun _ => some 0) k := by
  unfold LayeredGarden.cutWeight2P stemFilter stemSet
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Option.elim, pow_zero, one_mul]

theorem cutWeight2P_expand {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (j₂ : ℕ)
    (k : GNode LG.garden.tree → Mom d) (hj : 0 < j₂) :
    LG.cutWeight2P L j₂ k = ∑ ε : Fin w → Bool, (∏ i, if ε i then (-1 : ℝ) else 1) *
      stemFilter LG L (fun i => some (if ε i then j₂ - 1 else j₂)) k := by
  have hne : j₂ ≠ 0 := hj.ne'
  have key : ∀ j : Fin w, prodDyadicCut L j₂ (stemSet LG j) (fun b => |omegaNode LG.garden k b|) =
      ∑ e : Bool, (if e then (-1 : ℝ) else 1) *
        prodDyadicCut (2 ^ (if e then j₂ - 1 else j₂) * L) 0 (stemSet LG j)
          (fun b => |omegaNode LG.garden k b|) := by
    intro j
    rw [Fintype.sum_bool]
    simp only [prodDyadicCut, hne, neg_mul, one_mul, Bool.false_eq_true, ↓reduceIte]
    ring
  unfold LayeredGarden.cutWeight2P
  have h2 : ∀ j : Fin w, prodDyadicCut L j₂ (Finset.univ.filter fun b : GBranch LG.garden.tree =>
      b.1.1 = j ∧ LG.OnStem b.toNode ∧ ¬ LG.garden.IsFlowerParent b) (fun b => |omegaNode LG.garden k b|) = _ :=
    key
  simp only [stemSet] at key
  rw [Finset.prod_congr rfl fun j _ => h2 j, Finset.prod_univ_sum]
  have : (Fintype.piFinset fun _ : Fin w => (Finset.univ : Finset Bool)) = Finset.univ := by
    ext; simp
  rw [this]
  refine Finset.sum_congr rfl fun ε _ => ?_
  unfold stemFilter
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Option.elim]

end WaveTurbulence.Flower.Cases
