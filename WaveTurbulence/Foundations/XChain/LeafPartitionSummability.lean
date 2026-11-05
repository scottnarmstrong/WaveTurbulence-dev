/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.PartitionCumulantSeries
public import WaveTurbulence.Foundations.XChain.LatticeMomentSeries
public import WaveTurbulence.Foundations.XChain.ForestLeafLabels
public import WaveTurbulence.Foundations.XChain.CumulantLinear
/-! Each irreducible-leaf-partition contribution is absolutely summable over actual decorations. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal

theorem summable_leaf_partition_cumulants {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (sig : GLeaf top → ℤˣ)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (P : Finpartition (univ : Finset (GLeaf top))) :
    Summable (fun κ : ForestDecoration top d n => ∏ B ∈ P.parts,
      cumulant μ (fun l ω => zpowSign (sig l) (c ω (κ.1 l.toNode))) B) := by
  classical
  let F := fun (l : GLeaf top) (m : Fin d → ℤ) (ω : Ω) => zpowSign (sig l) (c ω m)
  have hs := summable_partitionCumulantProduct μ F P (fun J _ =>
    summable_lattice_product_moments c hc hcs hM (fun l : ↥J => sig l.1))
  let e : ForestDecoration top d n → ((l : ↥(univ : Finset (GLeaf top))) → (Fin d → ℤ)) :=
    fun κ l => κ.1 l.1.toNode
  have he : Function.Injective e := by
    intro a b hab
    exact forestDecoration_eq_of_leaves top n a b (fun l => congrFun hab ⟨l, mem_univ l⟩)
  have hcomp := hs.comp_injective he
  apply hcomp.congr
  intro κ
  unfold partitionCumulantProduct
  rw [← prod_coe_sort P.parts (fun B => cumulant μ
    (fun l ω => zpowSign (sig l) (c ω (κ.1 l.toNode))) B)]
  apply prod_congr rfl
  intro B _
  apply cumulant_congr_on
  intro l hl ω
  exact dif_pos hl

end WaveTurbulence.Induct
