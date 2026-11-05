/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestDecorationEquiv
public import WaveTurbulence.Foundations.XChain.TopTreeLeafProducts
public import WaveTurbulence.Foundations.XChain.TopPartitionExpansion
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
/-! The actual signed tree summands have precisely the source irreducible leaf-partition expansion. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped Classical

noncomputable def topTreeCoefficient {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (t : Fin w → ℝ) (j : Fin w) : ℂ :=
  zpowSign (sig j) (epsProd (top j) (forestDecorationEquiv top n κ j).1 *
    timeInt L γ δ (top j) (forestDecorationEquiv top n κ j).1 p (t j))

theorem signed_treeSummand_eq_leafGroup {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (t : Fin w → ℝ) (c : (Fin d → ℤ) → ℂ) (j : Fin w) :
    zpowSign (sig j) (treeSummand L γ δ p (top j) c (t j) (n j) (forestDecorationEquiv top n κ j)) =
      topTreeCoefficient L γ δ p top sig n κ t j *
        ∏ l ∈ topLeafGroups top j, zpowSign (nodeSign sig l.1) (c (κ.1 l.toNode)) := by
  rw [treeSummand_eq, zpowSign_mul]
  apply congrArg (fun z : ℂ => topTreeCoefficient L γ δ p top sig n κ t j * z)
  unfold leafProd
  rw [zpowSign_prod]
  have he : (∏ l : GLeaf (single (top j)), zpowSign (sig j)
      (zpowSign (treeSign (top j) l.toNode) (c ((forestDecorationEquiv top n κ j).1 l.toNode)))) =
      ∏ l : GLeaf (single (top j)),
        zpowSign (nodeSign sig (singleLeafToForest top j l).1) (c (κ.1 (singleLeafToForest top j l).toNode)) := by
    apply prod_congr rfl
    intro l _
    rw [zpowSign_comp, nodeSign_single_mul]
    rfl
  exact he.trans (prod_singleLeaf_eq_group top j
    (fun l => zpowSign (nodeSign sig l.1) (c (κ.1 l.toNode))))

theorem cumulant_treeSummands_eq_irreduciblePartitions {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (t : Fin w → ℝ) (c : Ω → (Fin d → ℤ) → ℂ) :
    cumulant μ (fun j ω => zpowSign (sig j)
      (treeSummand L γ δ p (top j) (c ω) (t j) (n j) (forestDecorationEquiv top n κ j))) univ =
      (∏ j, topTreeCoefficient L γ δ p top sig n κ t j) *
        ∑ P ∈ (univ : Finset (Finpartition (univ : Finset (GLeaf top)))).filter
          (TopPartitionIrreducible top),
          ∏ B ∈ P.parts, cumulant μ (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B := by
  have he : (fun j ω => zpowSign (sig j)
      (treeSummand L γ δ p (top j) (c ω) (t j) (n j) (forestDecorationEquiv top n κ j))) =
      fun j ω => topTreeCoefficient L γ δ p top sig n κ t j *
        ∏ l ∈ topLeafGroups top j, zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode)) := by
    funext j ω
    exact signed_treeSummand_eq_leafGroup L γ δ p top sig n κ t (c ω) j
  rw [he, cumulant_mul, cumulant_top_leaf_groups]

end WaveTurbulence.Induct
