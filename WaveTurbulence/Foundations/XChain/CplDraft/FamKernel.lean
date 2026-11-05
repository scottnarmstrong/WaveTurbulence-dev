/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.FamIdentity
public import WaveTurbulence.Foundations.XChain.CoupleKernelTailExpansion
public import WaveTurbulence.Foundations.XChain.CoupleTruncatedOrderCarrier
public import WaveTurbulence.Foundations.XChain.CanonicalGraftTopCut

/-!
# CPL-2, step 3: the family kernel series is a garden sum

**Statements.** Let `𝒮 ⊆ truncatedTrees M`, and weight each couple `𝒬 ∈ 𝒞_{p+1}` (truncation `(M, N_p)`) by
`[∀ j, layerCutForest 𝒬 p j ∈ 𝒮]`, the indicator that its top trees lie in the family.
1. `famKernelExpansion_eq_finsum`: the family's kernel series (CPL step 2) is `∑ᶠ_𝒬 [tops ∈ 𝒮] K_𝒬`.
2. `famGarden_tail_eq`: the part of order `> Ncut` is INDUCT's order tail `lowerOrderTail`, summed over the
   forests of `𝒮`.
3. `famGarden_eq_sum_orders_add_tail`: the split into orders `≤ Ncut` and the tail.

**Proof.** Exactly INDUCT's couple expansion (`CoupleKernelExpansion`, `CoupleOrderKernelExpansion`,
`CoupleKernelTailExpansion`), with the weight carried through the graft bijection. INDUCT's
`canonicalGraftData_layerCutForest` says that the top trees of a graft are the data's tops.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset Induct SysAPI
open scoped Classical

variable {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)

theorem layerCutForest_expansionGraft {p M Natt : ℕ}
    (D : GraftExpansionData (![1, -1] : Fin 2 → ℤˣ) p M Natt) :
    layerCutForest D.toCanonical.graft p = fun j => (D.top j).1 :=
  canonicalGraftData_layerCutForest D.toCanonical

/-- **The family kernel series as a garden sum.** -/
theorem famKernelExpansion_eq_finsum {p : ℕ} (M Natt : ℕ) (𝒮 : Finset TTree) (t : ℝ)
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin 2 → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt},
      if ∀ j, layerCutForest LG.1 p j ∈ 𝒮 then KG L γ δ F LG.1 t n else 0) =
      famKernelExpansion L γ δ F ![1, -1] p M Natt 𝒮 t n := by
  rw [← sum_graftExpansionData_eq_source_couple p M Natt
    (fun LG => if ∀ j, layerCutForest LG p j ∈ 𝒮 then KG L γ δ F LG t n else 0)]
  rw [sum_graftExpansionData_eq_index ![1, -1] M Natt]
  unfold famKernelExpansion
  refine sum_congr rfl fun top _ => ?_
  by_cases h : ∀ j, (top j).1 ∈ 𝒮
  · rw [ite_eq_left h, mul_sum]
    refine sum_congr rfl fun P _ => ?_
    rw [sum_congr rfl fun low _ => ite_eq_left (by
      rw [layerCutForest_expansionGraft ⟨top, P.1, P.2, low⟩]; exact h)]
    exact sum_KG_graftLowerFamily L γ δ F ![1, -1] (fun j => (top j).1) P.1 P.2 t hpt htp n hF
  · rw [ite_eq_right h]
    exact sum_eq_zero fun P _ => sum_eq_zero fun low _ => ite_eq_right (by
      rw [layerCutForest_expansionGraft ⟨top, P.1, P.2, low⟩]; exact h)

/-- **The family tail** of order `> Ncut`. -/
theorem famGarden_tail_eq {p : ℕ} (M Natt : ℕ) (𝒮 : Finset TTree) (t : ℝ)
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin 2 → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) (Ncut : ℕ) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt},
      if Ncut < LG.1.garden.order then
        (if ∀ j, layerCutForest LG.1 p j ∈ 𝒮 then KG L γ δ F LG.1 t n else 0) else 0) =
      ∑ top : Fin 2 → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then
        (∏ j, zpowSign (![1, -1] j) (treePrefactor L γ δ d (top j).1)) *
          ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
              TopPartitionIrreducible (fun j => (top j).1) P},
            lowerOrderTail L γ δ F ![1, -1] (fun j => (top j).1) P.1 p Natt
              ((Ncut + 1) - ∑ j, (top j).1.order) t n
        else 0 := by
  rw [← sum_graftExpansionData_eq_source_couple p M Natt
    (fun LG => if Ncut < LG.garden.order then
      (if ∀ j, layerCutForest LG p j ∈ 𝒮 then KG L γ δ F LG t n else 0) else 0)]
  rw [sum_graftExpansionData_eq_index ![1, -1] M Natt]
  refine sum_congr rfl fun top _ => ?_
  by_cases h : ∀ j, (top j).1 ∈ 𝒮
  · rw [ite_eq_left h]
    have hw : ∀ D : GraftExpansionData (![1, -1] : Fin 2 → ℤˣ) p M Natt, (∀ j, (D.top j).1 ∈ 𝒮) →
        (if Ncut < D.toCanonical.graft.garden.order then
          (if ∀ j, layerCutForest D.toCanonical.graft p j ∈ 𝒮
            then KG L γ δ F D.toCanonical.graft t n else 0) else 0) =
        (if Ncut < D.toCanonical.graft.garden.order then (1 : ℂ) else 0) *
          KG L γ δ F D.toCanonical.graft t n := by
      intro D hD
      rw [ite_eq_left (show ∀ j, layerCutForest D.toCanonical.graft p j ∈ 𝒮 by
          rw [layerCutForest_expansionGraft D]; exact hD)]
      split_ifs <;> simp
    rw [mul_sum]
    refine sum_congr rfl fun P _ => ?_
    rw [sum_congr rfl fun low _ => hw ⟨top, P.1, P.2, low⟩ h]
    refine (sum_KG_graftLowerFamily_by_order L γ δ F ![1, -1] (fun j => (top j).1) P.1 P.2 t hpt htp n hF
      (fun N => if Ncut < N then 1 else 0)).trans ?_
    refine congrArg (fun z : ℂ => (∏ j, zpowSign (![1, -1] j) (treePrefactor L γ δ d (top j).1)) * z) ?_
    unfold lowerOrderTail lowerOrderTailIntegrand
    refine tsum_congr fun κ => ?_
    refine congrArg (fun z : ℂ =>
      (∏ j, topTreeCoefficient L γ δ p (fun j => (top j).1) ![1, -1] n κ (fun _ => t) j) * z) ?_
    refine sum_congr rfl fun orders _ => ?_
    have hiff : (Ncut < (∑ j, (top j).1.order) + ∑ B, (orders B).1) ↔
        (Ncut + 1) - (∑ j, (top j).1.order) ≤ ∑ B, (orders B).1 := by omega
    by_cases h' : Ncut < (∑ j, (top j).1.order) + ∑ B, (orders B).1
    · rw [ite_eq_left h', one_mul, ite_eq_left (hiff.mp h')]
    · rw [ite_eq_right h', zero_mul, ite_eq_right (fun hh => h' (hiff.mpr hh))]
  · rw [ite_eq_right h]
    refine sum_eq_zero fun P _ => sum_eq_zero fun low _ => ?_
    rw [ite_eq_right (show ¬ ∀ j, layerCutForest (GraftExpansionData.toCanonical
      ⟨top, P.1, P.2, low⟩).graft p j ∈ 𝒮 by
        rw [layerCutForest_expansionGraft ⟨top, P.1, P.2, low⟩]; exact h)]
    exact ite_self 0

/-- **The order split** of the weighted garden sum. -/
theorem famGarden_eq_sum_orders_add_tail (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p M Natt : ℕ)
    (𝒮 : Finset TTree) (Ncut : ℕ) (t : ℝ) (n : Fin 2 → (Fin P.d → ℤ)) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt},
      if ∀ j, layerCutForest LG.1 p j ∈ 𝒮 then KG P.L P.γ P.δ F LG.1 t n else 0) =
      (∑ N ∈ range (Ncut + 1), ∑ᶠ LG : {LG : LayeredGarden 2 //
          (IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt) ∧ LG.garden.order = N},
          if ∀ j, layerCutForest LG.1 p j ∈ 𝒮 then KG P.L P.γ P.δ F LG.1 t n else 0) +
        ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt},
          if Ncut < LG.1.garden.order then
            (if ∀ j, layerCutForest LG.1 p j ∈ 𝒮 then KG P.L P.γ P.δ F LG.1 t n else 0) else 0 := by
  let Q : LayeredGarden 2 → Prop := fun LG => IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt
  have hf : {LG : LayeredGarden 2 | Q LG}.Finite :=
    (finite_canonC_truncated p M Natt).subset (fun LG h => h)
  have : Finite {LG : LayeredGarden 2 // Q LG} := hf.to_subtype
  let : Fintype {LG : LayeredGarden 2 // Q LG} := Fintype.ofFinite _
  let g : LayeredGarden 2 → ℂ := fun LG =>
    if ∀ j, layerCutForest LG p j ∈ 𝒮 then KG P.L P.γ P.δ F LG t n else 0
  simp only [finsum_eq_sum_of_fintype]
  have he := sum_eq_sum_orders_add_tail (fun LG : {LG : LayeredGarden 2 // Q LG} => LG.1.garden.order)
    (fun LG => g LG.1) Ncut
  refine he.trans (congrArg (fun z : ℂ => z +
    ∑ LG : {LG : LayeredGarden 2 // Q LG}, if Ncut < LG.1.garden.order then g LG.1 else 0) ?_)
  exact sum_congr rfl fun N _ => sum_subtype_ite_order_eq_finsum Q (fun LG => LG.garden.order) g N

end WaveTurbulence.Cpl
