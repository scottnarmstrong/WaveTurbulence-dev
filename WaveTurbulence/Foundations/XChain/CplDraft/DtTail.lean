/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.DtKind
public import WaveTurbulence.Foundations.XChain.LowerFamilyOrderKernel
public import WaveTurbulence.Foundations.XChain.LowerOrderTail
public import WaveTurbulence.Foundations.XChain.GardenGraftOrder
public import WaveTurbulence.Foundations.XChain.FiniteOrderCutoff
public import WaveTurbulence.Foundations.XChain.FiniteSubtypeOrderSum
public import WaveTurbulence.Foundations.XChain.TruncatedGraftFinite

/-!
# CPL-3, step 8: the order split and the tail of the `∂_t` garden sum

**Statements.**
1. `gardenSum_eq_sum_orders_add_tail`: the order split of a garden sum over `𝒞_{p+1}` with truncation `(M, Natt)`,
   for any summand. This is `famGarden_eq_sum_orders_add_tail` (FamKernel) with the kernel left general.
2. `sum_kernelKgen_rootsFixed_lowerFamily_by_order`: the lower-family sum of the root-fixed kernels, weighted by
   a function of the order. It is the generic series whose lower factor is split by the orders of the lower
   gardens (INDUCT's `sum_lowerFamily_by_orders`).
3. `genOrderTail`: the generic order tail `∑'_κ ∏_j σ_j coef_j(κ) ∑_{orders, ∑ ≥ J} ∏_B K_{orders B}`, the
   analogue of INDUCT's `lowerOrderTail` with the top coefficient left general.
4. `famGenGarden_dt_tail_eq`: the tail of order `> Ncut` of the root-fixed garden sum is the sum of the generic
   order tails, with `J = Ncut + 1 − ∑_j n(𝒯_j)`.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset Induct SysAPI
open scoped Classical

/-- **The order split** of a garden sum, for any summand. -/
theorem gardenSum_eq_sum_orders_add_tail (p M Natt : ℕ) (g : LayeredGarden 2 → ℂ) (Ncut : ℕ) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt}, g LG.1) =
      (∑ N ∈ range (Ncut + 1), ∑ᶠ LG : {LG : LayeredGarden 2 //
          (IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt) ∧ LG.garden.order = N}, g LG.1) +
        ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt},
          if Ncut < LG.1.garden.order then g LG.1 else 0 := by
  let Q : LayeredGarden 2 → Prop := fun LG => IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt
  have hf : {LG : LayeredGarden 2 | Q LG}.Finite :=
    (finite_canonC_truncated p M Natt).subset (fun LG h => h)
  have : Finite {LG : LayeredGarden 2 // Q LG} := hf.to_subtype
  let : Fintype {LG : LayeredGarden 2 // Q LG} := Fintype.ofFinite _
  simp only [finsum_eq_sum_of_fintype]
  have he := sum_eq_sum_orders_add_tail (fun LG : {LG : LayeredGarden 2 // Q LG} => LG.1.garden.order)
    (fun LG => g LG.1) Ncut
  refine he.trans (congrArg (fun z : ℂ => z +
    ∑ LG : {LG : LayeredGarden 2 // Q LG}, if Ncut < LG.1.garden.order then g LG.1 else 0) ?_)
  exact sum_congr rfl fun N _ => sum_subtype_ite_order_eq_finsum Q (fun LG => LG.garden.order) g N

section

variable (L γ δ : ℝ) {d w p : ℕ}

/-- The generic order-tail integrand: `∏_j σ_j coef_j(κ)` times the lower-order kernels of total order `≥ J`. -/
noncomputable def genOrderTailIntegrand (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (coef : (j : Fin w) → TreeCoef d (top j)) (P : Finpartition (univ : Finset (GLeaf top))) (p Natt J : ℕ)
    (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) : ℂ :=
  (∏ j, genTopCoef top sig coef κ j) *
    ∑ orders : P.parts → Fin (Natt + 1),
      if J ≤ ∑ B, (orders B).1 then
        ∏ B : P.parts, lowerOrderKernelSum L γ δ F
          (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt (orders B)
          (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
      else 0

/-- **The generic order tail.** -/
noncomputable def genOrderTail (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (coef : (j : Fin w) → TreeCoef d (top j)) (P : Finpartition (univ : Finset (GLeaf top))) (p Natt J : ℕ)
    (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑' κ : ForestDecoration top d n, genOrderTailIntegrand L γ δ F sig top coef P p Natt J n κ

variable {sig : Fin w → ℤˣ}

/-- **The lower-family sum of the root-fixed kernels, by order.** -/
theorem sum_kernelKgen_rootsFixed_lowerFamily_by_order {Natt : ℕ} (top : Fin w → TTree)
    (hnode : ∀ j, top j ≠ .leaf) (P : Finpartition (univ : Finset (GLeaf top)))
    (hP : TopPartitionIrreducible top P) (F : ℕ → Mom d → ℝ) {t : ℝ} (hpt : (p : ℝ) ≤ t)
    (htp : t ≤ (p : ℝ) + 1) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) (W : ℕ → ℂ) :
    (∑ low : LowerFamily sig top P p Natt,
      W (graftLowerFamily sig top P hP low).graft.garden.order *
        kernelKgen L γ δ F (graftLowerFamily sig top P hP low).graft (rootFix t) ∅ (fun _ => 1) (fun _ => t)
          0 n 0) =
    ∑' κ : ForestDecoration top d n,
      (∏ j, genTopCoef top sig (fun j => dtCoef L γ δ p t (top j)) κ j) *
        ∑ orders : P.parts → Fin (Natt + 1),
          W ((∑ j, (top j).order) + ∑ B, (orders B).1) *
            ∏ B : P.parts, lowerOrderKernelSum L γ δ F
              (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt (orders B)
              (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) := by
  let c := fun κ : ForestDecoration top d n => ∏ j, genTopCoef top sig (fun j => dtCoef L γ δ p t (top j)) κ j
  let u := fun low : LowerFamily sig top P p Natt => (graftLowerFamily sig top P hP low).graft.garden.order
  let f := fun (low : LowerFamily sig top P p Natt) (κ : ForestDecoration top d n) =>
    c κ * ∏ B : P.parts, KG L γ δ F (low B).low p
      (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
  have ho (low : LowerFamily sig top P p Natt) :
      u low = (∑ j, (top j).order) + ∑ B : P.parts, (low B).low.garden.order :=
    gardenGraft_order sig top P (fun B => (low B).low.garden)
      (fun B => (low B).plain) (fun B k => congrFun (low B).sign k)
  have hk (low : LowerFamily sig top P p Natt) :
      kernelKgen L γ δ F (graftLowerFamily sig top P hP low).graft (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 =
        ∑' κ, f low κ ∧ Summable (f low) :=
    kernelKgen_rootsFixed_graft L γ δ (graftLowerFamily sig top P hP low) hnode F hpt htp n hF
  have he : (∑ low : LowerFamily sig top P p Natt, W (u low) *
      kernelKgen L γ δ F (graftLowerFamily sig top P hP low).graft (rootFix t) ∅ (fun _ => 1) (fun _ => t)
        0 n 0) = ∑ low, ∑' κ, W (u low) * f low κ := by
    refine sum_congr rfl fun low _ => ?_
    rw [(hk low).1, ← tsum_mul_left]
  refine he.trans ?_
  rw [← Summable.tsum_finsetSum (fun low _ => (hk low).2.mul_left (W (u low)))]
  refine tsum_congr fun κ => ?_
  change (∑ low : LowerFamily sig top P p Natt, W (u low) * (c κ * ∏ B : P.parts,
    KG L γ δ F (low B).low p (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode))) = _
  have hcomm : ∀ low : LowerFamily sig top P p Natt, W (u low) * (c κ * ∏ B : P.parts,
      KG L γ δ F (low B).low p (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) =
      c κ * (W (u low) * ∏ B : P.parts,
        KG L γ δ F (low B).low p (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) :=
    fun _ => by ring
  rw [sum_congr rfl fun low _ => hcomm low, ← mul_sum]
  apply congrArg (fun z : ℂ => c κ * z)
  simp_rw [ho]
  exact sum_lowerFamily_by_orders L γ δ F sig top P κ
    (fun orders => W ((∑ j, (top j).order) + ∑ B, (orders B).1))

end

section

variable (L γ δ : ℝ) {d : ℕ} (F : ℕ → Mom d → ℝ)

/-- **The tail of the root-fixed garden sum.** -/
theorem famGenGarden_dt_tail_eq {p : ℕ} (M Natt : ℕ) (𝒮 : Finset TTree) (h𝒮 : ∀ T ∈ 𝒮, T ≠ .leaf) {t : ℝ}
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin 2 → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) (Ncut : ℕ) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt},
      if Ncut < LG.1.garden.order then
        (if ∀ j, layerCutForest LG.1 p j ∈ 𝒮 then
          kernelKgen L γ δ F LG.1 (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 else 0) else 0) =
      ∑ top : Fin 2 → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then
        ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
            TopPartitionIrreducible (fun j => (top j).1) P},
          genOrderTail L γ δ F ![1, -1] (fun j => (top j).1) (fun j => dtCoef L γ δ p t (top j).1) P.1 p Natt
            ((Ncut + 1) - ∑ j, (top j).1.order) n
        else 0 := by
  rw [← sum_graftExpansionData_eq_source_couple p M Natt
    (fun LG => if Ncut < LG.garden.order then
      (if ∀ j, layerCutForest LG p j ∈ 𝒮 then
        kernelKgen L γ δ F LG (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 else 0) else 0)]
  rw [sum_graftExpansionData_eq_index ![1, -1] M Natt]
  refine sum_congr rfl fun top _ => ?_
  by_cases h : ∀ j, (top j).1 ∈ 𝒮
  · rw [ite_eq_left h]
    have hw : ∀ D : GraftExpansionData (![1, -1] : Fin 2 → ℤˣ) p M Natt, (∀ j, (D.top j).1 ∈ 𝒮) →
        (if Ncut < D.toCanonical.graft.garden.order then
          (if ∀ j, layerCutForest D.toCanonical.graft p j ∈ 𝒮
            then kernelKgen L γ δ F D.toCanonical.graft (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 else 0)
          else 0) =
        (if Ncut < D.toCanonical.graft.garden.order then (1 : ℂ) else 0) *
          kernelKgen L γ δ F D.toCanonical.graft (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 := by
      intro D hD
      rw [ite_eq_left (show ∀ j, layerCutForest D.toCanonical.graft p j ∈ 𝒮 by
          rw [layerCutForest_expansionGraft D]; exact hD)]
      split_ifs <;> simp
    refine sum_congr rfl fun P _ => ?_
    rw [sum_congr rfl fun low _ => hw ⟨top, P.1, P.2, low⟩ h]
    refine (sum_kernelKgen_rootsFixed_lowerFamily_by_order L γ δ (sig := ![1, -1]) (fun j => (top j).1)
      (fun j => h𝒮 _ (h j)) P.1 P.2 F hpt htp n hF (fun N => if Ncut < N then 1 else 0)).trans ?_
    unfold genOrderTail genOrderTailIntegrand
    refine tsum_congr fun κ => ?_
    refine congrArg (fun z : ℂ =>
      (∏ j, genTopCoef (fun j => (top j).1) ![1, -1] (fun j => dtCoef L γ δ p t (top j).1) κ j) * z) ?_
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

end

end WaveTurbulence.Cpl
