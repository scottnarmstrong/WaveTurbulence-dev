/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.FixedRoot
public import WaveTurbulence.Foundations.XChain.CplDraft.FamKernel
public import WaveTurbulence.Foundations.XChain.LowerFamilyKernelSum
public import WaveTurbulence.Foundations.XChain.CoupleKernelExpansion
public import WaveTurbulence.Foundations.XChain.GraftExpansionSums
public import WaveTurbulence.Foundations.XChain.PlainGraftEquality
public import WaveTurbulence.Foundations.XChain.CanonicalGraftKernel
public import WaveTurbulence.Foundations.XChain.UnmarkedPhaseIntegral
public import WaveTurbulence.Foundations.XChain.GraftAddresses

/-!
# CPL-3, step 6: the `∂_t` kernel series is a garden sum (roots held at `t`)

**Statements.**
1. `kernelKgen_rootsFixed_graft`: for a canonical graft whose top trees are not leaves, the kernel with both
   roots held at `t` is `∑'_κ (∏_j σ_j dtCoef_j(κ)) ∏_B K(lower garden B)`. This is `kernelKgen_graft` (graftgen)
   combined with `prefactor_mul_topGenFactor_roots`.
2. `sum_kernelKgen_rootsFixed_lowerFamily`: summed over the lower families, it is the generic kernel series
   `∑'_κ genKerIntegrand(dtCoef)`.
3. `famGenKernelExpansion_dt_eq_finsum`: for a family `𝒮` of non-leaf trees, the family's `∂_t` kernel series is
   `∑ᶠ_𝒬 [tops ∈ 𝒮] kernelKgen(𝒬; roots at t)` over `𝒬 ∈ 𝒞_{p+1}` with truncation `(M, N_p)`.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset Induct SysAPI
open scoped Classical

/-- The roots held at `t`, on any garden. -/
def rootFix {w : ℕ} {tree : Fin w → TTree} (t : ℝ) : GBranch tree → Option ℝ :=
  fun b => if b.1.2 = [] then some t else none

theorem ne_nil_of_mem_leaves {T : TTree} (hT : T ≠ .leaf) {q : TTree.Path} (hq : q ∈ T.leaves) : q ≠ [] := by
  cases T with
  | leaf => exact absurd rfl hT
  | node l m r =>
    rintro rfl
    simp [TTree.leaves, TTree.pre] at hq

section

variable (L γ δ : ℝ) {d w p : ℕ} {sig : Fin w → ℤˣ}

theorem kernelKgen_rootsFixed_graft (C : CanonicalGraftData sig p) (hnode : ∀ j, C.top j ≠ .leaf)
    (F : ℕ → Mom d → ℝ) {t : ℝ} (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    kernelKgen L γ δ F C.graft (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 =
      ∑' kt : ForestDecoration C.top d n,
        (∏ j, genTopCoef C.top sig (fun j => dtCoef L γ δ p t (C.top j)) kt j) *
          ∏ B : C.partition.parts, KG L γ δ F (C.low B) p
            (fun k => kt.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode) ∧
    Summable fun kt : ForestDecoration C.top d n =>
        (∏ j, genTopCoef C.top sig (fun j => dtCoef L γ δ p t (C.top j)) kt j) *
          ∏ B : C.partition.parts, KG L γ δ F (C.low B) p
            (fun k => kt.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode) := by
  have hF' : ∀ q, Summable fun m : Fin d → ℤ => |F q ((0 : Mom d) + latticePoint L m)| := by
    simpa only [zero_add] using hF
  have hn : ∀ B l, (C.low B).garden.mark l ≠ some MarkTag.lower := by
    intro B l he
    have hf := (C.plain B l).symm.trans he
    cases hf
  have he := markedLayeredGardenGraft_eq_layeredGardenGraft sig C.top C.partition C.low p C.plain C.sign
    C.layer_bound
  have hfixT : ∀ b, rootFix t (gardenBranchEquiv C.top C.partition (fun B => (C.low B).garden) (.inl b)) =
      fixRoots C.top t b := by
    intro b
    unfold rootFix fixRoots
    rw [gardenBranchEquiv_top_val]
  have hfixL : ∀ z, rootFix t (gardenBranchEquiv C.top C.partition (fun B => (C.low B).garden) (.inr z)) = none := by
    rintro ⟨B, a⟩
    unfold rootFix
    rw [gardenBranchEquiv_lower_val]
    have hl := ((blockRootEquiv C.top C.partition).symm ⟨B, a.1.1⟩).2
    have hne := ne_nil_of_mem_leaves (hnode _) hl
    simp [hne]
  have hfixv : ∀ b v, fixRoots C.top t b = some v → (p : ℝ) ≤ v := by
    intro b v h
    unfold fixRoots at h
    by_cases hb : b.1.2 = []
    · simp only [hb, ↓reduceIte, Option.some.injEq] at h
      exact h ▸ hpt
    · simp [hb] at h
  have hk := GraftGen.kernelKgen_graft L γ δ (hsig := C.sign) (hbound := C.layer_bound) F
    C.lower_branch_layer_lt hn (fun B => not_flowerParent_of_plain _ (C.plain B)) (rootFix t) (fixRoots C.top t)
    hfixT hfixL hfixv ∅ ∅ (fun _ => iff_of_false (notMem_empty _) (notMem_empty _)) (fun _ => notMem_empty _)
    (fun _ => 1) (by simp) t 0 hpt 0 n 0 hF'
  have hs := GraftGen.summable_kernelKgen_graft_series L γ δ (hsig := C.sign) (hbound := C.layer_bound) F
    C.lower_branch_layer_lt hn (fun B => not_flowerParent_of_plain _ (C.plain B)) (rootFix t) (fixRoots C.top t)
    hfixT hfixL hfixv ∅ ∅ (fun _ => iff_of_false (notMem_empty _) (notMem_empty _)) (fun _ => notMem_empty _)
    (fun _ => 1) (by simp) t 0 hpt 0 n 0 hF'
  have hpre (kt : ForestDecoration C.top d n) := prefactor_mul_topGenFactor_roots C.top L γ δ p sig hnode kt htp
  have hid : ∀ kt : ForestDecoration C.top d n,
      ((coupling d L γ δ : ℂ) ^ (∑ j, (C.top j).order) *
        ∏ b : GBranch C.top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
        (GraftGen.topGenFactor L γ δ sig C.top (fixRoots C.top t) ∅ (fun _ => 1) kt.1 0 p t *
          ∏ B : C.partition.parts, kernelK L γ δ F (C.low B) (fun _ => p) 0 0
            (fun k => kt.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode) 0) =
      (∏ j, genTopCoef C.top sig (fun j => dtCoef L γ δ p t (C.top j)) kt j) *
          ∏ B : C.partition.parts, KG L γ δ F (C.low B) p
            (fun k => kt.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode) := by
    intro kt
    rw [← mul_assoc, hpre kt]
    rfl
  refine ⟨?_, (hs.mul_left ((coupling d L γ δ : ℂ) ^ (∑ j, (C.top j).order) *
    ∏ b : GBranch C.top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ))).congr hid⟩
  refine (congrArg (fun LG : LayeredGarden w =>
    kernelKgen L γ δ F LG (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0) he).symm.trans ?_
  refine hk.trans ?_
  rw [← tsum_mul_left]
  exact tsum_congr hid

/-- **The lower-family sum** of the `∂_t` kernels. -/
theorem sum_kernelKgen_rootsFixed_lowerFamily {Natt : ℕ} (top : Fin w → TTree) (hnode : ∀ j, top j ≠ .leaf)
    (P : Finpartition (univ : Finset (GLeaf top))) (hP : TopPartitionIrreducible top P)
    (F : ℕ → Mom d → ℝ) {t : ℝ} (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    (∑ low : LowerFamily sig top P p Natt,
      kernelKgen L γ δ F (graftLowerFamily sig top P hP low).graft (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0) =
    ∑' κ : ForestDecoration top d n,
      genKerIntegrand L γ δ F sig top (fun j => dtCoef L γ δ p t (top j)) P p Natt n κ := by
  let c := fun κ : ForestDecoration top d n => ∏ j, genTopCoef top sig (fun j => dtCoef L γ δ p t (top j)) κ j
  let f := fun (low : LowerFamily sig top P p Natt) (κ : ForestDecoration top d n) =>
    c κ * ∏ B : P.parts, KG L γ δ F (low B).low p
      (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
  have hk (low : LowerFamily sig top P p Natt) :
      kernelKgen L γ δ F (graftLowerFamily sig top P hP low).graft (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 =
        ∑' κ, f low κ ∧ Summable (f low) :=
    kernelKgen_rootsFixed_graft L γ δ (graftLowerFamily sig top P hP low) hnode F hpt htp n hF
  rw [sum_congr rfl fun low _ => (hk low).1, ← Summable.tsum_finsetSum (fun low _ => (hk low).2)]
  refine tsum_congr fun κ => ?_
  change (∑ low : LowerFamily sig top P p Natt, c κ * ∏ B : P.parts,
    KG L γ δ F (low B).low p (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) = _
  rw [← mul_sum]
  unfold genKerIntegrand
  apply congrArg (fun z : ℂ => c κ * z)
  have hp := tsum_independent_prod (fun (B : P.parts) (D : LowerGraftData
      (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt) =>
    KG L γ δ F D.low p (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode))
  simpa only [tsum_fintype, lowerKernelSum, topBlockKernel] using hp

/-- **The family's `∂_t` kernel series as a garden sum.** -/
theorem famGenKernelExpansion_dt_eq_finsum (M Natt : ℕ) (𝒮 : Finset TTree) (h𝒮 : ∀ T ∈ 𝒮, T ≠ .leaf)
    (F : ℕ → Mom d → ℝ) {t : ℝ} (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin 2 → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p M Natt},
      if ∀ j, layerCutForest LG.1 p j ∈ 𝒮 then
        kernelKgen L γ δ F LG.1 (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 else 0) =
      famGenKernelExpansion L γ δ F ![1, -1] p M Natt 𝒮 (dtCoef L γ δ p t) n := by
  rw [← sum_graftExpansionData_eq_source_couple p M Natt
    (fun LG => if ∀ j, layerCutForest LG p j ∈ 𝒮 then
      kernelKgen L γ δ F LG (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 n 0 else 0)]
  rw [sum_graftExpansionData_eq_index ![1, -1] M Natt]
  unfold famGenKernelExpansion
  refine sum_congr rfl fun top _ => ?_
  by_cases h : ∀ j, (top j).1 ∈ 𝒮
  · rw [ite_eq_left h]
    refine sum_congr rfl fun P _ => ?_
    rw [sum_congr rfl fun low _ => ite_eq_left (by
      rw [layerCutForest_expansionGraft ⟨top, P.1, P.2, low⟩]; exact h)]
    exact sum_kernelKgen_rootsFixed_lowerFamily L γ δ (fun j => (top j).1) (fun j => h𝒮 _ (h j)) P.1 P.2 F hpt
      htp n hF
  · rw [ite_eq_right h]
    exact sum_eq_zero fun P _ => sum_eq_zero fun low _ => ite_eq_right (by
      rw [layerCutForest_expansionGraft ⟨top, P.1, P.2, low⟩]; exact h)

end

end WaveTurbulence.Cpl
