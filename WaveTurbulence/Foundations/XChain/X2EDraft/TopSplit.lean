/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerGraftEquiv
public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerFamily
public import WaveTurbulence.Foundations.XChain.GraftGenDraft.KernelGenSeries
public import WaveTurbulence.Foundations.XChain.ForestRootTimes
public import WaveTurbulence.Foundations.XChain.ForestRootEpsilon
public import WaveTurbulence.Foundations.XChain.ForestRootPrefactor

/-!
# X2E-3, step 1: the top integral with designated times, tree by tree

**Statements.**
1. `topFixIntegral_eq_prod`: the top-forest integral of graftgen (`topFixIntegral`: designated times `fix`, removed
   phases `off`) is the product over the trees of the single-tree integrals with the restricted data. The free time
   coordinates split by tree (`freeTimeSplit`, measure preserving: INDUCT's `finiteTimeCurry` pattern of
   `forestRootTimeSplit`), and so do the domain, the phases and the indicator.
2. `single_topFixIntegral_eq`: for one tree of sign `σ`, the integral is `σ`-conjugate of the tree integral
   `treeFixIntegral` in X2/X3's form (`treeDomFix`, `phaseOffT`, `extendFixT`); with the designated times of a
   flower pattern this is X3's `TIpat`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped Classical

/-! ## Free coordinates by tree -/

section Split

variable {w : ℕ} (top : Fin w → TTree) (fix : GBranch top → Option ℝ)

/-- The designated times of tree `j`. -/
noncomputable def treeFix (j : Fin w) : GBranch (single (top j)) → Option ℝ :=
  fun b => fix (singleBranchToForest top j b)

/-- The free branches, by tree. -/
noncomputable def freeSplitEquiv :
    {b : GBranch top // fix b = none} ≃ Σ j, {b : GBranch (single (top j)) // treeFix top fix j b = none} where
  toFun b := ⟨b.1.1.1, ⟨⟨(0, b.1.1.2), b.1.2⟩, b.2⟩⟩
  invFun x := ⟨singleBranchToForest top x.1 x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨j, ⟨⟨⟨i, q⟩, hq⟩, h⟩⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rfl

/-- The free time coordinates, by tree. -/
noncomputable def freeTimeSplit :
    ({b : GBranch top // fix b = none} → ℝ) ≃ᵐ
      ((j : Fin w) → {b : GBranch (single (top j)) // treeFix top fix j b = none} → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : {b : GBranch top // fix b = none} => ℝ)
    (freeSplitEquiv top fix).symm).symm.trans
    (finiteTimeCurry (fun j => {b : GBranch (single (top j)) // treeFix top fix j b = none}))

theorem measurePreserving_freeTimeSplit : MeasurePreserving (freeTimeSplit top fix) volume volume :=
  ((measurePreserving_piCongrLeft (fun _ : {b : GBranch top // fix b = none} => (volume : Measure ℝ))
    (freeSplitEquiv top fix).symm).symm).trans
      (measurePreserving_finiteTimeCurry (fun j => {b : GBranch (single (top j)) // treeFix top fix j b = none}))

theorem integral_free_prod (f : (j : Fin w) → ({b : GBranch (single (top j)) // treeFix top fix j b = none} → ℝ) → ℂ) :
    (∫ τ : {b : GBranch top // fix b = none} → ℝ,
      ∏ j, f j (fun b => τ ⟨singleBranchToForest top j b.1, b.2⟩)) = ∏ j, ∫ τ, f j τ := by
  have he : (fun τ : {b : GBranch top // fix b = none} → ℝ =>
      ∏ j, f j (fun b => τ ⟨singleBranchToForest top j b.1, b.2⟩)) =
      fun τ => ∏ j, f j (freeTimeSplit top fix τ j) := rfl
  rw [he]
  exact ((measurePreserving_freeTimeSplit top fix).integral_comp' (fun z => ∏ j, f j (z j))).trans
    (integral_fintype_prod_volume_eq_prod f)

theorem extendFixF_single (τ : {b : GBranch top // fix b = none} → ℝ) (j : Fin w) (b : GBranch (single (top j))) :
    GraftGen.extendFixF (single (top j)) (treeFix top fix j)
      (fun c => τ ⟨singleBranchToForest top j c.1, c.2⟩) b =
      GraftGen.extendFixF top fix τ (singleBranchToForest top j b) := by
  unfold GraftGen.extendFixF treeFix
  split <;> rfl

theorem extendFixF_single' (τ : {b : GBranch top // fix b = none} → ℝ) (j : Fin w) :
    GraftGen.extendFixF (single (top j)) (treeFix top fix j) (fun c => τ ⟨singleBranchToForest top j c.1, c.2⟩) =
      fun b => GraftGen.extendFixF top fix τ (singleBranchToForest top j b) :=
  funext (extendFixF_single top fix τ j)

theorem topDomFix_iff (p t : ℝ) (x : GBranch top → ℝ) :
    x ∈ GraftGen.topDomFix top p t fix ↔
      ∀ j, (fun b => x (singleBranchToForest top j b)) ∈
        GraftGen.topDomFix (single (top j)) p t (treeFix top fix j) := by
  constructor
  · intro h j b
    have hb := h (singleBranchToForest top j b)
    exact ⟨hb.1, fun b' hc => hb.2 (singleBranchToForest top j b') ⟨rfl, hc.2⟩⟩
  · intro h b
    let c : GBranch (single (top b.1.1)) := ⟨(0, b.1.2), b.2⟩
    have hb := h b.1.1 c
    refine ⟨hb.1, ?_⟩
    intro b' hc
    have hm : b'.1.2 ∈ (top b.1.1).branching :=
      (congrArg (fun j => b'.1.2 ∈ (top j).branching) hc.1).mp b'.2
    let c' : GBranch (single (top b.1.1)) := ⟨(0, b'.1.2), hm⟩
    have he : singleBranchToForest top b.1.1 c' = b' := Subtype.ext (Prod.ext hc.1.symm rfl)
    have ht := hb.2 c' ⟨rfl, hc.2⟩
    rw [← he]
    exact ht

/-- The removed phases of tree `j`. -/
noncomputable def treeOff (off : Finset (GBranch top)) (j : Fin w) : Finset (GBranch (single (top j))) :=
  univ.filter fun b => singleBranchToForest top j b ∈ off

theorem mem_treeOff (off : Finset (GBranch top)) (j : Fin w) (c : GBranch (single (top j))) :
    c ∈ treeOff top off j ↔ singleBranchToForest top j c ∈ off := by
  unfold treeOff
  simp

theorem forestPhaseProdOff_eq_prod (L γ δ : ℝ) {d : ℕ} (sig : Fin w → ℤˣ) (off : Finset (GBranch top))
    (k : GNode top → Mom d) (x : GBranch top → ℝ) :
    GraftGen.forestPhaseProdOff L γ δ sig top off k x =
      ∏ j, GraftGen.forestPhaseProdOff L γ δ (fun _ => sig j) (single (top j)) (treeOff top off j)
        (fun a => k (singleNodeToForest top j a)) (fun b => x (singleBranchToForest top j b)) := by
  unfold GraftGen.forestPhaseProdOff
  rw [← (forestSingleBranchEquiv top).symm.prod_comp, Fintype.prod_sigma]
  refine prod_congr rfl fun j _ => prod_congr rfl fun b _ => ?_
  simp only [treeOff, mem_filter, mem_univ, true_and, forestSingleBranchEquiv_symm_apply]
  rfl

end Split

/-! ## The product formula -/

section Product

variable (L γ δ : ℝ) {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)

/-- **The top integral with designated times, tree by tree.** -/
theorem topFixIntegral_eq_prod (fix : GBranch top → Option ℝ) (off : Finset (GBranch top))
    (k : GNode top → Mom d) (p t : ℝ) :
    GraftGen.topFixIntegral L γ δ sig top fix off k p t =
      ∏ j, GraftGen.topFixIntegral L γ δ (fun _ => sig j) (single (top j)) (treeFix top fix j) (treeOff top off j)
        (fun a => k (singleNodeToForest top j a)) p t := by
  unfold GraftGen.topFixIntegral
  rw [← integral_free_prod top fix]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [extendFixF_single']
  by_cases h : GraftGen.extendFixF top fix τ ∈ GraftGen.topDomFix top p t fix
  · rw [Set.indicator_of_mem h, forestPhaseProdOff_eq_prod top L γ δ sig off k]
    refine prod_congr rfl fun j _ => ?_
    rw [Set.indicator_of_mem ((topDomFix_iff top fix p t _).mp h j)]
  · rw [Set.indicator_of_notMem h]
    rw [topDomFix_iff] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact (prod_eq_zero (mem_univ j) (Set.indicator_of_notMem hj _)).symm

end Product

/-! ## One tree -/

section Tree

variable (L γ δ : ℝ) {d : ℕ}

/-- The time integral of one tree with designated times (X2/X3's form; with the times of a flower pattern this is
X3's `TIpat`). -/
noncomputable def treeFixIntegral (p : ℕ) (T : TTree) (fix : GBranch (single T) → Option ℝ)
    (off : Finset (GBranch (single T))) (κ : GNode (single T) → (Fin d → ℤ)) (t : ℝ) : ℂ :=
  ∫ τ : {b : GBranch (single T) // fix b = none} → ℝ,
    (treeDomFix p T t fix).indicator (phaseOffT L γ δ T off κ) (extendFixT fix τ)

theorem zpowSign_indicator {α : Type*} (σ : ℤˣ) (S : Set α) (f : α → ℂ) (x : α) :
    zpowSign σ (S.indicator f x) = S.indicator (fun y => zpowSign σ (f y)) x := by
  by_cases h : x ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zpowSign_zero]

theorem zpowSign_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) (σ : ℤˣ) (f : α → ℂ) :
    zpowSign σ (∫ x, f x ∂μ) = ∫ x, zpowSign σ (f x) ∂μ := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact (integral_conj).symm

theorem zpowSign_exp_mul_I (σ : ℤˣ) (θ : ℝ) :
    zpowSign σ (Complex.exp (θ * Complex.I)) = Complex.exp (((σ : ℤ) * θ : ℝ) * Complex.I) := by
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simp [zpowSign]
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    rw [show zpowSign (-1) (Complex.exp (θ * Complex.I)) = (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) from
      ite_eq_right hne, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring

/-- **One tree of sign `σ`**: the top integral is the `σ`-conjugate of the tree integral. -/
theorem single_topFixIntegral_eq (σ : ℤˣ) (p : ℕ) (T : TTree) (fix : GBranch (single T) → Option ℝ)
    (off : Finset (GBranch (single T))) (κ : GNode (single T) → (Fin d → ℤ)) (t : ℝ) :
    GraftGen.topFixIntegral L γ δ (fun _ => σ) (single T) fix off (fun a => (0 : Mom d) + latticePoint L (κ a))
      (p : ℝ) t = zpowSign σ (treeFixIntegral L γ δ p T fix off κ t) := by
  unfold GraftGen.topFixIntegral treeFixIntegral
  rw [zpowSign_integral]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  beta_reduce
  rw [zpowSign_indicator]
  have hx : GraftGen.extendFixF (single T) fix τ = extendFixT fix τ := rfl
  rw [hx]
  have hS : GraftGen.topDomFix (single T) (p : ℝ) t fix = treeDomFix p T t fix := rfl
  rw [hS]
  congr 1
  funext y
  unfold GraftGen.forestPhaseProdOff phaseOffT
  rw [zpowSign_prod]
  refine prod_congr rfl fun c _ => ?_
  split_ifs
  · simp [zpowSign]
  · rw [zpowSign_exp_mul_I]
    congr 2
    simp only [zero_add, omegaT, treeSign, nodeSign, TTree.pathSign, one_mul]
    push_cast
    ring

end Tree

end WaveTurbulence.X2E
