/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.DtRep
public import WaveTurbulence.Foundations.XChain.GraftGenDraft.KernelGenSeries
public import WaveTurbulence.Foundations.XChain.ForestRootPhaseIntegral

/-!
# CPL-3, step 5: the top integral with the roots held at `t` (combinatorics)

Let `top : Fin w → TTree` be a forest of non-leaf trees. Its *children forest* `childForest top` has width
`w · 3`: tree `(j, i)` is the `i`-th child of `top j`, with sign `σ_j (−1)^{[i = 1]}`.

**Statements.**
- `childBranch`: a bijection from the branches of the children forest onto the non-root branches of `top`,
  `((j,i), q) ↦ (j, i :: q)`.
- It respects the child relation, the node labels and the signs (`nodeSign_childBranch`).

This is the combinatorial input for `topFixIntegral_roots` (part B). With the roots held at `t`, the free
times of `top` are the times of the children forest, and INDUCT's `forestPhaseIntegral_eq_roots` factors
their integral.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Induct SysAPI
open scoped Classical

/-- The `i`-th child of a tree (`•` for `•`). -/
def childOf : TTree → Fin 3 → TTree
  | .leaf, _ => .leaf
  | .node l m r, i => ![l, m, r] i

theorem mem_branching_cons_iff (T : TTree) (i : Fin 3) (q : TTree.Path) :
    i :: q ∈ T.branching ↔ T ≠ .leaf ∧ q ∈ (childOf T i).branching := by
  cases T with
  | leaf => simp [TTree.branching]
  | node l m r =>
    simp only [TTree.branching, Finset.mem_insert, Finset.mem_union, TTree.pre, Finset.mem_image,
      List.cons.injEq, ne_eq, reduceCtorEq, not_false_eq_true, true_and, childOf]
    fin_cases i <;> simp

theorem mem_nodes_cons_iff (T : TTree) (i : Fin 3) (q : TTree.Path) :
    i :: q ∈ T.nodes ↔ T ≠ .leaf ∧ q ∈ (childOf T i).nodes := by
  cases T with
  | leaf => simp [TTree.nodes]
  | node l m r =>
    simp only [TTree.nodes, Finset.mem_insert, Finset.mem_union, TTree.pre, Finset.mem_image,
      List.cons.injEq, ne_eq, reduceCtorEq, not_false_eq_true, true_and, childOf]
    fin_cases i <;> simp

theorem nil_mem_branching_iff (T : TTree) : ([] : TTree.Path) ∈ T.branching ↔ T ≠ .leaf := by
  cases T with
  | leaf => simp [TTree.branching]
  | node l m r => simp [TTree.branching]

variable {w : ℕ}

/-- The children forest, indexed by `Fin (w * 3) ≃ Fin w × Fin 3`. -/
def childForest (top : Fin w → TTree) : Fin (w * 3) → TTree :=
  fun x => childOf (top (finProdFinEquiv.symm x).1) (finProdFinEquiv.symm x).2

/-- The signs of the children forest: `σ_j (−1)^{[i = 1]}`. -/
def childSig (sig : Fin w → ℤˣ) : Fin (w * 3) → ℤˣ :=
  fun x => TTree.pathSign (sig (finProdFinEquiv.symm x).1) [(finProdFinEquiv.symm x).2]

variable (top : Fin w → TTree)

/-- A branch of the children forest as a non-root branch of `top`. -/
def childBranch (c : GBranch (childForest top)) : {b : GBranch top // b.1.2 ≠ []} :=
  ⟨⟨((finProdFinEquiv.symm c.1.1).1, (finProdFinEquiv.symm c.1.1).2 :: c.1.2),
    ((mem_branching_cons_iff _ _ _).2 ⟨fun h => by
      have hc := c.2
      change c.1.2 ∈ (childOf (top (finProdFinEquiv.symm c.1.1).1) (finProdFinEquiv.symm c.1.1).2).branching
        at hc
      rw [h] at hc
      simp [childOf, TTree.branching] at hc, c.2⟩)⟩, List.cons_ne_nil _ _⟩

/-- A child-forest node as a node of `top` (non-leaf trees). -/
def childNode (hnode : ∀ j, top j ≠ .leaf) (a : GNode (childForest top)) : GNode top :=
  ⟨((finProdFinEquiv.symm a.1.1).1, (finProdFinEquiv.symm a.1.1).2 :: a.1.2),
    (mem_nodes_cons_iff _ _ _).2 ⟨hnode _, a.2⟩⟩

theorem childBranch_bijective : Function.Bijective (childBranch top) := by
  constructor
  · intro c c' h
    have h1 := congrArg (fun b : {b : GBranch top // b.1.2 ≠ []} => b.1.1.1) h
    have h2 := congrArg (fun b : {b : GBranch top // b.1.2 ≠ []} => b.1.1.2) h
    simp only [childBranch, List.cons.injEq] at h1 h2
    have hx : c.1.1 = c'.1.1 :=
      finProdFinEquiv.symm.injective (Prod.ext h1 h2.1)
    exact Subtype.ext (Prod.ext hx h2.2)
  · rintro ⟨⟨⟨j, q⟩, hq⟩, hne⟩
    obtain ⟨i, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hm := (mem_branching_cons_iff (top j) i rest).1 hq
    refine ⟨⟨(finProdFinEquiv (j, i), rest), ?_⟩, ?_⟩
    · change rest ∈ (childOf (top (finProdFinEquiv.symm (finProdFinEquiv (j, i))).1)
        (finProdFinEquiv.symm (finProdFinEquiv (j, i))).2).branching
      simpa only [Equiv.symm_apply_apply] using hm.2
    · apply Subtype.ext
      apply Subtype.ext
      simp [childBranch]

theorem childBranch_toNode (hnode : ∀ j, top j ≠ .leaf) (c : GBranch (childForest top)) :
    (childBranch top c).1.toNode = childNode top hnode c.toNode := rfl

theorem childBranch_child (hnode : ∀ j, top j ≠ .leaf) (c : GBranch (childForest top)) (k : Fin 3) :
    (childBranch top c).1.child k = childNode top hnode (c.child k) := rfl

theorem childBranch_isChildOf_iff (c c' : GBranch (childForest top)) :
    (childBranch top c').1.IsChildOf (childBranch top c).1 ↔ c'.IsChildOf c := by
  unfold GBranch.IsChildOf childBranch
  simp only [List.cons_append, List.cons.injEq]
  constructor
  · rintro ⟨h1, k, h2, h3⟩
    exact ⟨finProdFinEquiv.symm.injective (Prod.ext h1 h2), k, h3⟩
  · rintro ⟨h1, k, h2⟩
    rw [h1]
    exact ⟨rfl, k, rfl, h2⟩

theorem nodeSign_childBranch (hnode : ∀ j, top j ≠ .leaf) (sig : Fin w → ℤˣ) (a : GNode (childForest top)) :
    nodeSign sig (childNode top hnode a).1 = nodeSign (childSig sig) a.1 := by
  simp only [nodeSign, childNode, childSig, TTree.pathSign, List.count_cons, List.count_nil]
  rw [zero_add, pow_add, mul_assoc]
  congr 1
  exact mul_comm _ _

/-! ## The change of variables (part B) -/

section Integral

open MeasureTheory

variable (L γ δ : ℝ) {d : ℕ} (sig : Fin w → ℤˣ) (hnode : ∀ j, top j ≠ .leaf)

/-- The roots held at `t`. -/
def fixRoots (t : ℝ) : GBranch top → Option ℝ := fun b => if b.1.2 = [] then some t else none

theorem fixRoots_eq_none_iff (t : ℝ) (b : GBranch top) : fixRoots top t b = none ↔ b.1.2 ≠ [] := by
  unfold fixRoots
  split_ifs with h <;> simp [h]

/-- The branches of the children forest are the free branches. -/
noncomputable def freeChildEquiv (t : ℝ) :
    GBranch (childForest top) ≃ {b : GBranch top // fixRoots top t b = none} :=
  (Equiv.ofBijective _ (childBranch_bijective top)).trans
    (Equiv.subtypeEquivRight fun b => (fixRoots_eq_none_iff top t b).symm)

/-- The root branch of tree `j`. -/
def rootBranch (j : Fin w) : GBranch top := ⟨(j, []), (nil_mem_branching_iff _).2 (hnode j)⟩

/-- The phase factor of the root of tree `j` at time `t`. -/
noncomputable def rootPhaseAt (k : GNode top → Mom d) (t : ℝ) (j : Fin w) : ℂ :=
  Complex.exp ((Real.pi * ((nodeSign sig (rootBranch top hnode j).toNode.1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
    resFactor (k ((rootBranch top hnode j).child 0)) (k ((rootBranch top hnode j).child 1))
      (k ((rootBranch top hnode j).child 2)) (k (rootBranch top hnode j).toNode) * t : ℝ) * Complex.I)

/-- The roots as a subtype. -/
def rootEquiv : Fin w ≃ {b : GBranch top // b.1.2 = []} where
  toFun j := ⟨rootBranch top hnode j, rfl⟩
  invFun b := b.1.1.1
  left_inv _ := rfl
  right_inv b := Subtype.ext (Subtype.ext (Prod.ext rfl b.2.symm))

/-- **The top integral with the roots held at `t`** is the root phases times the forest phase integral of the
children forest. -/
theorem topFixIntegral_roots {p t : ℝ} (hp0 : 0 ≤ p) (htp : t ≤ p + 1) (k : GNode top → Mom d) :
    GraftGen.topFixIntegral L γ δ sig top (fixRoots top t) ∅ k p t =
      (∏ j, rootPhaseAt top L γ δ sig hnode k t j) *
        forestPhaseIntegral L γ δ (childSig sig) (childForest top) (fun a => k (childNode top hnode a)) p t := by
  set Φ := MeasurableEquiv.piCongrLeft (fun _ : {b : GBranch top // fixRoots top t b = none} => ℝ)
    (freeChildEquiv top t)
  have hmp := measurePreserving_piCongrLeft (fun _ : {b : GBranch top // fixRoots top t b = none} =>
    (volume : Measure ℝ)) (freeChildEquiv top t)
  unfold GraftGen.topFixIntegral forestPhaseIntegral
  rw [← integral_const_mul]
  refine (hmp.integral_comp' (fun τ => (GraftGen.topDomFix top p t (fixRoots top t)).indicator
    (GraftGen.forestPhaseProdOff L γ δ sig top ∅ k) (GraftGen.extendFixF top (fixRoots top t) τ))).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  set τh := GraftGen.extendFixF top (fixRoots top t) (Φ σ)
  have hroot : ∀ b : GBranch top, b.1.2 = [] → τh b = t := fun b hb =>
    GraftGen.extendFixF_of_some top (Φ σ) (by simp [fixRoots, hb])
  have hfree : ∀ c, τh (childBranch top c).1 = σ c := by
    intro c
    have hn : fixRoots top t (childBranch top c).1 = none :=
      (fixRoots_eq_none_iff top t _).2 (childBranch top c).2
    change GraftGen.extendFixF top (fixRoots top t) (Φ σ) (childBranch top c).1 = σ c
    rw [GraftGen.extendFixF_of_none top (Φ σ) hn]
    have he : (⟨(childBranch top c).1, hn⟩ : {b : GBranch top // fixRoots top t b = none}) =
        freeChildEquiv top t c := rfl
    rw [he]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (freeChildEquiv top t) σ c
  have hdom : τh ∈ GraftGen.topDomFix top p t (fixRoots top t) ↔
      σ ∈ ForestTimeDomain (childForest top) p t := by
    constructor
    · intro h c
      have hb : fixRoots top t (childBranch top c).1 = none :=
        (fixRoots_eq_none_iff top t _).2 (childBranch top c).2
      obtain ⟨h1, h2, -, h4⟩ := (h (childBranch top c).1).1 hb
      rw [hfree] at h1 h4
      refine ⟨h1, h4, fun c' hc' => ?_⟩
      have hb' : fixRoots top t (childBranch top c').1 = none :=
        (fixRoots_eq_none_iff top t _).2 (childBranch top c').2
      have := (h (childBranch top c).1).2 (childBranch top c').1
        ((childBranch_isChildOf_iff top c c').2 hc') (Or.inl hb')
      rwa [hfree, hfree] at this
    · intro h b
      refine ⟨fun hb => ?_, fun b' hb' _ => ?_⟩
      · obtain ⟨c, hc⟩ := (childBranch_bijective top).2 ⟨b, (fixRoots_eq_none_iff top t b).1 hb⟩
        have hbc : b = (childBranch top c).1 := by rw [hc]
        rw [hbc, hfree]
        obtain ⟨h1, h2, -⟩ := h c
        exact ⟨h1, by linarith, by linarith, h2⟩
      · have hne' : b'.1.2 ≠ [] := by
          rw [hb'.2.choose_spec]
          simp
        obtain ⟨c', hc'⟩ := (childBranch_bijective top).2 ⟨b', hne'⟩
        have hbc' : b' = (childBranch top c').1 := by rw [hc']
        by_cases hb0 : b.1.2 = []
        · rw [hroot b hb0, hbc', hfree]
          exact (h c').2.1
        · obtain ⟨c, hc⟩ := (childBranch_bijective top).2 ⟨b, hb0⟩
          have hbc : b = (childBranch top c).1 := by rw [hc]
          rw [hbc, hbc', hfree, hfree]
          rw [hbc, hbc'] at hb'
          exact (h c).2.2 c' ((childBranch_isChildOf_iff top c c').1 hb')
  have hph : GraftGen.forestPhaseProdOff L γ δ sig top ∅ k τh =
      (∏ j, rootPhaseAt top L γ δ sig hnode k t j) *
        forestPhaseProd L γ δ (childSig sig) (childForest top) (fun a => k (childNode top hnode a)) σ := by
    unfold GraftGen.forestPhaseProdOff forestPhaseProd
    simp only [Finset.notMem_empty, ite_false]
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun b : GBranch top => b.1.2 = [])]
    congr 1
    · refine (Fintype.prod_equiv (rootEquiv top hnode) _ _ fun j => ?_).symm
      unfold rootPhaseAt
      have hr : τh ((rootEquiv top hnode) j).1 = t := hroot _ rfl
      rw [hr]
      rfl
    · refine (Fintype.prod_equiv (Equiv.ofBijective _ (childBranch_bijective top)) _ _ fun c => ?_).symm
      change _ = Complex.exp ((Real.pi * ((nodeSign sig (childBranch top c).1.toNode.1 : ℤˣ) : ℤ) * δ *
        L ^ (2 * γ) * resFactor (k ((childBranch top c).1.child 0)) (k ((childBranch top c).1.child 1))
          (k ((childBranch top c).1.child 2)) (k (childBranch top c).1.toNode) * τh (childBranch top c).1 : ℝ) *
          Complex.I)
      rw [hfree, childBranch_toNode top hnode, childBranch_child top hnode, childBranch_child top hnode,
        childBranch_child top hnode, nodeSign_childBranch top hnode]
  show (GraftGen.topDomFix top p t (fixRoots top t)).indicator
      (GraftGen.forestPhaseProdOff L γ δ sig top ∅ k) τh =
    (∏ j, rootPhaseAt top L γ δ sig hnode k t j) * (ForestTimeDomain (childForest top) p t).indicator
      (forestPhaseProd L γ δ (childSig sig) (childForest top) fun a => k (childNode top hnode a)) σ
  by_cases hσ : σ ∈ ForestTimeDomain (childForest top) p t
  · rw [Set.indicator_of_mem (hdom.2 hσ), Set.indicator_of_mem hσ, hph]
  · rw [Set.indicator_of_notMem (fun h => hσ (hdom.1 h)), Set.indicator_of_notMem hσ, mul_zero]

end Integral

/-! ## The top factor with the roots held at `t` (part C) -/

section TopFactor

variable (L γ δ : ℝ) {d : ℕ} (p : ℕ)

theorem zpowSign_conj (ζ : ℤˣ) (z : ℂ) : zpowSign ζ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (zpowSign ζ z) := by
  rcases Int.units_eq_one_or ζ with rfl | rfl <;> simp [zpowSign]

/-- The child labels of a non-leaf tree. -/
def childLabels {T : TTree} (hT : T ≠ .leaf) (i : Fin 3) (κ : GNode (single T) → (Fin d → ℤ)) :
    GNode (single (childOf T i)) → (Fin d → ℤ) :=
  fun a => κ ⟨(0, i :: a.1.2), (mem_nodes_cons_iff T i a.1.2).2 ⟨hT, a.2⟩⟩

/-- The root branch of a non-leaf tree. -/
def rootBr (T : TTree) (hT : T ≠ .leaf) : GBranch (single T) := ⟨(0, []), (nil_mem_branching_iff T).2 hT⟩

/-- **The signed fixed-root coefficient of one tree** as the root phase times the signed children integrals. -/
theorem zpowSign_dtTimeCoef (ζ : ℤˣ) (T : TTree) (hT : T ≠ .leaf) (κ : GNode (single T) → (Fin d → ℤ))
    (t : ℝ) :
    zpowSign ζ (dtTimeCoef L γ δ p T κ t) =
      Complex.exp ((Real.pi * ((ζ : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        resFactor (latticePoint L (κ ((rootBr T hT).child 0))) (latticePoint L (κ ((rootBr T hT).child 1)))
          (latticePoint L (κ ((rootBr T hT).child 2))) (latticePoint L (κ (rootBr T hT).toNode)) * t : ℝ) *
          Complex.I) *
        ∏ i : Fin 3, zpowSign (TTree.pathSign ζ [i])
          (timeInt L γ δ (childOf T i) (childLabels hT i κ) p t) := by
  cases T with
  | leaf => exact absurd rfl hT
  | node l m r =>
    have hp0 : TTree.pathSign ζ [0] = ζ := by simp [TTree.pathSign]
    have hp1 : TTree.pathSign ζ [1] = -ζ := by simp [TTree.pathSign]
    have hp2 : TTree.pathSign ζ [2] = ζ := by simp [TTree.pathSign]
    rw [Fin.prod_univ_three, hp0, hp1, hp2, zpowSign_neg]
    simp only [dtTimeCoef]
    rw [zpowSign_mul, zpowSign_mul, zpowSign_mul, zpowSign_conj]
    have hroot : zpowSign ζ (rootPhase l m r L γ δ κ t) =
        Complex.exp ((Real.pi * ((ζ : ℤ) : ℝ) * δ * L ^ (2 * γ) *
          resFactor (latticePoint L (κ ((rootB l m r).child 0))) (latticePoint L (κ ((rootB l m r).child 1)))
            (latticePoint L (κ ((rootB l m r).child 2))) (latticePoint L (κ (rootB l m r).toNode)) * t : ℝ) *
          Complex.I) := by
      unfold rootPhase
      rw [zpowSign_exp_real_mul_I]
      congr 2
      push_cast
      ring
    rw [hroot]
    simp only [mul_assoc]
    rfl

end TopFactor

/-! ## The forest top factor -/

section ForestTopFactor

variable (L γ δ : ℝ) {d : ℕ} (p : ℕ) (sig : Fin w → ℤˣ) (hnode : ∀ j, top j ≠ .leaf)

theorem nodeSign_rootBranch (j : Fin w) : nodeSign sig (rootBranch top hnode j).toNode.1 = sig j := by
  simp [nodeSign, rootBranch, GBranch.toNode, TTree.pathSign]

include hnode in
/-- **The prefactor times the top factor with the roots held at `t`** is the product of the signed `∂_t`
coefficients of the top trees. -/
theorem prefactor_mul_topGenFactor_roots {n : Fin w → (Fin d → ℤ)} (kt : ForestDecoration top d n) {t : ℝ}
    (htp : t ≤ (p : ℝ) + 1) :
    ((coupling d L γ δ : ℂ) ^ (∑ j, (top j).order) *
        ∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
      GraftGen.topGenFactor L γ δ sig top (fixRoots top t) ∅ (fun _ => 1) kt.1 0 p t =
    ∏ j, genTopCoef top sig (fun j => dtCoef L γ δ p t (top j)) kt j := by
  let g : Fin w × Fin 3 → ℂ := fun ji => zpowSign (TTree.pathSign (sig ji.1) [ji.2])
    (timeInt L γ δ (childOf (top ji.1) ji.2)
      (childLabels (hnode ji.1) ji.2 (fun a => kt.1 (singleNodeToForest top ji.1 a))) p t)
  have hj : ∀ j, genTopCoef top sig (fun j => dtCoef L γ δ p t (top j)) kt j =
      zpowSign (sig j) (treePrefactor L γ δ d (top j)) *
        epsProd (top j) (fun a => kt.1 (singleNodeToForest top j a)) *
          (rootPhaseAt top L γ δ sig hnode (fun a => latticePoint L (kt.1 a)) t j * ∏ i : Fin 3, g (j, i)) := by
    intro j
    unfold genTopCoef dtCoef
    rw [zpowSign_mul, zpowSign_mul, zpowSign_epsProd,
      zpowSign_dtTimeCoef L γ δ p (sig j) (top j) (hnode j)]
    congr 2
    unfold rootPhaseAt
    rw [nodeSign_rootBranch top sig hnode j]
    rfl
  rw [Finset.prod_congr rfl (fun j _ => hj j), ← prod_signed_treePrefactor_eq L γ δ top sig]
  unfold GraftGen.topGenFactor
  simp only [zero_add, Complex.ofReal_one, mul_one]
  rw [topFixIntegral_roots top L γ δ sig hnode (Nat.cast_nonneg p) htp, forest_epsProd_eq_roots top kt.1,
    forestPhaseIntegral_eq_roots L γ δ (childForest top) (childSig sig)
      (fun a => kt.1 (childNode top hnode a)) p t,
    Fintype.prod_equiv finProdFinEquiv.symm (fun x => zpowSign (childSig sig x)
      (timeInt L γ δ (childForest top x)
        (fun a => kt.1 (childNode top hnode (singleNodeToForest (childForest top) x a))) p t)) g (fun x => rfl),
    Fintype.prod_prod_type]
  simp only [prod_mul_distrib]
  ring

end ForestTopFactor

end WaveTurbulence.Cpl
