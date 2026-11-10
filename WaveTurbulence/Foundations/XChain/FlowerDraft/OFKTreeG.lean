/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.Kernel

/-!
# O-FK, part 1: tree terms with time-dependent leaf inputs

`treeTermG p T D t n` generalizes `treeTerm`. Leaf `ℓ` gets the input `D.B ℓ (t_{ℓ^pr})`, evaluated at the time of
its parent branching node (or at the upper time `t` if `T` is a single leaf):
`𝒥^G_T(t)_n = (δ/(2L^{d−γ}))^{n(T)} ζ(T) ∑_κ ε_κ ∫_{𝒟(p,t)} ∏ e^{…t_𝔫} ∏_ℓ (D.B ℓ (t_{ℓ^pr}))_{κ_ℓ}^{ζ_ℓ}`.

* For constant inputs it is `treeTerm` (`treeTermG_const`); for a single leaf it is the input at `t`
  (`treeTermG_leaf`).
* The flower tree term `𝒥_F[b]` of `Flower-Ops` is `treeTermG` with `b` at the flower and `a(p)` elsewhere
  (part 3). Its kernel form is a Fubini in the flower parent's time.
* `timeIntG_node`: the time integral of `node l m r` splits at the root. The leaves below the root's children
  read the root time.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

/-! ## Leaf data -/

/-- Leaf inputs depending on time, continuous in time, with summable majorants uniform in time. -/
structure LeafData (T : TTree) (d : ℕ) where
  B : GLeaf (single T) → ℝ → (Fin d → ℤ) → ℂ
  U : GLeaf (single T) → (Fin d → ℤ) → ℝ
  cont : ∀ ℓ q, Continuous fun s => B ℓ s q
  summ : ∀ ℓ, Summable (U ℓ)
  nonneg : ∀ ℓ k, 0 ≤ U ℓ k
  bound : ∀ ℓ s q, ‖B ℓ s q‖ ≤ U ℓ q

/-- Restriction of leaf data to a subtree. -/
def LeafData.res {T S : TTree} {i : Fin 3} {d : ℕ} (D : LeafData T d) (h : IsSubtreeAt T S i) :
    LeafData S d where
  B ℓ := D.B (h.embL ℓ)
  U ℓ := D.U (h.embL ℓ)
  cont ℓ := D.cont (h.embL ℓ)
  summ ℓ := D.summ (h.embL ℓ)
  nonneg ℓ := D.nonneg (h.embL ℓ)
  bound ℓ := D.bound (h.embL ℓ)

/-! ## Parent times and leaf factors -/

theorem leaf_dropLast_mem {T : TTree} (ℓ : GLeaf (single T)) (h : ℓ.1.2 ≠ []) :
    ℓ.1.2.dropLast ∈ T.branching :=
  TTree.branching_of_append_mem T (i := ℓ.1.2.getLast h)
    (by rw [List.dropLast_append_getLast h]; exact TTree.leaves_subset_nodes _ ℓ.2)

/-- The parent of a non-root leaf. -/
def leafParent {T : TTree} (ℓ : GLeaf (single T)) (h : ℓ.1.2 ≠ []) : GBranch (single T) :=
  ⟨(0, ℓ.1.2.dropLast), leaf_dropLast_mem ℓ h⟩

/-- The time of the parent of the leaf `ℓ`, or the upper time `t` if `ℓ` is the root. -/
noncomputable def parTime {T : TTree} (τ : GBranch (single T) → ℝ) (t : ℝ) (ℓ : GLeaf (single T)) : ℝ :=
  if h : ℓ.1.2 = [] then t else τ (leafParent ℓ h)

variable {d : ℕ}

/-- The leaf factor `∏_ℓ (D.B ℓ (t_{ℓ^pr}))_{κ_ℓ}^{ζ_ℓ}`. -/
noncomputable def leafFactorG (T : TTree) (D : LeafData T d) (κ : GNode (single T) → (Fin d → ℤ))
    (τ : GBranch (single T) → ℝ) (t : ℝ) : ℂ :=
  ∏ ℓ : GLeaf (single T), zpowSign (treeSign T ℓ.toNode) (D.B ℓ (parTime τ t ℓ) (κ ℓ.toNode))

theorem continuous_zpowSign (σ : ℤˣ) : Continuous (zpowSign σ) := by
  unfold zpowSign
  split_ifs
  · exact continuous_id
  · exact Complex.continuous_conj

theorem continuous_parTime_joint {T : TTree} (ℓ : GLeaf (single T)) :
    Continuous fun z : ℝ × (GBranch (single T) → ℝ) => parTime z.2 z.1 ℓ := by
  unfold parTime
  by_cases h : ℓ.1.2 = []
  · simp only [h, ↓reduceDIte]; fun_prop
  · simp only [h, ↓reduceDIte]; fun_prop

theorem continuous_leafFactorG_joint (T : TTree) (D : LeafData T d)
    (κ : GNode (single T) → (Fin d → ℤ)) :
    Continuous fun z : ℝ × (GBranch (single T) → ℝ) => leafFactorG T D κ z.2 z.1 := by
  unfold leafFactorG
  refine continuous_finsetProd _ fun ℓ _ => (continuous_zpowSign _).comp ?_
  exact (D.cont ℓ _).comp (continuous_parTime_joint ℓ)

theorem continuous_leafFactorG (T : TTree) (D : LeafData T d) (κ : GNode (single T) → (Fin d → ℤ))
    (t : ℝ) : Continuous fun τ => leafFactorG T D κ τ t :=
  (continuous_leafFactorG_joint T D κ).comp (Continuous.prodMk continuous_const continuous_id)

/-- The bound of the leaf factor. -/
noncomputable def leafBound (T : TTree) (D : LeafData T d) (κ : GNode (single T) → (Fin d → ℤ)) : ℝ :=
  ∏ ℓ : GLeaf (single T), D.U ℓ (κ ℓ.toNode)

theorem leafBound_nonneg (T : TTree) (D : LeafData T d) (κ : GNode (single T) → (Fin d → ℤ)) :
    0 ≤ leafBound T D κ := Finset.prod_nonneg fun ℓ _ => D.nonneg ℓ _

theorem norm_leafFactorG_le (T : TTree) (D : LeafData T d) (κ : GNode (single T) → (Fin d → ℤ))
    (τ : GBranch (single T) → ℝ) (t : ℝ) : ‖leafFactorG T D κ τ t‖ ≤ leafBound T D κ := by
  unfold leafFactorG leafBound
  rw [norm_prod]
  gcongr with ℓ _
  rw [norm_zpowSign]
  exact D.bound ℓ _ _

/-! ## The time integral and the tree term -/

variable (L γ δ : ℝ)

/-- The time integral with leaf inputs. -/
noncomputable def timeIntG (T : TTree) (κ : GNode (single T) → (Fin d → ℤ)) (D : LeafData T d)
    (p t : ℝ) : ℂ :=
  ∫ τ, (treeTimeDomain T p t).indicator (fun τ => phaseFn L γ δ T κ τ * leafFactorG T D κ τ t) τ

/-- **The tree term with time-dependent leaf inputs.** -/
noncomputable def treeTermG (p : ℕ) (T : TTree) (D : LeafData T d) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  treePrefactor L γ δ d T *
    ∑' κ : TreeDecoration T d n, epsProd T κ.1 * timeIntG L γ δ T κ.1 D p t

/-- Constant inputs give `treeTerm`. -/
theorem treeTermG_const (p : ℕ) (T : TTree) {aP : (Fin d → ℤ) → ℂ}
    (D : LeafData T d) (hD : ∀ ℓ s, D.B ℓ s = aP) (t : ℝ) (n : Fin d → ℤ) :
    treeTermG L γ δ p T D t n = treeTerm L γ δ p T aP t n := by
  rw [treeTerm_eq]
  unfold treeTermG
  congr 1
  refine tsum_congr fun κ => ?_
  rw [treeSummand_eq]
  have hl : ∀ τ, leafFactorG T D κ.1 τ t = leafProd T aP κ.1 := fun τ => by
    unfold leafFactorG leafProd
    simp only [hD]
  unfold timeIntG timeInt
  simp only [hl]
  have : (fun τ => (treeTimeDomain T (p : ℝ) t).indicator
      (fun τ => phaseFn L γ δ T κ.1 τ * leafProd T aP κ.1) τ) =
      fun τ => (treeTimeDomain T (p : ℝ) t).indicator (phaseFn L γ δ T κ.1) τ * leafProd T aP κ.1 := by
    funext τ
    by_cases h : τ ∈ treeTimeDomain T (p : ℝ) t
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [this, integral_mul_const]
  ring

/-- A single leaf gives its input at the upper time. -/
theorem treeTermG_leaf (p : ℕ) (D : LeafData TTree.leaf d) (t : ℝ) (n : Fin d → ℤ) :
    treeTermG L γ δ p TTree.leaf D t n = D.B ⟨(0, []), by simp [single, TTree.leaves]⟩ t n := by
  classical
  let κ₀ : TreeDecoration TTree.leaf d n := ⟨fun _ => n, fun c => isEmptyElim c, rfl⟩
  have hsub : ∀ κ : TreeDecoration TTree.leaf d n, κ = κ₀ := fun κ =>
    Subtype.ext (funext fun a => by rw [gNode_single_leaf_eq_root a]; exact κ.2.2)
  let ℓ₀ : GLeaf (single TTree.leaf) := ⟨(0, []), by simp [single, TTree.leaves]⟩
  have huniq : ∀ ℓ : GLeaf (single TTree.leaf), ℓ = ℓ₀ := fun ℓ =>
    Subtype.ext (congrArg Subtype.val (gNode_single_leaf_eq_root ℓ.toNode))
  have hdom : treeTimeDomain TTree.leaf (p : ℝ) t = univ := by
    ext τ
    simp only [treeTimeDomain, mem_ofPred_eq, mem_univ, iff_true]
    exact fun c => isEmptyElim c
  have hval : ∀ τ : GBranch (single TTree.leaf) → ℝ,
      phaseFn L γ δ TTree.leaf κ₀.1 τ * leafFactorG TTree.leaf D κ₀.1 τ t = D.B ℓ₀ t n := by
    intro τ
    unfold phaseFn leafFactorG
    rw [Fintype.prod_empty, one_mul, Fintype.prod_eq_single ℓ₀ fun ℓ hℓ => absurd (huniq ℓ) hℓ]
    have hsign : treeSign TTree.leaf ℓ₀.toNode = 1 := treeSign_root _
    have hpar : parTime τ t ℓ₀ = t := by simp [parTime, ℓ₀]
    rw [hsign, hpar]
    simp [zpowSign, κ₀]
  unfold treeTermG timeIntG
  rw [tsum_eq_single κ₀ fun κ hκ => absurd (hsub κ) hκ, hdom]
  simp only [Set.indicator_univ, hval]
  rw [integral_const]
  simp [treePrefactor, epsProd, TTree.order, volume_pi, Measure.pi_of_empty (fun _ => volume)]
  rfl

/-! ## Bounds and measurability -/

theorem norm_integral_treeTimeDomain_le_C (T : TTree) (p t : ℝ) (f : (GBranch (single T) → ℝ) → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ τ, ‖f τ‖ ≤ C) :
    ‖∫ τ, (treeTimeDomain T p t).indicator f τ‖ ≤ boxVol T p t * C := by
  set Box : Set (GBranch (single T) → ℝ) := Set.pi univ fun _ => Icc p t
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBc : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
  have h := norm_integral_le_of_norm_le (μ := volume) (f := (treeTimeDomain T p t).indicator f)
    (g := Box.indicator fun _ => C)
    ((integrable_indicator_iff hBm).2 (integrableOn_const hBc.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun τ => by
      by_cases hD : τ ∈ treeTimeDomain T p t
      · have hτ : τ ∈ Box := fun c _ => ⟨(hD c).1.le, (hD c).2.1.le⟩
        rw [Set.indicator_of_mem hD, Set.indicator_of_mem hτ]
        exact hf τ
      · rw [Set.indicator_of_notMem hD, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hC) _)
  rw [integral_indicator hBm, setIntegral_const, smul_eq_mul] at h
  exact h

theorem norm_timeIntG_le (T : TTree) (κ : GNode (single T) → (Fin d → ℤ)) (D : LeafData T d)
    (p t : ℝ) : ‖timeIntG L γ δ T κ D p t‖ ≤ boxVol T p t * leafBound T D κ :=
  norm_integral_treeTimeDomain_le_C T p t _ (leafBound_nonneg T D κ) fun τ => by
    rw [norm_mul, norm_phaseFn, one_mul]
    exact norm_leafFactorG_le T D κ τ t

theorem stronglyMeasurable_timeIntG (T : TTree) (κ : GNode (single T) → (Fin d → ℤ))
    (D : LeafData T d) (p : ℝ) : StronglyMeasurable fun t => timeIntG L γ δ T κ D p t := by
  have hU := (isOpen_domSet T p).measurableSet
  have hF : StronglyMeasurable fun z : ℝ × (GBranch (single T) → ℝ) =>
      {z : ℝ × (GBranch (single T) → ℝ) | z.2 ∈ treeTimeDomain T p z.1}.indicator
        (fun z => phaseFn L γ δ T κ z.2 * leafFactorG T D κ z.2 z.1) z :=
    (((continuous_phaseFn L γ δ T κ).comp continuous_snd).mul
      (continuous_leafFactorG_joint T D κ)).stronglyMeasurable.indicator hU
  convert hF.integral_prod_right' (ν := (volume : Measure (GBranch (single T) → ℝ))) using 1
  funext t
  unfold timeIntG
  congr 1

/-! ## The root recursion of the time integral -/

section Node

variable (l m r : TTree)

theorem parTime_embL {S : TTree} {i : Fin 3} (h : IsSubtreeAt (TTree.node l m r) S i)
    (τ : GBranch (single (TTree.node l m r)) → ℝ) (t : ℝ) (ℓ : GLeaf (single S)) :
    parTime τ t (h.embL ℓ) = parTime (fun c => τ (h.embB c)) (τ (rootB l m r)) ℓ := by
  unfold parTime
  have hne : (h.embL ℓ).1.2 ≠ [] := by simp [IsSubtreeAt.embL]
  simp only [hne, ↓reduceDIte]
  by_cases hq : ℓ.1.2 = []
  · simp only [hq, ↓reduceDIte]
    congr 1
    exact GBranch.ext_path (by simp [leafParent, IsSubtreeAt.embL, hq, rootB])
  · simp only [hq, ↓reduceDIte]
    congr 1
    exact GBranch.ext_path (by
      simp [leafParent, IsSubtreeAt.embL, IsSubtreeAt.embB, List.dropLast_cons_of_ne_nil hq])

/-- The leaf factor of `node l m r` splits at the root; the middle subtree is conjugated. -/
theorem leafFactorG_node (D : LeafData (TTree.node l m r) d)
    (κ : GNode (single (TTree.node l m r)) → (Fin d → ℤ))
    (τ : GBranch (single (TTree.node l m r)) → ℝ) (t : ℝ) :
    leafFactorG (TTree.node l m r) D κ τ t =
      leafFactorG l (D.res (isSubtreeAt_left l m r)) ((isSubtreeAt_left l m r).res κ)
          (fun c => τ ((isSubtreeAt_left l m r).embB c)) (τ (rootB l m r)) *
        ((starRingEnd ℂ) (leafFactorG m (D.res (isSubtreeAt_mid l m r))
            ((isSubtreeAt_mid l m r).res κ) (fun c => τ ((isSubtreeAt_mid l m r).embB c))
            (τ (rootB l m r))) *
          leafFactorG r (D.res (isSubtreeAt_right l m r)) ((isSubtreeAt_right l m r).res κ)
            (fun c => τ ((isSubtreeAt_right l m r).embB c)) (τ (rootB l m r))) := by
  unfold leafFactorG
  rw [prod_gLeaf_node (M := ℂ), map_prod (starRingEnd ℂ)]
  have hl : ∀ ℓ : GLeaf (single l), zpowSign (treeSign (TTree.node l m r)
      ((isSubtreeAt_left l m r).embL ℓ).toNode)
      (D.B ((isSubtreeAt_left l m r).embL ℓ) (parTime τ t ((isSubtreeAt_left l m r).embL ℓ))
        (κ ((isSubtreeAt_left l m r).embL ℓ).toNode)) =
      zpowSign (treeSign l ℓ.toNode) ((D.res (isSubtreeAt_left l m r)).B ℓ
        (parTime (fun c => τ ((isSubtreeAt_left l m r).embB c)) (τ (rootB l m r)) ℓ)
        ((isSubtreeAt_left l m r).res κ ℓ.toNode)) := fun ℓ => by
    rw [IsSubtreeAt.embL_toNode, treeSign_embN_left, parTime_embL]
    rfl
  have hm : ∀ ℓ : GLeaf (single m), zpowSign (treeSign (TTree.node l m r)
      ((isSubtreeAt_mid l m r).embL ℓ).toNode)
      (D.B ((isSubtreeAt_mid l m r).embL ℓ) (parTime τ t ((isSubtreeAt_mid l m r).embL ℓ))
        (κ ((isSubtreeAt_mid l m r).embL ℓ).toNode)) =
      (starRingEnd ℂ) (zpowSign (treeSign m ℓ.toNode) ((D.res (isSubtreeAt_mid l m r)).B ℓ
        (parTime (fun c => τ ((isSubtreeAt_mid l m r).embB c)) (τ (rootB l m r)) ℓ)
        ((isSubtreeAt_mid l m r).res κ ℓ.toNode))) := fun ℓ => by
    rw [IsSubtreeAt.embL_toNode, treeSign_embN_mid, zpowSign_neg, parTime_embL]
    rfl
  have hr : ∀ ℓ : GLeaf (single r), zpowSign (treeSign (TTree.node l m r)
      ((isSubtreeAt_right l m r).embL ℓ).toNode)
      (D.B ((isSubtreeAt_right l m r).embL ℓ) (parTime τ t ((isSubtreeAt_right l m r).embL ℓ))
        (κ ((isSubtreeAt_right l m r).embL ℓ).toNode)) =
      zpowSign (treeSign r ℓ.toNode) ((D.res (isSubtreeAt_right l m r)).B ℓ
        (parTime (fun c => τ ((isSubtreeAt_right l m r).embB c)) (τ (rootB l m r)) ℓ)
        ((isSubtreeAt_right l m r).res κ ℓ.toNode)) := fun ℓ => by
    rw [IsSubtreeAt.embL_toNode, treeSign_embN_right, parTime_embL]
    rfl
  rw [Finset.prod_congr rfl fun ℓ _ => hl ℓ, Finset.prod_congr rfl fun ℓ _ => hm ℓ,
    Finset.prod_congr rfl fun ℓ _ => hr ℓ]

theorem integrable_timeIntegrandG (S : TTree) (κ : GNode (single S) → (Fin d → ℤ)) (D : LeafData S d)
    (p t : ℝ) :
    Integrable ((treeTimeDomain S p t).indicator
      (fun τ => phaseFn L γ δ S κ τ * leafFactorG S D κ τ t)) := by
  refine (integrable_indicator_iff (measurableSet_treeTimeDomain S p t)).2
    (Measure.integrableOn_of_bounded (M := leafBound S D κ) ?_
      ((continuous_phaseFn L γ δ S κ).mul (continuous_leafFactorG S D κ t)).aestronglyMeasurable
      (ae_of_all _ fun τ => by
        rw [norm_mul, norm_phaseFn, one_mul]
        exact norm_leafFactorG_le S D κ τ t))
  exact (lt_of_le_of_lt (measure_mono (treeTimeDomain_subset_box S p t))
    (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne

/-- **The time integral of `node l m r` with leaf inputs.** -/
theorem timeIntG_node (D : LeafData (TTree.node l m r) d)
    (κ : GNode (single (TTree.node l m r)) → (Fin d → ℤ)) {p t : ℝ} (hpt : p ≤ t) :
    timeIntG L γ δ (TTree.node l m r) κ D p t =
      ∫ s in p..t, rootPhase l m r L γ δ κ s *
        (timeIntG L γ δ l ((isSubtreeAt_left l m r).res κ) (D.res (isSubtreeAt_left l m r)) p s *
          ((starRingEnd ℂ) (timeIntG L γ δ m ((isSubtreeAt_mid l m r).res κ)
              (D.res (isSubtreeAt_mid l m r)) p s) *
            timeIntG L γ δ r ((isSubtreeAt_right l m r).res κ) (D.res (isSubtreeAt_right l m r)) p s)) := by
  set κl := (isSubtreeAt_left l m r).res κ
  set κm := (isSubtreeAt_mid l m r).res κ
  set κr := (isSubtreeAt_right l m r).res κ
  set Dl := D.res (isSubtreeAt_left l m r)
  set Dm := D.res (isSubtreeAt_mid l m r)
  set Dr := D.res (isSubtreeAt_right l m r)
  set Q : ∀ S : TTree, (GNode (single S) → (Fin d → ℤ)) → LeafData S d → ℝ →
      (GBranch (single S) → ℝ) → ℂ := fun S κS DS s =>
    (treeTimeDomain S p s).indicator (fun y => phaseFn L γ δ S κS y * leafFactorG S DS κS y s) with hQ
  set H : ℝ × ((GBranch (single l) → ℝ) × ((GBranch (single m) → ℝ) × (GBranch (single r) → ℝ))) →
      ℂ := fun z => (Ioo p t).indicator (rootPhase l m r L γ δ κ) z.1 *
    (Q l κl Dl z.1 z.2.1 * ((starRingEnd ℂ) (Q m κm Dm z.1 z.2.2.1) * Q r κr Dr z.1 z.2.2.2)) with hH
  have hGH : ∀ τ, (treeTimeDomain (TTree.node l m r) p t).indicator
      (fun τ => phaseFn L γ δ (TTree.node l m r) κ τ * leafFactorG (TTree.node l m r) D κ τ t) τ =
      H (timeSplit l m r τ) := by
    intro τ
    rw [timeSplit_apply]
    simp only [hH, hQ]
    have hdom := mem_treeTimeDomain_node l m r (p := p) (t := t) τ
    by_cases hT : τ ∈ treeTimeDomain (TTree.node l m r) p t
    · obtain ⟨hA, hB, hC, hD⟩ := hdom.1 hT
      rw [Set.indicator_of_mem hT, Set.indicator_of_mem hA, Set.indicator_of_mem hB,
        Set.indicator_of_mem hC, Set.indicator_of_mem hD, phaseFn_node, leafFactorG_node, map_mul]
      ring
    · rw [Set.indicator_of_notMem hT]
      by_cases hA : τ (rootB l m r) ∈ Ioo p t
      · by_cases hB : (fun c => τ ((isSubtreeAt_left l m r).embB c)) ∈
            treeTimeDomain l p (τ (rootB l m r))
        · by_cases hC : (fun c => τ ((isSubtreeAt_mid l m r).embB c)) ∈
              treeTimeDomain m p (τ (rootB l m r))
          · by_cases hD : (fun c => τ ((isSubtreeAt_right l m r).embB c)) ∈
                treeTimeDomain r p (τ (rootB l m r))
            · exact absurd (hdom.2 ⟨hA, hB, hC, hD⟩) hT
            · simp [Set.indicator_of_notMem hD]
          · simp [Set.indicator_of_notMem hC]
        · simp [Set.indicator_of_notMem hB]
      · simp [Set.indicator_of_notMem hA]
  have hmp := measurePreserving_timeSplit l m r
  have hHint : Integrable H ((volume : Measure ℝ).prod ((volume : Measure (GBranch (single l) → ℝ)).prod
      ((volume : Measure (GBranch (single m) → ℝ)).prod (volume : Measure (GBranch (single r) → ℝ))))) := by
    refine (hmp.integrable_comp_emb (timeSplit l m r).measurableEmbedding).1 ?_
    have := integrable_timeIntegrandG L γ δ (TTree.node l m r) κ D p t
    convert this using 1
    funext τ
    exact (hGH τ).symm
  have hinner : ∀ s, ∫ y, H (s, y) ∂((volume : Measure (GBranch (single l) → ℝ)).prod
      ((volume : Measure (GBranch (single m) → ℝ)).prod (volume : Measure (GBranch (single r) → ℝ)))) =
      (Ioo p t).indicator (fun s => rootPhase l m r L γ δ κ s *
        (timeIntG L γ δ l κl Dl p s * ((starRingEnd ℂ) (timeIntG L γ δ m κm Dm p s) *
          timeIntG L γ δ r κr Dr p s))) s := by
    intro s
    simp only [hH]
    set Ql := Q l κl Dl s
    set Qm := Q m κm Dm s
    set Qr := Q r κr Dr s
    have e1 : ∫ a : (GBranch (single l) → ℝ) × ((GBranch (single m) → ℝ) × (GBranch (single r) → ℝ)),
        Ql a.1 * ((starRingEnd ℂ) (Qm a.2.1) * Qr a.2.2) ∂((volume : Measure (GBranch (single l) → ℝ)).prod
          ((volume : Measure (GBranch (single m) → ℝ)).prod (volume : Measure (GBranch (single r) → ℝ)))) =
        (∫ x, Ql x) * ∫ w : (GBranch (single m) → ℝ) × (GBranch (single r) → ℝ),
          (starRingEnd ℂ) (Qm w.1) * Qr w.2 ∂((volume : Measure (GBranch (single m) → ℝ)).prod
            (volume : Measure (GBranch (single r) → ℝ))) :=
      integral_prod_mul Ql
        (fun w : (GBranch (single m) → ℝ) × (GBranch (single r) → ℝ) => (starRingEnd ℂ) (Qm w.1) * Qr w.2)
    have e2 : ∫ w : (GBranch (single m) → ℝ) × (GBranch (single r) → ℝ),
        (starRingEnd ℂ) (Qm w.1) * Qr w.2 ∂((volume : Measure (GBranch (single m) → ℝ)).prod
          (volume : Measure (GBranch (single r) → ℝ))) =
        (∫ x, (starRingEnd ℂ) (Qm x)) * ∫ y, Qr y :=
      integral_prod_mul (fun x => (starRingEnd ℂ) (Qm x)) Qr
    rw [integral_const_mul, e1, e2, integral_conj, Set.indicator_mul_left]
    rfl
  calc timeIntG L γ δ (TTree.node l m r) κ D p t
      = ∫ τ, H (timeSplit l m r τ) := by
        unfold timeIntG
        exact integral_congr_ae (ae_of_all _ hGH)
    _ = ∫ z, H z ∂((volume : Measure ℝ).prod ((volume : Measure (GBranch (single l) → ℝ)).prod
          ((volume : Measure (GBranch (single m) → ℝ)).prod
            (volume : Measure (GBranch (single r) → ℝ))))) := hmp.integral_comp' H
    _ = ∫ s, ∫ y, H (s, y) ∂((volume : Measure (GBranch (single l) → ℝ)).prod
          ((volume : Measure (GBranch (single m) → ℝ)).prod
            (volume : Measure (GBranch (single r) → ℝ)))) := integral_prod H hHint
    _ = ∫ s, (Ioo p t).indicator (fun s => rootPhase l m r L γ δ κ s *
          (timeIntG L γ δ l κl Dl p s * ((starRingEnd ℂ) (timeIntG L γ δ m κm Dm p s) *
            timeIntG L γ δ r κr Dr p s))) s := integral_congr_ae (ae_of_all _ hinner)
    _ = _ := by
        rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
          intervalIntegral.integral_of_le hpt]

end Node

end WaveTurbulence.SysAPI
