/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Assembly
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Probes

/-!
# X3: `∂_t` of the flower kernel is the `dRoot` kernel (T L2331, `∂_t` part)

For a flower tree `F` whose flower parent is not the root, `p < s < t ≤ p+1`, and any `†`/cutoffs:

`𝒦_F^{plain}(t, s) = ∫_s^t 𝒦_F^{dRoot}(u, s) du`  (`flowerKernelGen_plain_eq_integral`).

If the flower parent is the root, `𝒦_F^{plain}(t, s)` does not depend on `t ∈ (s, p+1]`
(`flowerKernelGen_plain_const`). Summed over the trees of a kind:

`𝒦^{plain}(t, s) = 𝒦^{plain}(t₀, s) + ∫_{t₀}^t 𝒦^{dRoot}(u, s) du` for `s < t₀, t ≤ p+1`
(`randFlowerKernel_plain_sub`).

The proof is Fubini at the root time on each decoration. Its slice at root time `u` is the `dRoot` domain
when `s < u < t`, and is empty otherwise (times decrease towards the root: `lt_root_of_ordered`).

Generic tools: `integral_eq_integral_glueAt` is Fubini at one coordinate of a finite index type (OFK's
`integral_eq_integral_glueTime` for any `Fintype`); `integral_equiv_congr` transports an integral along an
index equivalence.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree

/-! ## Generic tools -/

section Generic

variable {J : Type*} [Fintype J] [DecidableEq J]

open Classical in
/-- `t_{c₀} := s`; the other coordinates from `τ'`. -/
noncomputable def glueAt (c₀ : J) (s : ℝ) (τ' : {c : J // c ≠ c₀} → ℝ) : J → ℝ :=
  fun c => if h : c = c₀ then s else τ' ⟨c, h⟩

omit [Fintype J] in
theorem glueAt_self (c₀ : J) (s : ℝ) (τ' : {c : J // c ≠ c₀} → ℝ) : glueAt c₀ s τ' c₀ = s := by
  simp [glueAt]

omit [Fintype J] in
theorem glueAt_ne (c₀ : J) (s : ℝ) (τ' : {c : J // c ≠ c₀} → ℝ) {c : J} (h : c ≠ c₀) :
    glueAt c₀ s τ' c = τ' ⟨c, h⟩ := by
  simp [glueAt, h]

open Classical in
/-- `ℝ^J ≃ ℝ × ℝ^{J ∖ {c₀}}`. -/
noncomputable def splitAt' (c₀ : J) : (J → ℝ) ≃ᵐ ℝ × ({c : J // c ≠ c₀} → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => ℝ) (· = c₀)).trans
    ((MeasurableEquiv.funUnique {c : J // c = c₀} ℝ).prodCongr (MeasurableEquiv.refl _))

omit [Fintype J] in
open Classical in
theorem splitAt'_symm_apply (c₀ : J) (z : ℝ × ({c : J // c ≠ c₀} → ℝ)) :
    (splitAt' c₀).symm z = glueAt c₀ z.1 z.2 := rfl

open Classical in
theorem measurePreserving_splitAt' (c₀ : J) :
    MeasurePreserving (splitAt' c₀) volume ((volume : Measure ℝ).prod volume) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : J => (volume : Measure ℝ)) (· = c₀)
  have h2 := measurePreserving_funUnique (volume : Measure ℝ) {c : J // c = c₀}
  refine (h2.prod (MeasurePreserving.id _)).comp ?_
  convert h1 using 3

/-- **Fubini at one coordinate.** -/
theorem integral_eq_integral_glueAt (c₀ : J) {H : (J → ℝ) → ℂ} (hH : Integrable H) :
    ∫ τ, H τ = ∫ s, ∫ τ', H (glueAt c₀ s τ') := by
  have hE := MeasurePreserving.symm (splitAt' c₀) (measurePreserving_splitAt' c₀)
  have hint : Integrable (fun z : ℝ × ({c : J // c ≠ c₀} → ℝ) => H (glueAt c₀ z.1 z.2))
      ((volume : Measure ℝ).prod volume) :=
    (hE.integrable_comp_emb (splitAt' c₀).symm.measurableEmbedding).2 hH
  rw [← hE.integral_comp' H]
  exact integral_prod _ hint

/-- Integrals over `ℝ^α` and `ℝ^β` agree along an equivalence `α ≃ β`. -/
theorem integral_equiv_congr {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (G : (β → ℝ) → ℂ) :
    ∫ τ : α → ℝ, G (fun b => τ (e.symm b)) = ∫ σ : β → ℝ, G σ := by
  have hmp := measurePreserving_piCongrLeft (fun _ : β => (volume : Measure ℝ)) e
  have := hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : β => ℝ) e) G
  have key : (fun τ : α → ℝ => G (fun b => τ (e.symm b))) =
      fun τ => G ((MeasurableEquiv.piCongrLeft (fun _ : β => ℝ) e) τ) := by
    funext τ
    congr 1
    funext b
    show τ (e.symm b) = Equiv.piCongrLeft (fun _ => ℝ) e τ b
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  rw [key]
  exact this

end Generic

/-! ## Times decrease towards the root -/

section Chain

variable {T : TTree}

/-- `lt_root_of_isChildOf` (SysDraft DuhTime) for any tree and any root branch. -/
theorem lt_root_of_ordered (r₀ : GBranch (single T)) (hr₀ : r₀.1.2 = []) {τ : GBranch (single T) → ℝ}
    (hτ : ∀ b b' : GBranch (single T), b'.IsChildOf b → τ b' < τ b) :
    ∀ c : GBranch (single T), c.1.2 ≠ [] → τ c < τ r₀ := by
  intro c
  induction h : c.1.2.length using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro hc
    have hsplit := List.dropLast_append_getLast hc
    have hmem : c.1.2.dropLast ∈ (T).branching := by
      refine TTree.branching_of_append_mem _ (i := c.1.2.getLast hc) ?_
      rw [hsplit]
      exact TTree.branching_subset_nodes _ c.2
    let c' : GBranch (single T) := ⟨(0, c.1.2.dropLast), hmem⟩
    have hchild : c.IsChildOf c' := ⟨Subsingleton.elim _ _, c.1.2.getLast hc, hsplit.symm⟩
    have hlt := hτ c' c hchild
    by_cases hq : c.1.2.dropLast = []
    · have : c' = r₀ := GBranch.ext_path (hq.trans hr₀.symm)
      rw [← this]
      exact hlt
    · have hlen : c'.1.2.length < k := by
        rw [← h]
        show c.1.2.dropLast.length < c.1.2.length
        rw [List.length_dropLast]
        have := List.length_pos_of_ne_nil hc
        omega
      exact hlt.trans (ih _ hlen c' rfl hq)

end Chain

/-! ## The flower tree: root, patterns, phases -/

section Tree

variable (L γ δ : ℝ) {d : ℕ} {F : FTree}

theorem continuous_glueAt {J : Type*} [DecidableEq J] (c₀ : J) (s : ℝ) : Continuous (glueAt c₀ s) := by
  refine continuous_pi fun c => ?_
  unfold glueAt
  split_ifs with h
  · exact continuous_const
  · exact continuous_apply _

theorem nil_mem_branching_toTree (hF : F ≠ flower) : ([] : TTree.Path) ∈ F.toTree.branching := by
  cases F with
  | flower => exact absurd rfl hF
  | node i F T₁ T₂ =>
    unfold FTree.toTree
    split_ifs <;> simp [TTree.branching]

/-- The root branch of a flower tree. -/
def rootBr (hF : F ≠ flower) : GBranch (single F.toTree) := ⟨(0, []), nil_mem_branching_toTree hF⟩

theorem eq_rootBr_iff (hF : F ≠ flower) (b : GBranch (single F.toTree)) : b = rootBr hF ↔ b.1.2 = [] :=
  ⟨fun h => h ▸ rfl, fun h => GBranch.ext_path h⟩

theorem child_path_ne_nil {T : TTree} {b b' : GBranch (single T)} (h : b'.IsChildOf b) : b'.1.2 ≠ [] := by
  obtain ⟨-, i, hi⟩ := h
  rw [hi]
  simp

theorem rootBr_ne_flowerParent (hF : F ≠ flower) (hpr : (F.flowerParent hF).1.2 ≠ []) :
    rootBr hF ≠ F.flowerParent hF := fun h => hpr (by rw [← h]; rfl)

/-- The root branch, as a free coordinate of the plain pattern. -/
def rootBr' (hF : F ≠ flower) (hpr : (F.flowerParent hF).1.2 ≠ []) : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} :=
  ⟨rootBr hF, rootBr_ne_flowerParent hF hpr⟩

theorem norm_phaseOffT_le (T : TTree) (off : Finset (GBranch (single T))) (κ : GNode (single T) → (Fin d → ℤ))
    (τ : GBranch (single T) → ℝ) : ‖phaseOffT L γ δ T off κ τ‖ ≤ 1 := by
  unfold phaseOffT
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun c _ => ?_
  split_ifs
  · simp
  · exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

theorem continuous_phaseOffT (T : TTree) (off : Finset (GBranch (single T))) (κ : GNode (single T) → (Fin d → ℤ)) :
    Continuous (phaseOffT L γ δ T off κ) := by
  unfold phaseOffT
  refine continuous_finsetProd _ fun c _ => ?_
  split_ifs
  · exact continuous_const
  · fun_prop

/-- The integrand on full time vectors: domain `𝒟(t)` and phases. -/
noncomputable def HT (p : ℕ) (T : TTree) (off : Finset (GBranch (single T))) (κ : GNode (single T) → (Fin d → ℤ))
    (t : ℝ) (x : GBranch (single T) → ℝ) : ℂ :=
  (treeTimeDomain T p t).indicator (phaseOffT L γ δ T off κ) x

theorem integrable_HT_glue (p : ℕ) (T : TTree) (off : Finset (GBranch (single T)))
    (κ : GNode (single T) → (Fin d → ℤ)) (t : ℝ) (c₀ : GBranch (single T)) (s : ℝ) :
    Integrable fun σ : {b : GBranch (single T) // b ≠ c₀} → ℝ => HT L γ δ p T off κ t (glueAt c₀ s σ) := by
  set Box : Set ({b : GBranch (single T) // b ≠ c₀} → ℝ) := Set.pi univ fun _ => Icc (p : ℝ) t
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBc : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
  have hbound : Integrable (Box.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBc.measure_lt_top.ne)
  have hmeas : StronglyMeasurable fun σ : {b : GBranch (single T) // b ≠ c₀} → ℝ =>
      HT L γ δ p T off κ t (glueAt c₀ s σ) :=
    ((continuous_phaseOffT L γ δ T off κ).stronglyMeasurable.indicator
      (measurableSet_treeTimeDomain T p t)).comp_measurable (continuous_glueAt c₀ s).measurable
  refine hbound.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun σ => ?_)
  unfold HT
  by_cases hm : glueAt c₀ s σ ∈ treeTimeDomain T p t
  · rw [Set.indicator_of_mem hm]
    have hσ : σ ∈ Box := fun b _ => by
      have h := hm b.1
      rw [glueAt_ne c₀ s σ b.2] at h
      exact ⟨h.1.le, h.2.1.le⟩
    rw [Set.indicator_of_mem hσ]
    exact norm_phaseOffT_le L γ δ T off κ _
  · rw [Set.indicator_of_notMem hm, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

end Tree

/-! ## The slices -/

section Slices

variable (L γ δ : ℝ) {d : ℕ} {F : FTree} (hF : F ≠ flower) (p : ℕ) (off : Finset (GBranch (single F.toTree)))
  (κ : GNode (single F.toTree) → (Fin d → ℤ))

include hF in
/-- **The plain pattern**: the time integral is that of `𝒟(t)` with `t_{𝔣^pr} := s`. -/
theorem timeInt_plain_eq {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (ht : t ≤ p + 1) :
    ∫ τ : {b // treeFixPat F hF .plain t s b = none} → ℝ,
      (treeDomFix p F.toTree t (treeFixPat F hF .plain t s)).indicator (phaseOffT L γ δ F.toTree off κ)
        (extendFixT (treeFixPat F hF .plain t s) τ) =
    ∫ σ : {b // b ≠ F.flowerParent hF} → ℝ, HT L γ δ p F.toTree off κ t (glueAt (F.flowerParent hF) s σ) := by
  classical
  have hfix : ∀ b, treeFixPat F hF .plain t s b = none ↔ b ≠ F.flowerParent hF := by
    intro b
    unfold treeFixPat
    by_cases h : b = F.flowerParent hF <;> simp [h]
  rw [← WaveTurbulence.FlowerProbes.integral_subtype_congr hfix
    (fun σ => HT L γ δ p F.toTree off κ t (glueAt (F.flowerParent hF) s σ))]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  set x := glueAt (F.flowerParent hF) s (fun q : {b // b ≠ F.flowerParent hF} => τ ⟨q.1, (hfix q.1).2 q.2⟩)
    with hx
  have hxf : x (F.flowerParent hF) = s := by rw [hx, glueAt_self]
  have hxo : ∀ b (hb : b ≠ F.flowerParent hF), x b = τ ⟨b, (hfix b).2 hb⟩ := fun b hb => by
    rw [hx, glueAt_ne _ _ _ hb]
  have hext : extendFixT (treeFixPat F hF .plain t s) τ = x := by
    funext b
    unfold extendFixT
    split
    · next v hv =>
      by_cases hb : b = F.flowerParent hF
      · subst hb
        unfold treeFixPat at hv
        simp only [↓reduceIte, Option.some.injEq] at hv
        rw [hxf, hv]
      · exfalso
        unfold treeFixPat at hv
        simp [hb] at hv
    · next hv =>
      rw [hxo b ((hfix b).1 hv)]
  have hdom : x ∈ treeDomFix p F.toTree t (treeFixPat F hF .plain t s) ↔ x ∈ treeTimeDomain F.toTree p t := by
    constructor
    · intro h b
      refine ⟨?_, ?_, fun b' hb' => ?_⟩
      · by_cases hb : b = F.flowerParent hF
        · rw [hb, hxf]; exact hps
        · exact ((h b).1 ((hfix b).2 hb)).1
      · by_cases hb : b = F.flowerParent hF
        · rw [hb, hxf]; exact hst
        · exact ((h b).1 ((hfix b).2 hb)).2.2.2
      · refine (h b).2 b' hb' ?_
        by_cases hb1 : b' = F.flowerParent hF
        · right
          exact (hfix b).2 fun e => WaveTurbulence.X2Probes.isChildOf_ne hb' (hb1.trans e.symm)
        · left
          exact (hfix b').2 hb1
    · intro h b
      refine ⟨fun hb => ?_, fun b' hb' _ => (h b).2.2 b' hb'⟩
      obtain ⟨h1, h2, -⟩ := h b
      exact ⟨h1, by linarith, by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith, h2⟩
  beta_reduce
  rw [hext]
  unfold HT
  by_cases hm : x ∈ treeTimeDomain F.toTree p t
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hdom.2 hm)]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hdom.1 h))]

variable (hpr : (F.flowerParent hF).1.2 ≠ [])

theorem treeFixPat_dRoot_eq_none (u s : ℝ) (b : GBranch (single F.toTree)) :
    treeFixPat F hF .dRoot u s b = none ↔ b ≠ F.flowerParent hF ∧ b ≠ rootBr hF := by
  by_cases h1 : b = F.flowerParent hF
  · have : treeFixPat F hF .dRoot u s b = some s := by unfold treeFixPat; simp [h1]
    rw [this]
    simp [h1]
  · by_cases h2 : b.1.2 = []
    · have : treeFixPat F hF .dRoot u s b = some u := by unfold treeFixPat; simp [h1, h2]
      rw [this]
      simp [(eq_rootBr_iff hF b).2 h2]
    · have : treeFixPat F hF .dRoot u s b = none := by unfold treeFixPat; simp [h1, h2]
      simp only [this, true_iff]
      exact ⟨h1, fun e => h2 ((eq_rootBr_iff hF b).1 e)⟩

include hpr in
/-- **The `dRoot` pattern**: the time integral is the root slice of `𝒟(t)` at `t_𝔯 = u`, for `s < u < t`. -/
theorem timeInt_dRoot_eq {t s u : ℝ} (hps : (p : ℝ) < s) (hsu : s < u) (hut : u < t) (ht : t ≤ p + 1) :
    ∫ τ : {b // treeFixPat F hF .dRoot u s b = none} → ℝ,
      (treeDomFix p F.toTree u (treeFixPat F hF .dRoot u s)).indicator (phaseOffT L γ δ F.toTree off κ)
        (extendFixT (treeFixPat F hF .dRoot u s) τ) =
    ∫ σ' : {x : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} // x ≠ rootBr' hF hpr} → ℝ,
      HT L γ δ p F.toTree off κ t (glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ')) := by
  classical
  have hfix := treeFixPat_dRoot_eq_none hF u s
  let e : {x : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} // x ≠ rootBr' hF hpr} ≃
      {b // treeFixPat F hF .dRoot u s b = none} :=
    { toFun := fun x => ⟨x.1.1, (hfix _).2 ⟨x.1.2, fun hr => x.2 (Subtype.ext hr)⟩⟩
      invFun := fun b => ⟨⟨b.1, ((hfix _).1 b.2).1⟩, fun hr => ((hfix _).1 b.2).2 (congrArg Subtype.val hr)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← integral_equiv_congr e (fun σ => (treeDomFix p F.toTree u (treeFixPat F hF .dRoot u s)).indicator
    (phaseOffT L γ δ F.toTree off κ) (extendFixT (treeFixPat F hF .dRoot u s) σ))]
  refine integral_congr_ae (ae_of_all _ fun σ' => ?_)
  set x := glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ') with hx
  have hxf : x (F.flowerParent hF) = s := by rw [hx, glueAt_self]
  have hxr : x (rootBr hF) = u := by
    rw [hx, glueAt_ne _ _ _ (rootBr_ne_flowerParent hF hpr)]
    exact glueAt_self _ _ _
  have hxo : ∀ b (hb1 : b ≠ F.flowerParent hF) (hb2 : b ≠ rootBr hF),
      x b = σ' ⟨⟨b, hb1⟩, fun h => hb2 (congrArg Subtype.val h)⟩ := fun b hb1 hb2 => by
    rw [hx, glueAt_ne _ _ _ hb1, glueAt_ne _ _ _ (fun h => hb2 (congrArg Subtype.val h))]
  have hext : extendFixT (treeFixPat F hF .dRoot u s) (fun b => σ' (e.symm b)) = x := by
    funext b
    unfold extendFixT
    split
    · next v hv =>
      by_cases hb : b = F.flowerParent hF
      · subst hb
        unfold treeFixPat at hv
        simp only [↓reduceIte, Option.some.injEq] at hv
        rw [hxf, hv]
      · by_cases hr : b = rootBr hF
        · subst hr
          unfold treeFixPat at hv
          simp only [rootBr_ne_flowerParent hF hpr, ↓reduceIte] at hv
          have : (rootBr hF).1.2 = [] := rfl
          simp only [this, ↓reduceIte, Option.some.injEq] at hv
          rw [hxr, hv]
        · exfalso
          exact (Option.some_ne_none v) (hv.symm.trans ((hfix b).2 ⟨hb, hr⟩))
    · next hv =>
      obtain ⟨hb1, hb2⟩ := (hfix b).1 hv
      rw [hxo b hb1 hb2]
      rfl
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hdom : x ∈ treeDomFix p F.toTree u (treeFixPat F hF .dRoot u s) ↔ x ∈ treeTimeDomain F.toTree p t := by
    constructor
    · intro h b
      by_cases hb1 : b = F.flowerParent hF
      · subst hb1
        refine ⟨by rw [hxf]; exact hps, by rw [hxf]; linarith, fun b' hb' => ?_⟩
        refine (h _).2 b' hb' (Or.inl ((hfix b').2 ⟨fun e => WaveTurbulence.X2Probes.isChildOf_ne hb' e, ?_⟩))
        intro e
        exact child_path_ne_nil hb' ((eq_rootBr_iff hF b').1 e)
      · by_cases hb2 : b = rootBr hF
        · subst hb2
          refine ⟨by rw [hxr]; linarith, by rw [hxr]; exact hut, fun b' hb' => ?_⟩
          by_cases hb'1 : b' = F.flowerParent hF
          · rw [hb'1, hxf, hxr]; exact hsu
          · refine (h _).2 b' hb' (Or.inl ((hfix b').2 ⟨hb'1, ?_⟩))
            intro e
            exact child_path_ne_nil hb' ((eq_rootBr_iff hF b').1 e)
        · obtain ⟨h1, -, -, h4⟩ := (h b).1 ((hfix b).2 ⟨hb1, hb2⟩)
          exact ⟨h1, by linarith, fun b' hb' => (h b).2 b' hb' (Or.inr ((hfix b).2 ⟨hb1, hb2⟩))⟩
    · intro h b
      have hord : ∀ c c' : GBranch (single F.toTree), c'.IsChildOf c → x c' < x c :=
        fun c c' hc => (h c).2.2 c' hc
      refine ⟨fun hb => ?_, fun b' hb' _ => (h b).2.2 b' hb'⟩
      obtain ⟨hb1, hb2⟩ := (hfix b).1 hb
      have hlt : x b < u := by
        rw [← hxr]
        exact lt_root_of_ordered (rootBr hF) rfl hord b (fun e => hb2 ((eq_rootBr_iff hF b).2 e))
      exact ⟨(h b).1, by linarith, by linarith [(h b).1], hlt⟩
  beta_reduce
  rw [hext]
  unfold HT
  by_cases hm : x ∈ treeTimeDomain F.toTree p t
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hdom.2 hm)]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hdom.1 h))]

include hpr in
/-- The root slice is empty for `u ∉ (s, t)`. -/
theorem HT_glue_eq_zero {t s u : ℝ} (hu : u ∉ Ioo s t)
    (σ' : {x : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} // x ≠ rootBr' hF hpr} → ℝ) :
    HT L γ δ p F.toTree off κ t (glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ')) = 0 := by
  set x := glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ') with hx
  have hxf : x (F.flowerParent hF) = s := by rw [hx, glueAt_self]
  have hxr : x (rootBr hF) = u := by
    rw [hx, glueAt_ne _ _ _ (rootBr_ne_flowerParent hF hpr)]
    exact glueAt_self _ _ _
  unfold HT
  refine Set.indicator_of_notMem (fun h => hu ⟨?_, ?_⟩) _
  · have := lt_root_of_ordered (rootBr hF) rfl (fun c c' hc => (h c).2.2 c' hc) (F.flowerParent hF) hpr
    rwa [hxf, hxr] at this
  · have := (h (rootBr hF)).2.1
    rwa [hxr] at this

/-- The time integral of a decoration for the pattern `pat` (the integral in `flowerKernelGen`). -/
noncomputable def TIpat (pat : FixPat) (t s : ℝ) : ℂ :=
  ∫ τ : {b // treeFixPat F hF pat t s b = none} → ℝ,
    (treeDomFix p F.toTree t (treeFixPat F hF pat t s)).indicator (phaseOffT L γ δ F.toTree off κ)
      (extendFixT (treeFixPat F hF pat t s) τ)

omit hF in
theorem extendFixT_free {T : TTree} (fix : GBranch (single T) → Option ℝ) (τ : {b // fix b = none} → ℝ)
    (b : {b // fix b = none}) : extendFixT fix τ b.1 = τ b := by
  unfold extendFixT
  split
  · next v hv => exact absurd (hv.symm.trans b.2) (by simp)
  · next hv => rfl

omit hpr in
theorem norm_TIpat_le_one (pat : FixPat) (t s : ℝ) : ‖TIpat L γ δ hF p off κ pat t s‖ ≤ 1 := by
  unfold TIpat
  set Box : Set ({b // treeFixPat F hF pat t s b = none} → ℝ) := Set.pi univ fun _ => Icc (p : ℝ) (p + 1)
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hvol : volume Box = 1 := by
    rw [volume_pi_pi]
    simp [Real.volume_Icc]
  have hint : Integrable (Box.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top))
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun τ => ?_)).trans (le_of_eq ?_)
  · by_cases hm : extendFixT (treeFixPat F hF pat t s) τ ∈ treeDomFix p F.toTree t (treeFixPat F hF pat t s)
    · rw [Set.indicator_of_mem hm]
      have hτ : τ ∈ Box := fun b _ => by
        have h := (hm b.1).1 b.2
        rw [extendFixT_free] at h
        exact ⟨h.1.le, h.2.1.le⟩
      rw [Set.indicator_of_mem hτ]
      exact norm_phaseOffT_le L γ δ F.toTree off κ _
    · rw [Set.indicator_of_notMem hm, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · rw [integral_indicator hBm, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, hvol]
    simp

include hpr in
/-- **The decoration-level FTC**: `TI_plain(t) = ∫_s^t TI_dRoot(u) du`. -/
theorem TIpat_plain_eq_integral {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (ht : t ≤ p + 1) :
    TIpat L γ δ hF p off κ .plain t s = ∫ u in s..t, TIpat L γ δ hF p off κ .dRoot u s := by
  unfold TIpat
  rw [timeInt_plain_eq L γ δ hF p off κ hps hst ht,
    integral_eq_integral_glueAt (rootBr' hF hpr) (integrable_HT_glue L γ δ p F.toTree off κ t _ s)]
  have hslice : ∀ u, ∫ σ', HT L γ δ p F.toTree off κ t
      (glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ')) =
      (Ioo s t).indicator (fun u => ∫ τ : {b // treeFixPat F hF .dRoot u s b = none} → ℝ,
        (treeDomFix p F.toTree u (treeFixPat F hF .dRoot u s)).indicator (phaseOffT L γ δ F.toTree off κ)
          (extendFixT (treeFixPat F hF .dRoot u s) τ)) u := by
    intro u
    by_cases hu : u ∈ Ioo s t
    · rw [Set.indicator_of_mem hu]
      exact (timeInt_dRoot_eq L γ δ hF p off κ hpr hps hu.1 hu.2 ht).symm
    · rw [Set.indicator_of_notMem hu]
      simp only [HT_glue_eq_zero L γ δ hF p off κ hpr hu, integral_zero]
  simp_rw [hslice]
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le hst.le,
    integral_Ioc_eq_integral_Ioo]

omit hpr in
/-- **Flower parent at the root**: `TI_plain(t)` does not depend on `t ∈ (s, p+1]`. -/
theorem TIpat_plain_const (hpr0 : (F.flowerParent hF).1.2 = []) {t t₀ s : ℝ} (hps : (p : ℝ) < s)
    (hst : s < t) (ht : t ≤ p + 1) (hst₀ : s < t₀) (ht₀ : t₀ ≤ p + 1) :
    TIpat L γ δ hF p off κ .plain t s = TIpat L γ δ hF p off κ .plain t₀ s := by
  unfold TIpat
  rw [timeInt_plain_eq L γ δ hF p off κ hps hst ht, timeInt_plain_eq L γ δ hF p off κ hps hst₀ ht₀]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  set x := glueAt (F.flowerParent hF) s σ with hx
  have hxf : x (F.flowerParent hF) = s := by rw [hx, glueAt_self]
  have hroot : F.flowerParent hF = rootBr hF := (eq_rootBr_iff hF _).2 hpr0
  have key : ∀ t' : ℝ, s < t' → (x ∈ treeTimeDomain F.toTree p t' ↔
      ∀ b, (p : ℝ) < x b ∧ ∀ b' : GBranch (single F.toTree), b'.IsChildOf b → x b' < x b) := by
    intro t' hst'
    constructor
    · intro h b
      exact ⟨(h b).1, (h b).2.2⟩
    · intro h b
      refine ⟨(h b).1, ?_, (h b).2⟩
      by_cases hb : b.1.2 = []
      · rw [(eq_rootBr_iff hF b).2 hb, ← hroot, hxf]
        exact hst'
      · have := lt_root_of_ordered (rootBr hF) rfl (fun c c' hc => (h c).2 c' hc) b hb
        rw [← hroot, hxf] at this
        linarith
  show HT L γ δ p F.toTree off κ t x = HT L γ δ p F.toTree off κ t₀ x
  unfold HT
  by_cases hm : ∀ b, (p : ℝ) < x b ∧ ∀ b' : GBranch (single F.toTree), b'.IsChildOf b → x b' < x b
  · rw [Set.indicator_of_mem ((key t hst).2 hm), Set.indicator_of_mem ((key t₀ hst₀).2 hm)]
  · rw [Set.indicator_of_notMem (fun h => hm ((key t hst).1 h)),
      Set.indicator_of_notMem (fun h => hm ((key t₀ hst₀).1 h))]

end Slices

/-! ## The kernels -/

section Kernels

variable (L γ δ : ℝ) {d : ℕ}

theorem chi0_mem_Icc (x : ℝ) : chi0 x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem abs_dyadicCut_le_one (L' : ℝ) (j : ℕ) (x : ℝ) : |dyadicCut L' j x| ≤ 1 := by
  unfold dyadicCut
  split_ifs
  · rw [abs_le]
    exact ⟨by linarith [(chi0_mem_Icc (x / L')).1], (chi0_mem_Icc _).2⟩
  · have h1 := chi0_mem_Icc (x / (2 ^ j * L'))
    have h2 := chi0_mem_Icc (x / (2 ^ (j - 1) * L'))
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_treeWeight_le_one {F : FTree} (hF : F ≠ flower) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    |treeWeight L F hF dagger cut1 cut2 κ| ≤ 1 := by
  unfold treeWeight
  rw [abs_mul, abs_mul]
  have h1 : |cut1.elim 1 fun j₁ => treeCut1 L F j₁ κ| ≤ 1 := by
    cases cut1 with
    | none => simp
    | some j => exact abs_dyadicCut_le_one L j _
  have h2 : |cut2.elim 1 fun j₂ => treeCut2 L F hF j₂ κ| ≤ 1 := by
    cases cut2 with
    | none => simp
    | some j => exact abs_dyadicCut_le_one L j _
  have h3 : |dagger.elim 1 fun c => treeSib L F hF c κ| ≤ 1 := by
    cases dagger with
    | none => simp
    | some c =>
      show |treeSib L F hF c κ| ≤ 1
      unfold treeSib
      rw [Finset.abs_prod]
      refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
      split_ifs <;> simp
  calc |cut1.elim 1 fun j₁ => treeCut1 L F j₁ κ| * |cut2.elim 1 fun j₂ => treeCut2 L F hF j₂ κ| *
        |dagger.elim 1 fun c => treeSib L F hF c κ| ≤ 1 * 1 * 1 := by
        gcongr
    _ = 1 := by ring

/-- The leaf product of `flowerKernelGen`: `∏_{ℓ≠𝔣} a_{κ_ℓ}(p)^{ζ_ℓ}` (OFK's `restProd`). -/
noncomputable def restP (F : FTree) (aP : (Fin d → ℤ) → ℂ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) : ℂ :=
  ∏ ℓ ∈ Finset.univ.erase F.flowerLeaf, zpowSign (treeSign F.toTree ℓ.toNode) (aP (κ ℓ.toNode))

theorem summable_restP (F : FTree) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) (k k' : Fin d → ℤ) :
    Summable fun κ : FlowerDecoration F d k k' => ‖restP F aP κ.1.1‖ := by
  classical
  let f : GLeaf (single F.toTree) → (Fin d → ℤ) → ℝ := fun ℓ m =>
    if ℓ = F.flowerLeaf then (if m = k' then 1 else 0) else ‖aP m‖
  have hf0 : ∀ ℓ m, 0 ≤ f ℓ m := fun ℓ m => by
    simp only [f]; split_ifs <;> first | exact norm_nonneg _ | norm_num
  have hf : ∀ ℓ, Summable (f ℓ) := fun ℓ => by
    by_cases hℓ : ℓ = F.flowerLeaf
    · simp only [f, hℓ, ↓reduceIte]
      exact summable_of_ne_finset_zero (s := {k'}) fun m hm => by simp_all
    · simp only [f, hℓ, ↓reduceIte]
      exact haP
  have hP := summable_pi_prod f hf0 hf
  let Φ : FlowerDecoration F d k k' → (GLeaf (single F.toTree) → (Fin d → ℤ)) := fun κ ℓ => κ.1.1 ℓ.toNode
  have hΦ : Function.Injective Φ := fun κ κ' h =>
    Subtype.ext (Subtype.ext (treeDecoration_eq_of_leaves κ.1 κ'.1 fun ℓ => congrFun h ℓ))
  refine (hP.comp_injective hΦ).congr fun κ => ?_
  simp only [Function.comp, Φ, restP, norm_prod, norm_zpowSign]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ F.flowerLeaf)]
  simp only [f, ↓reduceIte, κ.2, one_mul]
  refine Finset.prod_congr rfl fun ℓ hℓ => ?_
  simp only [Finset.ne_of_mem_erase hℓ, ↓reduceIte]

instance instCountableFlowerDecoration (F : FTree) (d : ℕ) (k k' : Fin d → ℤ) :
    Countable (FlowerDecoration F d k k') :=
  inferInstanceAs (Countable {κ : TreeDecoration F.toTree d k // κ.1 F.flowerLeaf.toNode = k'})

theorem continuous_glueAt₂ {J : Type*} [DecidableEq J] (c₀ : J) :
    Continuous fun z : ℝ × ({c : J // c ≠ c₀} → ℝ) => glueAt c₀ z.1 z.2 := by
  refine continuous_pi fun c => ?_
  unfold glueAt
  split_ifs with h
  · exact continuous_fst
  · exact (continuous_apply _).comp continuous_snd

variable {F : FTree} (hF : F ≠ flower) (p : ℕ)

theorem flowerKernelGen_eq (aP : (Fin d → ℤ) → ℂ) (pat : FixPat) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (t s : ℝ) (k k' : Fin d → ℤ) :
    flowerKernelGen L γ δ p F aP pat dagger cut1 cut2 t s k k' =
      treePrefactor L γ δ d F.toTree * ∑' κ : FlowerDecoration F d k k',
        epsProd F.toTree κ.1.1 * (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ) *
          TIpat L γ δ hF p (if dagger.isSome then {F.flowerParent hF} else ∅) κ.1.1 pat t s *
            restP F aP κ.1.1 := by
  unfold flowerKernelGen
  simp only [hF, ↓reduceDIte]
  rfl

theorem stronglyMeasurable_slice (hpr : (F.flowerParent hF).1.2 ≠ []) (off : Finset (GBranch (single F.toTree)))
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) (t s : ℝ) :
    StronglyMeasurable fun u => ∫ σ', HT L γ δ p F.toTree off κ t
      (glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ')) := by
  have hH : StronglyMeasurable (HT L γ δ p F.toTree off κ t) :=
    (continuous_phaseOffT L γ δ F.toTree off κ).stronglyMeasurable.indicator (measurableSet_treeTimeDomain _ _ _)
  have hg : Continuous fun z : ℝ × ({x : {b : GBranch (single F.toTree) // b ≠ F.flowerParent hF} //
      x ≠ rootBr' hF hpr} → ℝ) => glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) z.1 z.2) :=
    (continuous_glueAt (F.flowerParent hF) s).comp (continuous_glueAt₂ (rootBr' hF hpr))
  exact (hH.comp_measurable hg.measurable).integral_prod_right'

/-- **`∂_t` of one flower kernel is its `dRoot` kernel**: `𝒦^{plain}(t, s) = ∫_s^t 𝒦^{dRoot}(u, s) du`. -/
theorem flowerKernelGen_plain_eq_integral (hpr : (F.flowerParent hF).1.2 ≠ []) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) {t s : ℝ}
    (hps : (p : ℝ) < s) (hst : s < t) (ht : t ≤ p + 1) (k k' : Fin d → ℤ) :
    flowerKernelGen L γ δ p F aP .plain dagger cut1 cut2 t s k k' =
      ∫ u in s..t, flowerKernelGen L γ δ p F aP .dRoot dagger cut1 cut2 u s k k' := by
  set off : Finset (GBranch (single F.toTree)) := if dagger.isSome then {F.flowerParent hF} else ∅
  set c : FlowerDecoration F d k k' → ℂ := fun κ =>
    epsProd F.toTree κ.1.1 * (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ)
  have hc : ∀ κ, ‖c κ‖ ≤ 1 := fun κ => by
    simp only [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖epsProd F.toTree κ.1.1‖ * |treeWeight L F hF dagger cut1 cut2 κ.1.1| ≤ 1 * 1 :=
          mul_le_mul (norm_epsProd_le _ _) (abs_treeWeight_le_one L hF dagger cut1 cut2 _) (abs_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have hR := summable_restP F haP k k'
  -- the slice, measurable, equal to the `dRoot` time integral on `(s, t)`
  set S : FlowerDecoration F d k k' → ℝ → ℂ := fun κ u => ∫ σ', HT L γ δ p F.toTree off κ.1.1 t
    (glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ'))
  have hSeq : ∀ κ, ∀ u ∈ Ioo s t, S κ u = TIpat L γ δ hF p off κ.1.1 .dRoot u s := fun κ u hu =>
    (timeInt_dRoot_eq L γ δ hF p off κ.1.1 hpr hps hu.1 hu.2 ht).symm
  have hae : ∀ κ, (fun u => c κ * TIpat L γ δ hF p off κ.1.1 .dRoot u s * restP F aP κ.1.1) =ᵐ[volume.restrict (Ioc s t)]
      fun u => c κ * S κ u * restP F aP κ.1.1 := by
    intro κ
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    have hnull : volume ({t} : Set ℝ) = 0 := measure_singleton t
    refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun u hu huI => ?_
    have huo : u ∈ Ioo s t := ⟨huI.1, lt_of_le_of_ne huI.2 hu⟩
    rw [hSeq κ u huo]
  have hmeas : ∀ κ, AEStronglyMeasurable (fun u => c κ * TIpat L γ δ hF p off κ.1.1 .dRoot u s * restP F aP κ.1.1)
      (volume.restrict (Ioc s t)) := fun κ =>
    (((stronglyMeasurable_const.mul (stronglyMeasurable_slice L γ δ hF p hpr off κ.1.1 t s)).mul
      stronglyMeasurable_const).aestronglyMeasurable).congr (hae κ).symm
  have hbound : ∀ κ, ∫⁻ u in Ioc s t, ‖c κ * TIpat L γ δ hF p off κ.1.1 .dRoot u s * restP F aP κ.1.1‖ₑ ≤
      ENNReal.ofReal ‖restP F aP κ.1.1‖ * volume (Ioc s t) := fun κ => by
    rw [← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun u _ => ?_
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, norm_mul]
    calc ‖c κ‖ * ‖TIpat L γ δ hF p off κ.1.1 .dRoot u s‖ * ‖restP F aP κ.1.1‖ ≤ 1 * 1 * ‖restP F aP κ.1.1‖ := by
          gcongr
          · exact hc κ
          · exact norm_TIpat_le_one L γ δ hF p off κ.1.1 _ _ _
      _ = _ := by ring
  have hfin : ∑' κ, ∫⁻ u in Ioc s t, ‖c κ * TIpat L γ δ hF p off κ.1.1 .dRoot u s * restP F aP κ.1.1‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hR]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  rw [flowerKernelGen_eq L γ δ hF p, intervalIntegral.integral_of_le hst.le]
  simp_rw [flowerKernelGen_eq L γ δ hF p]
  rw [integral_const_mul]
  congr 1
  rw [integral_tsum hmeas hfin]
  refine tsum_congr fun κ => ?_
  rw [TIpat_plain_eq_integral L γ δ hF p off κ.1.1 hpr hps hst ht, intervalIntegral.integral_of_le hst.le,
    integral_mul_const, integral_const_mul]

theorem norm_slice_le (hpr : (F.flowerParent hF).1.2 ≠ []) (off : Finset (GBranch (single F.toTree)))
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) {t s : ℝ} (hps : (p : ℝ) < s) (ht : t ≤ p + 1) (u : ℝ) :
    ‖∫ σ', HT L γ δ p F.toTree off κ t (glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ'))‖ ≤ 1 := by
  by_cases hu : u ∈ Ioo s t
  · rw [← timeInt_dRoot_eq L γ δ hF p off κ hpr hps hu.1 hu.2 ht]
    exact norm_TIpat_le_one L γ δ hF p off κ _ _ _
  · simp only [HT_glue_eq_zero L γ δ hF p off κ hpr hu, integral_zero, norm_zero, zero_le_one]

theorem intervalIntegrable_flowerKernelGen_dRoot (hpr : (F.flowerParent hF).1.2 ≠ []) {aP : (Fin d → ℤ) → ℂ}
    (haP : Summable fun k => ‖aP k‖) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) {b s : ℝ}
    (hps : (p : ℝ) < s) (hsb : s < b) (hb : b ≤ p + 1) (k k' : Fin d → ℤ) :
    IntervalIntegrable (fun u => flowerKernelGen L γ δ p F aP .dRoot dagger cut1 cut2 u s k k') volume s b := by
  set off : Finset (GBranch (single F.toTree)) := if dagger.isSome then {F.flowerParent hF} else ∅
  set c : FlowerDecoration F d k k' → ℂ := fun κ =>
    epsProd F.toTree κ.1.1 * (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ)
  have hc : ∀ κ, ‖c κ‖ ≤ 1 := fun κ => by
    simp only [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖epsProd F.toTree κ.1.1‖ * |treeWeight L F hF dagger cut1 cut2 κ.1.1| ≤ 1 * 1 :=
          mul_le_mul (norm_epsProd_le _ _) (abs_treeWeight_le_one L hF dagger cut1 cut2 _) (abs_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have hR := summable_restP F haP k k'
  set S : FlowerDecoration F d k k' → ℝ → ℂ := fun κ u => ∫ σ', HT L γ δ p F.toTree off κ.1.1 b
    (glueAt (F.flowerParent hF) s (glueAt (rootBr' hF hpr) u σ'))
  set pref := treePrefactor L γ δ d F.toTree
  have hG : StronglyMeasurable fun u => pref * ∑' κ, c κ * S κ u * restP F aP κ.1.1 := by
    refine stronglyMeasurable_const.mul (stronglyMeasurable_tsum' (fun κ => ?_) fun u => ?_)
    · exact (stronglyMeasurable_const.mul (stronglyMeasurable_slice L γ δ hF p hpr off κ.1.1 b s)).mul
        stronglyMeasurable_const
    · refine Summable.of_norm_bounded hR fun κ => ?_
      rw [norm_mul, norm_mul]
      calc ‖c κ‖ * ‖S κ u‖ * ‖restP F aP κ.1.1‖ ≤ 1 * 1 * ‖restP F aP κ.1.1‖ := by
            gcongr
            · exact hc κ
            · exact norm_slice_le L γ δ hF p hpr off κ.1.1 hps hb u
        _ = _ := by ring
  have hSeq : ∀ κ, ∀ u ∈ Ioo s b, S κ u = TIpat L γ δ hF p off κ.1.1 .dRoot u s := fun κ u hu =>
    (timeInt_dRoot_eq L γ δ hF p off κ.1.1 hpr hps hu.1 hu.2 hb).symm
  have hterm : ∀ u (κ : FlowerDecoration F d k k'),
      ‖c κ * TIpat L γ δ hF p off κ.1.1 .dRoot u s * restP F aP κ.1.1‖ ≤ ‖restP F aP κ.1.1‖ := fun u κ => by
    rw [norm_mul, norm_mul]
    calc ‖c κ‖ * ‖TIpat L γ δ hF p off κ.1.1 .dRoot u s‖ * ‖restP F aP κ.1.1‖ ≤ 1 * 1 * ‖restP F aP κ.1.1‖ := by
          gcongr
          · exact hc κ
          · exact norm_TIpat_le_one L γ δ hF p off κ.1.1 _ _ _
      _ = _ := by ring
  have hsum : ∀ u, Summable fun κ : FlowerDecoration F d k k' =>
      ‖c κ * TIpat L γ δ hF p off κ.1.1 .dRoot u s * restP F aP κ.1.1‖ := fun u =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm u) hR
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hsb.le]
  refine ⟨?_, MeasureTheory.HasFiniteIntegral.restrict_of_bounded
    (C := ‖pref‖ * ∑' κ : FlowerDecoration F d k k', ‖restP F aP κ.1.1‖) measure_Ioc_lt_top ?_⟩
  · refine hG.aestronglyMeasurable.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    refine (measure_eq_zero_iff_ae_notMem.1 (measure_singleton b)).mono fun u hu huI => ?_
    have huo : u ∈ Ioo s b := ⟨huI.1, lt_of_le_of_ne huI.2 hu⟩
    rw [flowerKernelGen_eq L γ δ hF p]
    congr 1
    refine tsum_congr fun κ => ?_
    rw [hSeq κ u huo]
  · refine Filter.Eventually.of_forall fun u => ?_
    rw [flowerKernelGen_eq L γ δ hF p, norm_mul]
    gcongr
    exact (norm_tsum_le_tsum_norm (hsum u)).trans (Summable.tsum_le_tsum (hterm u) (hsum u) hR)

/-- **Flower parent at the root**: the kernel does not depend on `t ∈ (s, p+1]`. -/
theorem flowerKernelGen_plain_const (hpr0 : (F.flowerParent hF).1.2 = []) (aP : (Fin d → ℤ) → ℂ)
    (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) {t t₀ s : ℝ} (hps : (p : ℝ) < s)
    (hst : s < t) (ht : t ≤ p + 1) (hst₀ : s < t₀) (ht₀ : t₀ ≤ p + 1) (k k' : Fin d → ℤ) :
    flowerKernelGen L γ δ p F aP .plain dagger cut1 cut2 t s k k' =
      flowerKernelGen L γ δ p F aP .plain dagger cut1 cut2 t₀ s k k' := by
  rw [flowerKernelGen_eq L γ δ hF p, flowerKernelGen_eq L γ δ hF p]
  congr 1
  refine tsum_congr fun κ => ?_
  rw [TIpat_plain_const L γ δ hF p _ κ.1.1 hpr0 hps hst ht hst₀ ht₀]

end Kernels

/-! ## The kernels of a kind -/

section Kind

variable (L γ δ : ℝ) {d : ℕ} (p Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
  (kind : FlowerKind) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ)

include haP in
/-- **`∂_t` of the random kernel of a kind**: for `p < s < t₀, t ≤ p+1`,
`𝒦^{plain}(t, s) = 𝒦^{plain}(t₀, s) + ∫_{t₀}^t 𝒦^{dRoot}(u, s) du`. -/
theorem randFlowerKernel_plain_sub {t₀ t s : ℝ} (hps : (p : ℝ) < s) (hst₀ : s < t₀) (ht₀ : t₀ ≤ p + 1)
    (hst : s < t) (ht : t ≤ p + 1) (k k' : Fin d → ℤ) :
    randFlowerKernel L γ δ p Ntr aP kind .plain dagger cut1 cut2 ζ t s k k' =
      randFlowerKernel L γ δ p Ntr aP kind .plain dagger cut1 cut2 ζ t₀ s k k' +
        ∫ u in t₀..t, randFlowerKernel L γ δ p Ntr aP kind .dRoot dagger cut1 cut2 ζ u s k k' := by
  classical
  have hint : ∀ F ∈ kindTrees Ntr kind, IntervalIntegrable (fun u =>
      if F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .dRoot then
        flowerKernelGen L γ δ p F aP .dRoot dagger cut1 cut2 u s k k' else 0) volume t₀ t := by
    intro F _
    split_ifs with h
    · obtain ⟨-, hF, hpr⟩ := h
      exact (intervalIntegrable_flowerKernelGen_dRoot L γ δ hF p hpr haP dagger cut1 cut2 hps hst₀ ht₀ k k').symm.trans
        (intervalIntegrable_flowerKernelGen_dRoot L γ δ hF p hpr haP dagger cut1 cut2 hps hst ht k k')
    · exact intervalIntegrable_const
  unfold randFlowerKernel
  simp only [Finset.sum_filter]
  rw [intervalIntegral.integral_finsetSum hint, ← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun F _ => ?_
  by_cases hF : F = flower
  · simp [hF]
  by_cases hζ : F.sign = ζ
  · have hplain : F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .plain := ⟨hζ, hF, trivial⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hplain), ite_eq_left_of_eq_true _ _ (eq_true hplain)]
    by_cases hpr : (F.flowerParent hF).1.2 = []
    · have hnd : ¬ (F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .dRoot) := fun ⟨_, hF', h⟩ => h hpr
      simp only [ite_eq_right_of_eq_false _ _ (eq_false hnd)]
      rw [intervalIntegral.integral_zero,
        flowerKernelGen_plain_const L γ δ hF p hpr aP dagger cut1 cut2 hps hst ht hst₀ ht₀, sub_self]
    · have hd : F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .dRoot := ⟨hζ, hF, hpr⟩
      simp only [ite_eq_left_of_eq_true _ _ (eq_true hd)]
      rw [flowerKernelGen_plain_eq_integral L γ δ hF p hpr haP dagger cut1 cut2 hps hst ht,
        flowerKernelGen_plain_eq_integral L γ δ hF p hpr haP dagger cut1 cut2 hps hst₀ ht₀,
        intervalIntegral.integral_interval_sub_left
          (intervalIntegrable_flowerKernelGen_dRoot L γ δ hF p hpr haP dagger cut1 cut2 hps hst ht k k')
          (intervalIntegrable_flowerKernelGen_dRoot L γ δ hF p hpr haP dagger cut1 cut2 hps hst₀ ht₀ k k')]
  · have h1 : ¬ (F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .plain) := fun h => hζ h.1
    have h2 : ¬ (F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF .dRoot) := fun h => hζ h.1
    simp only [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2), intervalIntegral.integral_zero, sub_self]

end Kind

end WaveTurbulence.Fixedpt
