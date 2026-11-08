/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Pin
public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueLeaves
public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueTreeInst

/-! # D2c PROT-CUT: splitting the free-time integral of `kernelProt`

* `protTime_split`: the free-time integral over a sum of index types is a product, once the integrand factors.
* `indicator_mul_of_iff`: indicators of product domains.
* For main's gluing data (`PL234.GlueData`, a paired tree glued on top of a garden at its lone position):
  `glueFreeEquiv`, `extendFix_glue_inl/inr`, **`protTime_glue`** (product of the two free-time integrals, given the
  product structure of the time domain at designation-consistent times), and **`protDom_glue_pinned`** (that
  product structure when the junction node, the root of the bottom tree `0`, is designated). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtCut

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.PL234 TTree

variable {w d : ℕ}

/-- **The free-time integral along a splitting of the free branches.** -/
theorem protTime_split (L γ δ : ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) {α β : Type*}
    [Fintype α] [Fintype β] (e : {b : GBranch LG.garden.tree // fix b = none} ≃ α ⊕ β)
    (I₁ : (α → ℝ) → ℂ) (I₂ : (β → ℝ) → ℂ)
    (hI : ∀ σ : α ⊕ β → ℝ, protIntegrand L γ δ LG up s fix K (fun b => σ (e b)) =
      I₁ (fun a => σ (Sum.inl a)) * I₂ (fun b => σ (Sum.inr b))) :
    protTime L γ δ LG up s fix K = (∫ x, I₁ x) * ∫ y, I₂ y := by
  have h1 := integral_arrow_equiv e.symm (protIntegrand L γ δ LG up s fix K)
  simp only [Equiv.symm_symm] at h1
  unfold protTime
  change ∫ τ, protIntegrand L γ δ LG up s fix K τ = _
  rw [← h1, ← integral_sum_mul I₁ I₂]
  exact integral_congr_ae (Filter.Eventually.of_forall hI)

/-- Indicators of a product domain. -/
theorem indicator_mul_of_iff {α β γ : Type*} (D : Set α) (D₁ : Set β) (D₂ : Set γ) (f : α → ℂ)
    (f₁ : β → ℂ) (f₂ : γ → ℂ) (x : α) (y : β) (z : γ) (hD : x ∈ D ↔ y ∈ D₁ ∧ z ∈ D₂)
    (hf : f x = f₁ y * f₂ z) : D.indicator f x = D₁.indicator f₁ y * D₂.indicator f₂ z := by
  by_cases h1 : y ∈ D₁ <;> by_cases h2 : z ∈ D₂
  · rw [Set.indicator_of_mem (hD.2 ⟨h1, h2⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2, hf]
  · rw [Set.indicator_of_notMem (fun h => h2 (hD.1 h).2), Set.indicator_of_notMem h2, mul_zero]
  · rw [Set.indicator_of_notMem (fun h => h1 (hD.1 h).1), Set.indicator_of_notMem h1, zero_mul]
  · rw [Set.indicator_of_notMem (fun h => h1 (hD.1 h).1), Set.indicator_of_notMem h1, zero_mul]

/-! ### Main's gluing data -/

variable [NeZero w]

namespace GlueFix

variable {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
variable (h : GlueData G G₁ G₂ X)

/-- The free branches of a glued garden. -/
def glueFreeEquiv (fix : GBranch G.tree → Option ℝ) :
    {b : GBranch G.tree // fix b = none} ≃
      {x : GBranch G₁.tree // fix (h.ofSum (.inl x)) = none} ⊕
        {y : GBranch G₂.tree // fix (h.ofSum (.inr y)) = none} :=
  (h.branchEquiv.subtypeEquiv (p := fun b => fix b = none)
    (q := fun z => fix (h.ofSum z) = none) (fun b => by
      show fix b = none ↔ fix (h.ofSum (h.toSum b)) = none
      rw [h.ofSum_toSum])).trans Equiv.subtypeSum

theorem glueFreeEquiv_symm_inl (fix : GBranch G.tree → Option ℝ)
    (x : {x : GBranch G₁.tree // fix (h.ofSum (.inl x)) = none}) :
    ((glueFreeEquiv h fix).symm (Sum.inl x)).1 = h.ofSum (.inl x.1) := rfl

theorem glueFreeEquiv_symm_inr (fix : GBranch G.tree → Option ℝ)
    (y : {y : GBranch G₂.tree // fix (h.ofSum (.inr y)) = none}) :
    ((glueFreeEquiv h fix).symm (Sum.inr y)).1 = h.ofSum (.inr y.1) := rfl

theorem extendFix_glue_inl (fix : GBranch G.tree → Option ℝ)
    (σ : {x : GBranch G₁.tree // fix (h.ofSum (.inl x)) = none} ⊕
        {y : GBranch G₂.tree // fix (h.ofSum (.inr y)) = none} → ℝ) (x : GBranch G₁.tree) :
    G.extendFix fix (fun b => σ (glueFreeEquiv h fix b)) (h.ofSum (.inl x)) =
      G₁.extendFix (fun x => fix (h.ofSum (.inl x))) (fun a => σ (Sum.inl a)) x := by
  cases hx : fix (h.ofSum (.inl x)) with
  | some v =>
    rw [extendFix_some G fix _ hx, extendFix_some G₁ (fun x => fix (h.ofSum (.inl x))) _ hx]
  | none =>
    rw [extendFix_free G fix _ ⟨_, hx⟩,
      extendFix_free G₁ (fun x => fix (h.ofSum (.inl x))) _ ⟨x, hx⟩]
    have : glueFreeEquiv h fix ⟨h.ofSum (.inl x), hx⟩ = Sum.inl ⟨x, hx⟩ := by
      rw [← (glueFreeEquiv h fix).apply_symm_apply (Sum.inl ⟨x, hx⟩)]
      rfl
    rw [this]

theorem extendFix_glue_inr (fix : GBranch G.tree → Option ℝ)
    (σ : {x : GBranch G₁.tree // fix (h.ofSum (.inl x)) = none} ⊕
        {y : GBranch G₂.tree // fix (h.ofSum (.inr y)) = none} → ℝ) (y : GBranch G₂.tree) :
    G.extendFix fix (fun b => σ (glueFreeEquiv h fix b)) (h.ofSum (.inr y)) =
      G₂.extendFix (fun y => fix (h.ofSum (.inr y))) (fun a => σ (Sum.inr a)) y := by
  cases hy : fix (h.ofSum (.inr y)) with
  | some v =>
    rw [extendFix_some G fix _ hy, extendFix_some G₂ (fun y => fix (h.ofSum (.inr y))) _ hy]
  | none =>
    rw [extendFix_free G fix _ ⟨_, hy⟩,
      extendFix_free G₂ (fun y => fix (h.ofSum (.inr y))) _ ⟨y, hy⟩]
    have : glueFreeEquiv h fix ⟨h.ofSum (.inr y), hy⟩ = Sum.inr ⟨y, hy⟩ := by
      rw [← (glueFreeEquiv h fix).apply_symm_apply (Sum.inr ⟨y, hy⟩)]
      rfl
    rw [this]

end GlueFix

/-- **The free-time integral of a glued garden is a product**, given the product structure of the time
domain at designation-consistent times. -/
theorem protTime_glue (L γ δ : ℝ) {LG : LayeredGarden w} {LG₁ : LayeredGarden 1}
    {LG₂ : LayeredGarden w} {X : RegChain} (h : GlueData LG.garden LG₁.garden LG₂.garden X)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (up₁ : GBranch LG₁.garden.tree → ℝ) (s₁ : ℝ) (up₂ : GBranch LG₂.garden.tree → ℝ) (s₂ : ℝ)
    (K : GNode LG.garden.tree → Mom d)
    (hD : ∀ τ : GBranch LG.garden.tree → ℝ, (∀ b v, fix b = some v → τ b = v) →
      (τ ∈ protDom LG up s fix ↔
        (fun x => τ (h.ofSum (.inl x))) ∈ protDom LG₁ up₁ s₁ (fun x => fix (h.ofSum (.inl x))) ∧
        (fun y => τ (h.ofSum (.inr y))) ∈ protDom LG₂ up₂ s₂ (fun y => fix (h.ofSum (.inr y))))) :
    protTime L γ δ LG up s fix K =
      protTime L γ δ LG₁ up₁ s₁ (fun x => fix (h.ofSum (.inl x))) (K ∘ h.ι₁) *
        protTime L γ δ LG₂ up₂ s₂ (fun y => fix (h.ofSum (.inr y))) (K ∘ h.ι₂) := by
  refine protTime_split L γ δ LG up s fix K (GlueFix.glueFreeEquiv h fix) _ _ fun σ => ?_
  unfold protIntegrand
  set τ := LG.garden.extendFix fix (fun b => σ (GlueFix.glueFreeEquiv h fix b))
  have e1 : (fun x => τ (h.ofSum (.inl x))) = LG₁.garden.extendFix (fun x => fix (h.ofSum (.inl x)))
      (fun a => σ (Sum.inl a)) := funext fun x => GlueFix.extendFix_glue_inl h fix σ x
  have e2 : (fun y => τ (h.ofSum (.inr y))) = LG₂.garden.extendFix (fun y => fix (h.ofSum (.inr y)))
      (fun a => σ (Sum.inr a)) := funext fun y => GlueFix.extendFix_glue_inr h fix σ y
  have hcons : ∀ b v, fix b = some v → τ b = v := fun b v hv => extendFix_some _ _ _ hv
  refine indicator_mul_of_iff _ _ _ _ _ _ τ _ _ ?_ ?_
  · rw [hD τ hcons, e1, e2]
  · rw [h.phaseProd_glue, e1, e2]

/-- The root of tree `0` of the bottom garden is the junction: a top branch has a bottom child only there. -/
theorem GlueFix.child_inr_inl {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
    (h : GlueData G G₁ G₂ X) (x : GBranch G₁.tree) (y : GBranch G₂.tree)
    (hc : (h.ofSum (.inr y)).IsChildOf (h.ofSum (.inl x))) : y.1 = ((0 : Fin w), []) := by
  have hx : ¬ X.lonePath <+: x.1.2 := by
    have hx0 : x.1.1 = 0 := Subsingleton.elim _ _
    have hm := x.2
    rw [hx0] at hm
    exact ((h.top_branch_iff _).mp hm).2
  obtain ⟨⟨j, q⟩, hy⟩ := y
  obtain ⟨h1, i, h2⟩ := hc
  have h1' : (botAddr X.lonePath (j, q)).1 = (0 : Fin w) := h1
  have h2' : (botAddr X.lonePath (j, q)).2 = x.1.2 ++ [i] := h2
  by_cases hj : j = 0
  · subst hj
    simp only [botAddr, ite_true] at h2'
    show ((0 : Fin w), q) = ((0 : Fin w), [])
    rcases List.eq_nil_or_concat q with hq | ⟨q', k, rfl⟩
    · rw [hq]
    · exfalso
      apply hx
      rw [List.concat_eq_append, ← List.append_assoc] at h2'
      have := List.append_inj' h2' rfl
      rw [← this.1]
      exact List.prefix_append _ _
  · simp only [botAddr, hj, ite_false] at h1'

/-- **The time domain of a glued garden with a designated junction.** The bottom root `r` (the node at the
lone position of the top paired tree) is designated at `u`; the top paired tree then carries the lone-port time
`u`. -/
theorem protDom_glue_pinned {LG : LayeredGarden w} {LG₁ : LayeredGarden 1} {LG₂ : LayeredGarden w}
    {X : RegChain} (h : GlueData LG.garden LG₁.garden LG₂.garden X)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (r : GBranch LG₂.garden.tree) (hr : r.1 = ((0 : Fin w), [])) (u : ℝ)
    (hfr : fix (h.ofSum (.inr r)) = some u)
    (hl₁ : ∀ x : GBranch LG₁.garden.tree, LG₁.layer x.toNode = LG.layer (h.ofSum (.inl x)).toNode)
    (hl₂ : ∀ y : GBranch LG₂.garden.tree, LG₂.layer y.toNode = LG.layer (h.ofSum (.inr y)).toNode)
    (hlone : ∀ b, LG.garden.IsLoneParent b ↔ ∃ y, b = h.ofSum (.inr y) ∧ LG₂.garden.IsLoneParent y)
    (hlone₁ : ∀ x : GBranch LG₁.garden.tree,
      LG₁.garden.IsLoneParent x ↔ (h.ofSum (.inr r)).IsChildOf (h.ofSum (.inl x)))
    (τ : GBranch LG.garden.tree → ℝ) (hτ : ∀ b v, fix b = some v → τ b = v) :
    τ ∈ protDom LG up s fix ↔
      (fun x => τ (h.ofSum (.inl x))) ∈ protDom LG₁ (fun x => up (h.ofSum (.inl x))) u
          (fun x => fix (h.ofSum (.inl x))) ∧
        (fun y => τ (h.ofSum (.inr y))) ∈ protDom LG₂ (fun y => up (h.ofSum (.inr y))) s
          (fun y => fix (h.ofSum (.inr y))) := by
  have hτr : τ (h.ofSum (.inr r)) = u := hτ _ _ hfr
  constructor
  · rintro ⟨hD, hL⟩
    refine ⟨⟨fun x => ⟨fun hx => ?_, fun x' hx' hor => ?_⟩, fun x hx hf => ?_⟩,
      ⟨fun y => ⟨fun hy => ?_, fun y' hy' hor => ?_⟩, fun y hy hf => ?_⟩⟩
    · have := (hD (h.ofSum (.inl x))).1 hx
      simp only [hl₁]; exact this
    · exact (hD (h.ofSum (.inl x))).2 _ ((h.child_inl_inl x x').mpr hx') hor
    · have hc := (hlone₁ x).mp hx
      have := (hD (h.ofSum (.inl x))).2 _ hc (Or.inr hf)
      rwa [hτr] at this
    · have := (hD (h.ofSum (.inr y))).1 hy
      simp only [hl₂]; exact this
    · exact (hD (h.ofSum (.inr y))).2 _ ((h.child_inr_inr y y').mpr hy') hor
    · exact hL _ ((hlone _).mpr ⟨y, rfl, hy⟩) hf
  · rintro ⟨⟨hD₁, hL₁⟩, ⟨hD₂, hL₂⟩⟩
    refine ⟨(h.forall_branch _).mpr ⟨fun x => ⟨fun hx => ?_, fun b' hb' hor => ?_⟩,
      fun y => ⟨fun hy => ?_, fun b' hb' hor => ?_⟩⟩, fun b hb hf => ?_⟩
    · have := (hD₁ x).1 hx
      simp only [hl₁] at this; exact this
    · rw [← h.ofSum_toSum b'] at hb' hor ⊢
      rcases hc : h.toSum b' with x' | y'
      · rw [hc] at hb' hor
        exact (hD₁ x).2 x' ((h.child_inl_inl x x').mp hb') hor
      · rw [hc] at hb' hor
        have hy' : y' = r := Subtype.ext ((GlueFix.child_inr_inl h x y' hb').trans hr.symm)
        subst hy'
        have hx1 : LG₁.garden.IsLoneParent x := (hlone₁ x).mpr hb'
        rcases hor with h1 | h1
        · rw [hfr] at h1; simp at h1
        · rw [hτr]; exact hL₁ x hx1 h1
    · have := (hD₂ y).1 hy
      simp only [hl₂] at this; exact this
    · rw [← h.ofSum_toSum b'] at hb' hor ⊢
      rcases hc : h.toSum b' with x' | y'
      · rw [hc] at hb'
        exact absurd hb' (h.not_child_inl_inr x' y)
      · rw [hc] at hb' hor
        exact (hD₂ y).2 y' ((h.child_inr_inr y y').mp hb') hor
    · obtain ⟨y, rfl, hy⟩ := (hlone b).mp hb
      exact hL₂ y hy hf

end WaveTurbulence.Flower.ProtCut
