/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarLayer
public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueLeaves
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs

/-! # FILT-COH (c5): gluing multiplied kernels across layers

For main's glue data `h : GlueData G G₁ G₂ X` (a paired tree `G₁` plugged on top of `G₂`):
* `kernelLeavesW_glue`: main's `PL234.kernelLeaves_glue` with decoration multipliers, under a functional
  factorization `m κ = m₁ (κ ∘ ι₁) * m₂ (κ ∘ ι₂)`;
* `nodeEquiv`, `prod_node`: the nodes of `G` are the nodes of `G₁` other than its lone leaf and the nodes of `G₂`;
* `starNode_ι₁`, `starNode_ι₂`, `starWeight_glue`, `prod_star_glue`: the star weight on `S` factors into the star
  weights on the pulled back sets (the lone leaf of `G₁` is the root of `G₂` and is counted below);
* `filtWeight_glue`: the filter layers factor through `ofSum`;
* `d5Mult`, `d5Mult_glue`: the D5 multiplier `starWeight · filtWeight · filtWeight` factors. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.PL234 WaveTurbulence.LGSpine TTree Finset
open WaveTurbulence.Links WaveTurbulence.Reg
open WaveTurbulence.PL234.GlueData (unbot botAddr_unbot unbot_botAddr botAddr_not_top)
open scoped ENNReal

variable {d : ℕ}

/-- The D5 multiplier (`ProtDefs.FiltCoherentBoundAt`). -/
@[expose] def d5Mult {w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) : ℂ :=
  IncTop.starWeight S ω κ * ProtDefs.filtWeight F ann M κ * ProtDefs.filtWeight Fu (fun _ => false) Mu κ

section Glue

variable {w : ℕ} [NeZero w] {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
  (h : GlueData G G₁ G₂ X)
include h

/-! ### Nodes -/

theorem not_prefix_of_ne_lone (x : GNode G₁.tree) (hx : x ≠ h.lone) : ¬ X.lonePath <+: x.1.2 := by
  intro hpre
  apply hx
  have hm := x.2
  have hx0 : x.1.1 = 0 := Subsingleton.elim _ _
  rw [hx0, h.tree1] at hm
  have he := plug_leaf_prefix X (G.sig 0) hm hpre
  apply Subtype.ext
  obtain ⟨⟨j, p⟩, _⟩ := x
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  subst he
  rfl

/-- The nodes of `G`, sorted into the two pieces. -/
@[expose] noncomputable def nodeToSum (a : GNode G.tree) : {x : GNode G₁.tree // x ≠ h.lone} ⊕ GNode G₂.tree := by
  classical
  exact if ha : a.1.1 = 0 ∧ ¬ X.lonePath <+: a.1.2 then
      .inl ⟨⟨((0 : Fin 1), a.1.2), by
        have hm := a.2
        rw [ha.1] at hm
        exact (h.top_node_iff a.1.2 ha.2).mpr hm⟩, fun he => ha.2 (by
          have := congrArg (fun x : GNode G₁.tree => x.1.2) he
          simp only [GlueData.lone] at this
          simp [this])⟩
    else .inr ⟨unbot X.lonePath a.1, by
      have hz : a.1.1 = 0 → X.lonePath <+: a.1.2 := fun h0 => by
        by_contra hn
        exact ha ⟨h0, hn⟩
      have hm := a.2
      rw [← botAddr_unbot hz] at hm
      exact (h.bot_iff _).1.mp hm⟩

/-- The nodes of the two pieces, placed in `G`. -/
@[expose] def nodeOfSum : {x : GNode G₁.tree // x ≠ h.lone} ⊕ GNode G₂.tree → GNode G.tree
  | .inl x => h.ι₁ x.1
  | .inr y => h.ι₂ y

theorem nodeOfSum_nodeToSum (a : GNode G.tree) : (nodeOfSum h) ((nodeToSum h) a) = a := by
  classical
  unfold nodeToSum
  by_cases ha : a.1.1 = 0 ∧ ¬ X.lonePath <+: a.1.2
  · rw [dite_eq_left ha]
    apply Subtype.ext
    obtain ⟨⟨j, p⟩, _⟩ := a
    simp only at ha
    show ((0 : Fin w), p) = (j, p)
    rw [ha.1]
  · rw [dite_eq_right ha]
    apply Subtype.ext
    exact botAddr_unbot fun h0 => by
      by_contra hne
      exact ha ⟨h0, hne⟩

theorem nodeToSum_nodeOfSum (z : {x : GNode G₁.tree // x ≠ h.lone} ⊕ GNode G₂.tree) :
    (nodeToSum h) ((nodeOfSum h) z) = z := by
  classical
  rcases z with x | y
  · have hx := (not_prefix_of_ne_lone h) x.1 x.2
    have hc : ((nodeOfSum h) (.inl x)).1.1 = 0 ∧ ¬ X.lonePath <+: ((nodeOfSum h) (.inl x)).1.2 := ⟨rfl, hx⟩
    unfold nodeToSum
    rw [dite_eq_left hc]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨⟨⟨j, p⟩, _⟩, _⟩ := x
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rfl
  · have hc : ¬ (((nodeOfSum h) (.inr y)).1.1 = 0 ∧ ¬ X.lonePath <+: ((nodeOfSum h) (.inr y)).1.2) :=
      botAddr_not_top _ _
    unfold nodeToSum
    rw [dite_eq_right hc]
    congr 1
    exact Subtype.ext (unbot_botAddr _ _)

/-- **The nodes of `G` are the non-lone nodes of `G₁` and the nodes of `G₂`.** -/
noncomputable def nodeEquiv : GNode G.tree ≃ {x : GNode G₁.tree // x ≠ h.lone} ⊕ GNode G₂.tree where
  toFun := (nodeToSum h)
  invFun := (nodeOfSum h)
  left_inv := (nodeOfSum_nodeToSum h)
  right_inv := (nodeToSum_nodeOfSum h)

theorem prod_node {M : Type*} [CommMonoid M] (f : GNode G.tree → M) :
    ∏ a, f a = (∏ x : {x : GNode G₁.tree // x ≠ h.lone}, f (h.ι₁ x.1)) * ∏ y, f (h.ι₂ y) := by
  rw [← (nodeEquiv h).symm.prod_comp, Fintype.prod_sum_type]
  rfl

/-! ### Stars -/

theorem starNode_ι₁ (x : GNode G₁.tree) (hx : x ≠ h.lone) (s : Fin 4) :
    IncTop.starNode (h.ι₁ x) s = h.ι₁ (IncTop.starNode x s) := by
  have hpre := (not_prefix_of_ne_lone h) x hx
  have hx0 : x.1.1 = 0 := Subsingleton.elim _ _
  have hiff : (h.ι₁ x).1.2 ∈ (G.tree (h.ι₁ x).1.1).branching ↔ x.1.2 ∈ (G₁.tree x.1.1).branching := by
    rw [hx0]
    exact ((h.top_branch_iff x.1.2).trans (and_iff_left hpre)).symm
  unfold IncTop.starNode
  by_cases hb : x.1.2 ∈ (G₁.tree x.1.1).branching
  · rw [dite_eq_left (hiff.mpr hb), dite_eq_left hb]
    refine Fin.cases rfl (fun j => ?_) s
    simp only [Fin.cases_succ]
    exact h.ofSum_inl_child ⟨x.1, hb⟩ j
  · rw [dite_eq_right (fun h' => hb (hiff.mp h')), dite_eq_right hb]

theorem starNode_ι₂ (y : GNode G₂.tree) (s : Fin 4) :
    IncTop.starNode (h.ι₂ y) s = h.ι₂ (IncTop.starNode y s) := by
  have hiff : (h.ι₂ y).1.2 ∈ (G.tree (h.ι₂ y).1.1).branching ↔ y.1.2 ∈ (G₂.tree y.1.1).branching :=
    (h.bot_iff y.1).2.2
  unfold IncTop.starNode
  by_cases hb : y.1.2 ∈ (G₂.tree y.1.1).branching
  · rw [dite_eq_left (hiff.mpr hb), dite_eq_left hb]
    refine Fin.cases rfl (fun j => ?_) s
    simp only [Fin.cases_succ]
    exact h.ofSum_inr_child ⟨y.1, hb⟩ j
  · rw [dite_eq_right (fun h' => hb (hiff.mp h')), dite_eq_right hb]

/-- The star set of the top piece (the lone leaf is counted below). -/
@[expose] noncomputable def starTop (S : Finset (GNode G.tree)) : Finset (GNode G₁.tree) := by
  classical
  exact univ.filter fun x => h.ι₁ x ∈ S ∧ x ≠ h.lone

/-- The star set of the bottom piece. -/
@[expose] noncomputable def starBot (S : Finset (GNode G.tree)) : Finset (GNode G₂.tree) := by
  classical
  exact univ.filter fun y => h.ι₂ y ∈ S

theorem prod_mem_glue {M : Type*} [CommMonoid M] (S : Finset (GNode G.tree)) (f : GNode G.tree → M) :
    ∏ a ∈ S, f a = (∏ x ∈ (starTop h) S, f (h.ι₁ x)) * ∏ y ∈ (starBot h) S, f (h.ι₂ y) := by
  classical
  have e1 : ∏ a ∈ S, f a = ∏ a, (if a ∈ S then f a else 1) := by
    rw [← Finset.prod_filter]
    congr 1
    ext a
    simp
  have e2 : ∏ x ∈ (starTop h) S, f (h.ι₁ x) =
      ∏ x : {x : GNode G₁.tree // x ≠ h.lone}, (if h.ι₁ x.1 ∈ S then f (h.ι₁ x.1) else 1) := by
    unfold starTop
    rw [Finset.prod_filter, ← Fintype.prod_subtype_mul_prod_subtype (fun x : GNode G₁.tree => x ≠ h.lone)]
    have h1 : ∏ x : {x : GNode G₁.tree // ¬ x ≠ h.lone},
        (if h.ι₁ x.1 ∈ S ∧ x.1 ≠ h.lone then f (h.ι₁ x.1) else 1) = 1 :=
      Finset.prod_eq_one fun x _ => ite_eq_right fun hc => hc.2 (not_not.mp x.2)
    rw [h1, mul_one]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp only [x.2, ne_eq, not_false_eq_true, and_true]
  have e3 : ∏ y ∈ (starBot h) S, f (h.ι₂ y) = ∏ y, (if h.ι₂ y ∈ S then f (h.ι₂ y) else 1) := by
    unfold starBot
    rw [Finset.prod_filter]
  rw [e1, (prod_node h), e2, e3]

/-- **The star weight factors.** -/
theorem starWeight_glue (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (κ : GNode G.tree → Mom d) :
    IncTop.starWeight S ω κ = IncTop.starWeight ((starTop h) S) (fun x => ω (h.ι₁ x)) (κ ∘ h.ι₁) *
      IncTop.starWeight ((starBot h) S) (fun y => ω (h.ι₂ y)) (κ ∘ h.ι₂) := by
  classical
  unfold IncTop.starWeight
  rw [(prod_mem_glue h) S]
  congr 1
  · refine Finset.prod_congr rfl fun x hx => ?_
    have hne : x ≠ h.lone := (Finset.mem_filter.mp hx).2.2
    unfold IncTop.starMomenta
    congr 2
    funext s
    rw [(starNode_ι₁ h) x hne s]
    rfl
  · refine Finset.prod_congr rfl fun y _ => ?_
    unfold IncTop.starMomenta
    congr 2
    funext s
    rw [(starNode_ι₂ h) y s]
    rfl

/-! ### Filters -/

/-- The filter set of the top piece. -/
@[expose] noncomputable def filtTop (F : Finset (GBranch G.tree)) : Finset (GBranch G₁.tree) := by
  classical
  exact univ.filter fun x => h.ofSum (.inl x) ∈ F

/-- The filter set of the bottom piece. -/
@[expose] noncomputable def filtBot (F : Finset (GBranch G.tree)) : Finset (GBranch G₂.tree) := by
  classical
  exact univ.filter fun y => h.ofSum (.inr y) ∈ F

/-- **The filter layer factors.** -/
theorem filtWeight_glue (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (κ : GNode G.tree → Mom d) :
    ProtDefs.filtWeight F ann M κ =
      ProtDefs.filtWeight ((filtTop h) F) (fun x => ann (h.ofSum (.inl x))) (fun x => M (h.ofSum (.inl x)))
          (κ ∘ h.ι₁) *
        ProtDefs.filtWeight ((filtBot h) F) (fun y => ann (h.ofSum (.inr y))) (fun y => M (h.ofSum (.inr y)))
          (κ ∘ h.ι₂) := by
  classical
  unfold ProtDefs.filtWeight filtTop filtBot
  rw [Finset.prod_filter, Finset.prod_filter]
  have e1 : ∀ g : GBranch G.tree → ℂ, ∏ b ∈ F, g b = ∏ b, (if b ∈ F then g b else 1) := fun g => by
    rw [← Finset.prod_filter]
    congr 1
    ext b
    simp
  rw [e1, h.prod_branch]
  simp only [h.omegaNode_inl, h.omegaNode_inr]

/-- **The D5 multiplier factors.** -/
theorem d5Mult_glue (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) :
    d5Mult S ω F ann M Fu Mu κ =
      d5Mult ((starTop h) S) (fun x => ω (h.ι₁ x)) ((filtTop h) F) (fun x => ann (h.ofSum (.inl x)))
          (fun x => M (h.ofSum (.inl x))) ((filtTop h) Fu) (fun x => Mu (h.ofSum (.inl x))) (κ ∘ h.ι₁) *
        d5Mult ((starBot h) S) (fun y => ω (h.ι₂ y)) ((filtBot h) F) (fun y => ann (h.ofSum (.inr y)))
          (fun y => M (h.ofSum (.inr y))) ((filtBot h) Fu) (fun y => Mu (h.ofSum (.inr y))) (κ ∘ h.ι₂) := by
  unfold d5Mult
  rw [(starWeight_glue h), (filtWeight_glue h) F ann M, (filtWeight_glue h) Fu (fun _ => false) Mu]
  ring

end Glue

section KernelGlue

/-- The multiplied kernel as a decoration series of main's leaf summands. -/
theorem kernelLeavesW_eq_tsum' (L γ δ : ℝ) {v : ℕ} (LG : LayeredGarden v) (H : LeafProfiles v d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k (fun _ => 0) 0 m =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0,
          m (cosetDecoration LG.garden L k κ.1) * leavesSummand L γ δ LG H up s k κ := rfl

variable {w : ℕ} [NeZero w]

/-- **The multiplied leafwise kernel of a glued garden is the product of the multiplied kernels of the two
pieces** (main's `PL234.kernelLeaves_glue`, sha256 in COPIED-SHA256SUMS), for a multiplier that factors through
the two node maps. -/
theorem kernelLeavesW_glue (L γ δ : ℝ) {LG : LayeredGarden w}
    {LG₁ : LayeredGarden 1} {LG₂ : LayeredGarden w} {X : RegChain}
    (h : GlueData LG.garden LG₁.garden LG₂.garden X) (hs : h.DecSplit (Fin d → ℤ))
    (hg : GlueData.DecGlue (G := LG.garden) (G₁ := LG₁.garden) (G₂ := LG₂.garden) (X := X)
      (Fin d → ℤ))
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, ¬ LG.garden.IsFlower ℓ)
    (hfl₁ : ∀ ℓ : GLeaf LG₁.garden.tree, ¬ LG₁.garden.IsFlower ℓ)
    (hfl₂ : ∀ ℓ : GLeaf LG₂.garden.tree, ¬ LG₂.garden.IsFlower ℓ)
    (hm₁ : ∀ ℓ : GLeaf LG₁.garden.tree,
      LG₁.garden.mark ℓ = if ℓ.1.2 = X.lonePath then some .lower else none)
    (hmtop : ∀ ℓ : GLeaf LG.garden.tree, (ℓ.1.1 = 0 ∧ ¬ X.lonePath <+: ℓ.1.2) →
      LG.garden.mark ℓ = none)
    (hmbot : ∀ (ℓ₂ : GLeaf LG₂.garden.tree) (ℓ : GLeaf LG.garden.tree),
      ℓ.1 = botAddr X.lonePath ℓ₂.1 → LG.garden.mark ℓ = LG₂.garden.mark ℓ₂)
    (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (up₁ : GBranch LG₁.garden.tree → ℝ) (s₁ : ℝ)
    (up₂ : GBranch LG₂.garden.tree → ℝ) (s₂ : ℝ)
    (hD : ∀ τ, τ ∈ kDomain LG up s ↔ (fun x => τ (h.ofSum (.inl x))) ∈ kDomain LG₁ up₁ s₁ ∧
      (fun y => τ (h.ofSum (.inr y))) ∈ kDomain LG₂ up₂ s₂)
    (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ) (m₁ : (GNode LG₁.garden.tree → Mom d) → ℂ)
    (m₂ : (GNode LG₂.garden.tree → Mom d) → ℂ) (hm : ∀ κ, m κ = m₁ (κ ∘ h.ι₁) * m₂ (κ ∘ h.ι₂))
    (hsum₁ : Summable fun κ : GenDecoration LG₁.garden d (fun _ => 0) 0 =>
      ‖m₁ (cosetDecoration LG₁.garden L k κ.1) * leavesSummand L γ δ LG₁ (fun z => H (topAddr z)) up₁ s₁ k κ‖)
    (hsum₂ : Summable fun κ : GenDecoration LG₂.garden d (fun _ => 0) 0 =>
      ‖m₂ (cosetDecoration LG₂.garden L k κ.1) *
        leavesSummand L γ δ LG₂ (fun z => H (botAddr X.lonePath z)) up₂ s₂ k κ‖) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k (fun _ => 0) 0 m =
      Flower.Stage1W.kernelLeavesW L γ δ LG₁ (fun z => H (topAddr z)) up₁ s₁ k (fun _ => 0) 0 m₁ *
        Flower.Stage1W.kernelLeavesW L γ δ LG₂ (fun z => H (botAddr X.lonePath z)) up₂ s₂ k (fun _ => 0) 0 m₂ := by
  let e := h.decEquiv hs hg hfl hfl₁ hfl₂
  have hsplit : ∀ p : GenDecoration LG₁.garden d (fun _ => 0) 0 × GenDecoration LG₂.garden d (fun _ => 0) 0,
      m (cosetDecoration LG.garden L k (e.symm p).1) * leavesSummand L γ δ LG H up s k (e.symm p) =
        (m₁ (cosetDecoration LG₁.garden L k p.1.1) * leavesSummand L γ δ LG₁ (fun z => H (topAddr z)) up₁ s₁ k p.1) *
          (m₂ (cosetDecoration LG₂.garden L k p.2.1) *
            leavesSummand L γ δ LG₂ (fun z => H (botAddr X.lonePath z)) up₂ s₂ k p.2) := by
    intro p
    have hp := e.apply_symm_apply p
    have h1 : (e.symm p).1 ∘ h.ι₁ = p.1.1 := congrArg (fun q => q.1.1) hp
    have h2 : (e.symm p).1 ∘ h.ι₂ = p.2.1 := congrArg (fun q => q.2.1) hp
    have c1 : cosetDecoration LG.garden L k (e.symm p).1 ∘ h.ι₁ =
        cosetDecoration LG₁.garden L k ((e.symm p).1 ∘ h.ι₁) := rfl
    have c2 : cosetDecoration LG.garden L k (e.symm p).1 ∘ h.ι₂ =
        cosetDecoration LG₂.garden L k ((e.symm p).1 ∘ h.ι₂) := rfl
    have hmm : m (cosetDecoration LG.garden L k (e.symm p).1) =
        m₁ (cosetDecoration LG₁.garden L k p.1.1) * m₂ (cosetDecoration LG₂.garden L k p.2.1) := by
      rw [hm, c1, c2, h1, h2]
    have hls : leavesSummand L γ δ LG H up s k (e.symm p) =
        leavesSummand L γ δ LG₁ (fun z => H (topAddr z)) up₁ s₁ k p.1 *
          leavesSummand L γ δ LG₂ (fun z => H (botAddr X.lonePath z)) up₂ s₂ k p.2 := by
      unfold leavesSummand
      rw [h.epsDec_glue, h.phaseIntegral_glue L γ δ (noFlowerParent_of_noFlower hfl)
        (noFlowerParent_of_noFlower hfl₁) (noFlowerParent_of_noFlower hfl₂) _ _ _ hD s s₁ s₂]
      have hin := h.prod_inputLeaves_glue hm₁ hmtop hmbot
        (fun z => (H z (k + latticePoint L (extend (e.symm p).1 z)) : ℂ))
      have l0 : ∀ ℓ : GLeaf LG.garden.tree,
          extend (e.symm p).1 ℓ.1 = (e.symm p).1 ℓ.toNode := fun ℓ => extend_node _ ℓ.toNode
      have l1 : ∀ ℓ : GLeaf LG₁.garden.tree,
          extend (e.symm p).1 (topAddr ℓ.1) = ((e.symm p).1 ∘ h.ι₁) ℓ.toNode :=
        fun ℓ => extend_node _ (h.ι₁ ℓ.toNode)
      have l2 : ∀ ℓ : GLeaf LG₂.garden.tree,
          extend (e.symm p).1 (botAddr X.lonePath ℓ.1) = ((e.symm p).1 ∘ h.ι₂) ℓ.toNode :=
        fun ℓ => extend_node _ (h.ι₂ ℓ.toNode)
      simp only [l0, l1, l2] at hin
      simp only [cosetDecoration] at hin ⊢
      rw [hin]
      rw [c1, c2, h1, h2]
      push_cast
      ring
    rw [hmm, hls]
    ring
  rw [kernelLeavesW_eq_tsum', kernelLeavesW_eq_tsum', kernelLeavesW_eq_tsum']
  rw [h.order_glue, pow_add, h.zeta_glue, ← e.symm.tsum_eq, tsum_congr hsplit,
    ← tsum_mul_tsum_of_summable_norm hsum₁ hsum₂]
  ring

end KernelGlue

end WaveTurbulence.Flower.FiltCoh
