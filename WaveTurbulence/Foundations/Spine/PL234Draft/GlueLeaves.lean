/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueTreeInst
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel

/-!
# Leafwise kernels of glued gardens (TARGET L1241–L1246 with L2065–L2067)

The spine's leafwise kernel `kernelLeaves` (individual profiles `H` at the positive input leaves,
indexed by leaf address) of a glued garden is the product of the leafwise kernels of the pieces, with
the profiles transported along the address maps (`kernelLeaves_glue`):

* `prod_inputLeaves_glue`: the input leaves of `G` are those of the top paired tree other than its lone
  leaf, and those of the bottom garden, at the transported addresses;
* `kernelLeaves_glue`: the product formula, given the time-domain product and summability.

The layer-indexed kernel is the case `H ℓ = F (𝔏_ℓ)` (spine `kernelLeaves_eq_kernelK`).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

/-- The address embedding of the leaves of a forest. -/
def leafEmb {v : ℕ} (tree : Fin v → TTree) : GLeaf tree ↪ Fin v × Path :=
  ⟨fun ℓ => ℓ.1, fun _ _ h => Subtype.ext h⟩

@[simp] theorem leafEmb_apply {v : ℕ} (tree : Fin v → TTree) (ℓ : GLeaf tree) :
    leafEmb tree ℓ = ℓ.1 := rfl

variable {w : ℕ} [NeZero w]

namespace GlueData

variable {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
variable (h : GlueData G G₁ G₂ X)
include h

theorem leaf_ofTop (ℓ : GLeaf G₁.tree) (hℓ : ℓ.1.2 ≠ X.lonePath) :
    (topAddr (w := w) ℓ.1).2 ∈ (G.tree (topAddr (w := w) ℓ.1).1).leaves := by
  have hx : ℓ.1.1 = 0 := Subsingleton.elim _ _
  have hm := ℓ.2
  rw [hx] at hm
  exact ((h.top_leaf_iff _).mp ⟨hm, hℓ⟩).1

theorem leaf_ofBot (ℓ : GLeaf G₂.tree) :
    (botAddr X.lonePath ℓ.1).2 ∈ (G.tree (botAddr X.lonePath ℓ.1).1).leaves :=
  (h.bot_iff ℓ.1).2.1.mpr ℓ.2

theorem leaf_top {ℓ : GLeaf G.tree} (ht : ℓ.1.1 = 0 ∧ ¬ X.lonePath <+: ℓ.1.2) :
    ℓ.1.2 ∈ (G₁.tree ((0 : Fin 1), ℓ.1.2).1).leaves := by
  have hm := ℓ.2
  rw [ht.1] at hm
  exact ((h.top_leaf_iff _).mpr ⟨hm, ht.2⟩).1

theorem leaf_bot {ℓ : GLeaf G.tree} (ht : ¬ (ℓ.1.1 = 0 ∧ ¬ X.lonePath <+: ℓ.1.2)) :
    (unbot X.lonePath ℓ.1).2 ∈ (G₂.tree (unbot X.lonePath ℓ.1).1).leaves := by
  have he : botAddr X.lonePath (unbot X.lonePath ℓ.1) = ℓ.1 :=
    botAddr_unbot fun h0 => by
      by_contra hne
      exact ht ⟨h0, hne⟩
  have := (h.bot_iff (unbot X.lonePath ℓ.1)).2.1
  rw [he] at this
  exact this.mp ℓ.2

omit h in
theorem prod_inputLeaves_addr {v : ℕ} {G' : Garden v} {M : Type*} [CommMonoid M]
    (g : Fin v × Path → M) :
    ∏ ℓ ∈ inputLeaves G', g ℓ.1 = ∏ z ∈ (inputLeaves G').map (leafEmb G'.tree), g z := by
  rw [prod_map]
  rfl

/-- **The input leaves of a glued garden.** -/
theorem prod_inputLeaves_glue
    (hm₁ : ∀ ℓ : GLeaf G₁.tree, G₁.mark ℓ = if ℓ.1.2 = X.lonePath then some .lower else none)
    (hmtop : ∀ ℓ : GLeaf G.tree, (ℓ.1.1 = 0 ∧ ¬ X.lonePath <+: ℓ.1.2) → G.mark ℓ = none)
    (hmbot : ∀ (ℓ₂ : GLeaf G₂.tree) (ℓ : GLeaf G.tree), ℓ.1 = botAddr X.lonePath ℓ₂.1 →
      G.mark ℓ = G₂.mark ℓ₂)
    {M : Type*} [CommMonoid M] (f : Fin w × Path → M) :
    ∏ ℓ ∈ inputLeaves G, f ℓ.1 =
      (∏ ℓ ∈ inputLeaves G₁, f (topAddr ℓ.1)) * ∏ ℓ ∈ inputLeaves G₂, f (botAddr X.lonePath ℓ.1) := by
  classical
  set A := (inputLeaves G).map (leafEmb G.tree)
  set A₁ := (inputLeaves G₁).map (leafEmb G₁.tree)
  set A₂ := (inputLeaves G₂).map (leafEmb G₂.tree)
  have e0 : ∏ ℓ ∈ inputLeaves G, f ℓ.1 = ∏ z ∈ A, f z := prod_inputLeaves_addr _
  have e1 : ∏ ℓ ∈ inputLeaves G₁, f (topAddr ℓ.1) = ∏ z ∈ A₁, f (topAddr z) :=
    prod_inputLeaves_addr (fun z => f (topAddr z))
  have e2 : ∏ ℓ ∈ inputLeaves G₂, f (botAddr X.lonePath ℓ.1) = ∏ z ∈ A₂, f (botAddr X.lonePath z) :=
    prod_inputLeaves_addr (fun z => f (botAddr X.lonePath z))
  rw [e0, e1, e2]
  have inj₁ : ∀ x ∈ A₁, ∀ y ∈ A₁, topAddr (w := w) x = topAddr y → x = y := by
    intro x _ y _ hxy
    obtain ⟨i, p⟩ := x
    obtain ⟨j, q⟩ := y
    have hi : i = j := Subsingleton.elim _ _
    simp only [topAddr, Prod.mk.injEq] at hxy
    rw [hi, hxy.2]
  have inj₂ : ∀ x ∈ A₂, ∀ y ∈ A₂, botAddr X.lonePath x = botAddr X.lonePath y → x = y := by
    intro x _ y _ hxy
    rw [← unbot_botAddr X.lonePath x, hxy, unbot_botAddr]
  have hdisj : Disjoint (A₁.image topAddr) (A₂.image (botAddr X.lonePath)) := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz₁
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hz₂
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_map.mp hx
    have hne : ℓ.1.2 ≠ X.lonePath := by
      intro he
      simp only [inputLeaves, mem_filter, mem_univ, true_and] at hℓ
      rw [hm₁ ℓ, ite_eq_left he] at hℓ
      exact absurd hℓ.2 (by simp)
    have hnp : ¬ X.lonePath <+: ℓ.1.2 := by
      intro hpre
      have hx0 : ℓ.1.1 = 0 := Subsingleton.elim _ _
      have hmem := ℓ.2
      rw [hx0, h.tree1] at hmem
      exact hne (plug_leaf_prefix X _ (TTree.leaves_subset_nodes _ hmem) hpre)
    apply botAddr_not_top X.lonePath y
    rw [hy]
    exact ⟨rfl, hnp⟩
  have hA : A = A₁.image topAddr ∪ A₂.image (botAddr X.lonePath) := by
    ext z
    simp only [A, A₁, A₂, Finset.mem_union, Finset.mem_image, Finset.mem_map,
      leafEmb_apply, inputLeaves, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨ℓ, ⟨hs, hm⟩, rfl⟩
      by_cases ht : ℓ.1.1 = 0 ∧ ¬ X.lonePath <+: ℓ.1.2
      · left
        refine ⟨((0 : Fin 1), ℓ.1.2), ⟨⟨_, h.leaf_top ht⟩, ⟨?_, ?_⟩, rfl⟩, ?_⟩
        · have e : h.ι₁ (GLeaf.toNode ⟨((0 : Fin 1), ℓ.1.2), h.leaf_top ht⟩) = ℓ.toNode := by
            apply Subtype.ext
            show ((0 : Fin w), ℓ.1.2) = ℓ.1
            rw [← ht.1]
          rw [← h.sign_ι₁, e]
          exact hs
        · have : ¬ ℓ.1.2 = X.lonePath := fun he => ht.2 (he ▸ List.prefix_refl _)
          exact (hm₁ _).trans (by simp [this])
        · show ((0 : Fin w), ℓ.1.2) = ℓ.1
          rw [← ht.1]
      · right
        have hb : botAddr X.lonePath (unbot X.lonePath ℓ.1) = ℓ.1 :=
          botAddr_unbot fun h0 => by
            by_contra hne
            exact ht ⟨h0, hne⟩
        refine ⟨unbot X.lonePath ℓ.1, ⟨⟨_, h.leaf_bot ht⟩, ⟨?_, ?_⟩, rfl⟩, hb⟩
        · have e : h.ι₂ (GLeaf.toNode ⟨unbot X.lonePath ℓ.1, h.leaf_bot ht⟩) = ℓ.toNode :=
            Subtype.ext hb
          rw [← h.sign_ι₂, e]
          exact hs
        · exact (hmbot _ ℓ hb.symm).symm.trans hm
    · rintro (⟨x, ⟨ℓ₁, ⟨hs, hm⟩, rfl⟩, rfl⟩ | ⟨y, ⟨ℓ₂, ⟨hs, hm⟩, rfl⟩, rfl⟩)
      · have hne : ℓ₁.1.2 ≠ X.lonePath := by
          intro he
          rw [hm₁ ℓ₁, ite_eq_left he] at hm
          exact absurd hm (by simp)
        refine ⟨⟨topAddr ℓ₁.1, h.leaf_ofTop ℓ₁ hne⟩, ⟨?_, ?_⟩, rfl⟩
        · rw [← h.sign_ι₁] at hs
          exact hs
        · have hnp : ¬ X.lonePath <+: ℓ₁.1.2 := by
            intro hpre
            have hx0 : ℓ₁.1.1 = 0 := Subsingleton.elim _ _
            have hmem := ℓ₁.2
            rw [hx0, h.tree1] at hmem
            exact hne (plug_leaf_prefix X _ (TTree.leaves_subset_nodes _ hmem) hpre)
          exact hmtop _ ⟨rfl, hnp⟩
      · refine ⟨⟨botAddr X.lonePath ℓ₂.1, h.leaf_ofBot ℓ₂⟩, ⟨?_, ?_⟩, rfl⟩
        · rw [← h.sign_ι₂] at hs
          exact hs
        · exact (hmbot ℓ₂ ⟨botAddr X.lonePath ℓ₂.1, h.leaf_ofBot ℓ₂⟩ rfl).trans hm
  rw [hA, prod_union hdisj, prod_image inj₁, prod_image inj₂]

theorem inputLeaf_ofTop
    (hm₁ : ∀ ℓ : GLeaf G₁.tree, G₁.mark ℓ = if ℓ.1.2 = X.lonePath then some .lower else none)
    (hmtop : ∀ ℓ : GLeaf G.tree, (ℓ.1.1 = 0 ∧ ¬ X.lonePath <+: ℓ.1.2) → G.mark ℓ = none)
    (ℓ₁ : GLeaf G₁.tree) (hℓ : ℓ₁ ∈ inputLeaves G₁) :
    ∃ ℓ ∈ inputLeaves G, ℓ.1 = topAddr ℓ₁.1 := by
  simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
  have hne : ℓ₁.1.2 ≠ X.lonePath := by
    intro he
    have hm := hℓ.2
    rw [hm₁ ℓ₁, ite_eq_left he] at hm
    exact absurd hm (by simp)
  refine ⟨⟨topAddr ℓ₁.1, h.leaf_ofTop ℓ₁ hne⟩, ⟨?_, ?_⟩, rfl⟩
  · have hs := hℓ.1
    rw [← h.sign_ι₁] at hs
    exact hs
  · have hnp : ¬ X.lonePath <+: ℓ₁.1.2 := by
      intro hpre
      have hx0 : ℓ₁.1.1 = 0 := Subsingleton.elim _ _
      have hmem := ℓ₁.2
      rw [hx0, h.tree1] at hmem
      exact hne (plug_leaf_prefix X _ (TTree.leaves_subset_nodes _ hmem) hpre)
    exact hmtop _ ⟨rfl, hnp⟩

theorem inputLeaf_ofBot
    (hmbot : ∀ (ℓ₂ : GLeaf G₂.tree) (ℓ : GLeaf G.tree), ℓ.1 = botAddr X.lonePath ℓ₂.1 →
      G.mark ℓ = G₂.mark ℓ₂)
    (ℓ₂ : GLeaf G₂.tree) (hℓ : ℓ₂ ∈ inputLeaves G₂) :
    ∃ ℓ ∈ inputLeaves G, ℓ.1 = botAddr X.lonePath ℓ₂.1 := by
  simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
  refine ⟨⟨botAddr X.lonePath ℓ₂.1, h.leaf_ofBot ℓ₂⟩, ⟨?_, ?_⟩, rfl⟩
  · have hs := hℓ.1
    rw [← h.sign_ι₂] at hs
    exact hs
  · exact (hmbot ℓ₂ ⟨botAddr X.lonePath ℓ₂.1, h.leaf_ofBot ℓ₂⟩ rfl).trans hℓ.2

end GlueData

/-- The summand of the leafwise kernel. -/
noncomputable def leavesSummand (L γ δ : ℝ) {v d : ℕ} (LG : LayeredGarden v) (H : LeafProfiles v d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) {nroot : Fin v → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

theorem kernelLeaves_eq_tsum (L γ δ : ℝ) {v d : ℕ} (LG : LayeredGarden v) (H : LeafProfiles v d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin v → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG H up s k₀ nroot nfl = (coupling d L γ δ : ℂ) ^ LG.garden.order *
      LG.garden.zeta * ∑' κ : GenDecoration LG.garden d nroot nfl, leavesSummand L γ δ LG H up s k₀ κ :=
  rfl

/-- **The leafwise kernel of a glued garden is the product of the leafwise kernels of the two
pieces** (TARGET (prooflayer1-1)–(prooflayer1-2) with individual leaf profiles), the profiles being
transported along the address maps. -/
theorem kernelLeaves_glue (L γ δ : ℝ) {d : ℕ} {LG : LayeredGarden w}
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
    (k : Mom d)
    (hsum₁ : Summable fun κ : GenDecoration LG₁.garden d (fun _ => 0) 0 =>
      ‖leavesSummand L γ δ LG₁ (fun z => H (topAddr z)) up₁ s₁ k κ‖)
    (hsum₂ : Summable fun κ : GenDecoration LG₂.garden d (fun _ => 0) 0 =>
      ‖leavesSummand L γ δ LG₂ (fun z => H (botAddr X.lonePath z)) up₂ s₂ k κ‖) :
    kernelLeaves L γ δ LG H up s k (fun _ => 0) 0 =
      kernelLeaves L γ δ LG₁ (fun z => H (topAddr z)) up₁ s₁ k (fun _ => 0) 0 *
        kernelLeaves L γ δ LG₂ (fun z => H (botAddr X.lonePath z)) up₂ s₂ k (fun _ => 0) 0 := by
  let e := h.decEquiv hs hg hfl hfl₁ hfl₂
  have hsplit : ∀ p : GenDecoration LG₁.garden d (fun _ => 0) 0 × GenDecoration LG₂.garden d (fun _ => 0) 0,
      leavesSummand L γ δ LG H up s k (e.symm p) =
        leavesSummand L γ δ LG₁ (fun z => H (topAddr z)) up₁ s₁ k p.1 *
          leavesSummand L γ δ LG₂ (fun z => H (botAddr X.lonePath z)) up₂ s₂ k p.2 := by
    intro p
    have hp := e.apply_symm_apply p
    have h1 : (e.symm p).1 ∘ h.ι₁ = p.1.1 := congrArg (fun q => q.1.1) hp
    have h2 : (e.symm p).1 ∘ h.ι₂ = p.2.1 := congrArg (fun q => q.2.1) hp
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
    have c1 : cosetDecoration LG.garden L k (e.symm p).1 ∘ h.ι₁ =
        cosetDecoration LG₁.garden L k ((e.symm p).1 ∘ h.ι₁) := rfl
    have c2 : cosetDecoration LG.garden L k (e.symm p).1 ∘ h.ι₂ =
        cosetDecoration LG₂.garden L k ((e.symm p).1 ∘ h.ι₂) := rfl
    simp only [cosetDecoration] at hin ⊢
    rw [hin]
    rw [c1, c2, h1, h2]
    push_cast
    ring
  rw [kernelLeaves_eq_tsum, kernelLeaves_eq_tsum, kernelLeaves_eq_tsum, h.order_glue, pow_add,
    h.zeta_glue, ← e.symm.tsum_eq, tsum_congr hsplit, ← tsum_mul_tsum_of_summable_norm hsum₁ hsum₂]
  ring

end WaveTurbulence.PL234
