/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueIdentity
/-! FLOWER-P7: injectivity of the glue, and every garden with a pairing-closed block is a glue. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

theorem gT_injective (σ : Fin a ⊕ Fin b ≃ Fin w) {TA TA' : Fin a → TTree} {TB TB' : Fin b → TTree}
    (h : gT σ TA TB = gT σ TA' TB') : TA = TA' ∧ TB = TB' := by
  constructor
  · funext i; simpa using congrFun h (σ (.inl i))
  · funext i; simpa using congrFun h (σ (.inr i))

theorem gSig_injective (σ : Fin a ⊕ Fin b ≃ Fin w) {sA sA' : Fin a → ℤˣ} {sB sB' : Fin b → ℤˣ}
    (h : gSig σ sA sB = gSig σ sA' sB') : sA = sA' ∧ sB = sB' := by
  constructor
  · funext i; simpa [gSig] using congrFun h (σ (.inl i))
  · funext i; simpa [gSig] using congrFun h (σ (.inr i))

theorem glueGarden_injective (σ : Fin a ⊕ Fin b ≃ Fin w) {GA GA' : Garden a} {GB GB' : Garden b}
    (h : glueGarden σ GA GB = glueGarden σ GA' GB') : GA = GA' ∧ GB = GB' := by
  obtain ⟨sA, tA, pA, mA, a1, a2, a3⟩ := GA
  obtain ⟨sA', tA', pA', mA', b1, b2, b3⟩ := GA'
  obtain ⟨sB, tB, pB, mB, c1, c2, c3⟩ := GB
  obtain ⟨sB', tB', pB', mB', d1, d2, d3⟩ := GB'
  have hs := gSig_injective σ (congrArg Garden.sig h)
  have ht := gT_injective σ (congrArg Garden.tree h)
  simp only at hs ht
  obtain ⟨rfl, rfl⟩ := hs
  obtain ⟨rfl, rfl⟩ := ht
  simp only [glueGarden, Garden.mk.injEq, heq_eq_eq, true_and] at h
  obtain ⟨hp, hm⟩ := h
  have e1 : pA = pA' := by
    funext x
    have := congrFun hp (glueLeaf σ tA tB (.inl x))
    simpa using this
  have e2 : mA = mA' := by
    funext x
    have := congrFun hm (glueLeaf σ tA tB (.inl x))
    simpa using this
  have e3 : pB = pB' := by
    funext x
    have := congrFun hp (glueLeaf σ tA tB (.inr x))
    simpa using this
  have e4 : mB = mB' := by
    funext x
    have := congrFun hm (glueLeaf σ tA tB (.inr x))
    simpa using this
  subst e1 e2 e3 e4
  exact ⟨rfl, rfl⟩

theorem glueLayered_injective (σ : Fin a ⊕ Fin b ≃ Fin w) {LA LA' : LayeredGarden a} {LB LB' : LayeredGarden b}
    (h : glueLayered σ LA LB = glueLayered σ LA' LB') : LA = LA' ∧ LB = LB' := by
  have hg := glueGarden_injective σ (congrArg LayeredGarden.garden h)
  obtain ⟨GA, lA, iA⟩ := LA
  obtain ⟨GA', lA', iA'⟩ := LA'
  obtain ⟨GB, lB, iB⟩ := LB
  obtain ⟨GB', lB', iB'⟩ := LB'
  simp only at hg
  obtain ⟨rfl, rfl⟩ := hg
  simp only [glueLayered, LayeredGarden.mk.injEq, heq_eq_eq, true_and] at h
  have e1 : lA = lA' := by
    funext x
    have := congrFun h (glueNode σ GA.tree GB.tree (.inl x))
    simpa using this
  have e2 : lB = lB' := by
    funext x
    have := congrFun h (glueNode σ GA.tree GB.tree (.inr x))
    simpa using this
  subst e1 e2
  exact ⟨rfl, rfl⟩

/-- A tree array is the glue of its two restrictions. -/
theorem gT_restrict (σ : Fin a ⊕ Fin b ≃ Fin w) (T : Fin w → TTree) :
    gT σ (fun i => T (σ (.inl i))) (fun i => T (σ (.inr i))) = T := by
  funext c
  obtain ⟨s, rfl⟩ := σ.surjective c
  rcases s with i | i <;> simp

/-- **Existence of the split.**  A garden in which the trees `σ (inl i)` are closed under the pairing is the
glue of its two restrictions. -/
theorem exists_glue_garden (σ : Fin a ⊕ Fin b ≃ Fin w) (G : Garden w)
    (hcl : ∀ ℓ : GLeaf G.tree, (∃ i, ℓ.1.1 = σ (.inl i)) → ∃ i, (G.pair ℓ).1.1 = σ (.inl i)) :
    ∃ GA GB, glueGarden σ GA GB = G := by
  classical
  obtain ⟨sg, tr, pr, mk, h1, h2, h3⟩ := G
  simp only at hcl
  have htr := gT_restrict σ tr
  generalize hTA : (fun i => tr (σ (.inl i))) = TA at htr
  generalize hTB : (fun i => tr (σ (.inr i))) = TB at htr
  subst htr
  -- the pairing preserves each block
  have hA : ∀ x : GLeaf TA, ∃ y : GLeaf TA, pr (glueLeaf σ TA TB (.inl x)) = glueLeaf σ TA TB (.inl y) := by
    intro x
    obtain ⟨i, hi⟩ := hcl (glueLeaf σ TA TB (.inl x)) ⟨x.1.1, rfl⟩
    obtain ⟨z, hz⟩ := (glueLeaf σ TA TB).surjective (pr (glueLeaf σ TA TB (.inl x)))
    rcases z with y | y
    · exact ⟨y, hz.symm⟩
    · have : (pr (glueLeaf σ TA TB (.inl x))).1.1 = σ (.inr y.1.1) := by rw [← hz]; rfl
      rw [this] at hi
      simp at hi
  have hB : ∀ x : GLeaf TB, ∃ y : GLeaf TB, pr (glueLeaf σ TA TB (.inr x)) = glueLeaf σ TA TB (.inr y) := by
    intro x
    obtain ⟨z, hz⟩ := (glueLeaf σ TA TB).surjective (pr (glueLeaf σ TA TB (.inr x)))
    rcases z with y | y
    · exfalso
      have e : pr (glueLeaf σ TA TB (.inl y)) = glueLeaf σ TA TB (.inr x) := by
        rw [hz, h1]
      obtain ⟨i, hi⟩ := hcl (glueLeaf σ TA TB (.inl y)) ⟨y.1.1, rfl⟩
      rw [e] at hi
      have : (glueLeaf σ TA TB (.inr x)).1.1 = σ (.inr x.1.1) := rfl
      rw [this] at hi
      simp at hi
    · exact ⟨y, hz.symm⟩
  choose pA hpA using hA
  choose pB hpB using hB
  refine ⟨
    { sig := fun i => sg (σ (.inl i)), tree := TA, pair := pA,
      mark := fun x => mk (glueLeaf σ TA TB (.inl x))
      pair_pair := fun x => by
        apply (glueLeaf σ TA TB).injective.comp Sum.inl_injective |>.eq_iff.mp
        show glueLeaf σ TA TB (.inl (pA (pA x))) = glueLeaf σ TA TB (.inl x)
        rw [← hpA, ← hpA, h1]
      pair_eq_iff := fun x => by
        have := h2 (glueLeaf σ TA TB (.inl x))
        rw [hpA] at this
        rwa [EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at this
      pair_sign := fun x hx => by
        have hne : pr (glueLeaf σ TA TB (.inl x)) ≠ glueLeaf σ TA TB (.inl x) := by
          rw [hpA]
          intro e
          exact hx (by simpa using e)
        have := h3 _ hne
        rw [hpA] at this
        simpa [nodeSign, glueLeaf_inl] using this },
    { sig := fun i => sg (σ (.inr i)), tree := TB, pair := pB,
      mark := fun x => mk (glueLeaf σ TA TB (.inr x))
      pair_pair := fun x => by
        apply (glueLeaf σ TA TB).injective.comp Sum.inr_injective |>.eq_iff.mp
        show glueLeaf σ TA TB (.inr (pB (pB x))) = glueLeaf σ TA TB (.inr x)
        rw [← hpB, ← hpB, h1]
      pair_eq_iff := fun x => by
        have := h2 (glueLeaf σ TA TB (.inr x))
        rw [hpB] at this
        rwa [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq] at this
      pair_sign := fun x hx => by
        have hne : pr (glueLeaf σ TA TB (.inr x)) ≠ glueLeaf σ TA TB (.inr x) := by
          rw [hpB]
          intro e
          exact hx (by simpa using e)
        have := h3 _ hne
        rw [hpB] at this
        simpa [nodeSign, glueLeaf_inr] using this }, ?_⟩
  simp only [glueGarden, Garden.mk.injEq, heq_eq_eq]
  refine ⟨?_, trivial, ?_, ?_⟩
  · funext c
    obtain ⟨s, rfl⟩ := σ.surjective c
    rcases s with i | i <;> simp [gSig]
  · funext ℓ
    obtain ⟨z, rfl⟩ := (glueLeaf σ TA TB).surjective ℓ
    rcases z with x | x
    · simp [hpA]
    · simp [hpB]
  · funext ℓ
    obtain ⟨z, rfl⟩ := (glueLeaf σ TA TB).surjective ℓ
    rcases z with x | x <;> simp

/-- Layered version of `exists_glue_garden`. -/
theorem exists_glue_layered (σ : Fin a ⊕ Fin b ≃ Fin w) (LG : LayeredGarden w)
    (hcl : ∀ ℓ : GLeaf LG.garden.tree, (∃ i, ℓ.1.1 = σ (.inl i)) → ∃ i, (LG.garden.pair ℓ).1.1 = σ (.inl i)) :
    ∃ LA LB, glueLayered σ LA LB = LG := by
  obtain ⟨GA, GB, hG⟩ := exists_glue_garden σ LG.garden hcl
  obtain ⟨G, layer, hl⟩ := LG
  simp only at hG
  subst hG
  refine ⟨⟨GA, fun x => layer (glueNode σ GA.tree GB.tree (.inl x)), ?_⟩,
    ⟨GB, fun x => layer (glueNode σ GA.tree GB.tree (.inr x)), ?_⟩, ?_⟩
  · constructor
    · intro br i
      have h := hl.1 (glueBranch σ GA.tree GB.tree (.inl br)) i
      rwa [glueBranch_child_inl, glueBranch_toNode_inl] at h
    · intro ℓ
      have h := hl.2 (glueLeaf σ GA.tree GB.tree (.inl ℓ))
      rwa [glue_pair_leaf_inl, glueLeaf_toNode_inl, glueLeaf_toNode_inl] at h
  · constructor
    · intro br i
      have h := hl.1 (glueBranch σ GA.tree GB.tree (.inr br)) i
      rwa [glueBranch_child_inr, glueBranch_toNode_inr] at h
    · intro ℓ
      have h := hl.2 (glueLeaf σ GA.tree GB.tree (.inr ℓ))
      rwa [glue_pair_leaf_inr, glueLeaf_toNode_inr, glueLeaf_toNode_inr] at h
  · simp only [glueLayered, LayeredGarden.mk.injEq, heq_eq_eq, true_and]
    funext x
    obtain ⟨y, rfl⟩ := (glueNode σ GA.tree GB.tree).surjective x
    rcases y with y | y <;> simp

end WaveTurbulence.FlowerP7
