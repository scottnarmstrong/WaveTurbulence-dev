/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Terms
public import WaveTurbulence.Foundations.Flower.CapsGlue.Fubini
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueIdentity
/-! # A3a CAPS-GLUE: the kernel `kernelKgen` of an n-ary glue is the product of the component kernels
(general `fix`, `off`, `wt`, `up`). Generalizes FLOWER-P7's `kernelKgen_glue` (binary, `fix ≡ none`, `off = ∅`,
`wt ≡ 1`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset MeasureTheory WaveTurbulence.FlowerP7

variable {m w d : ℕ} {a : Fin m → ℕ}

theorem glueL_layer_branch (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) (c : Fin m)
    (x : GBranch (LA c).garden.tree) :
    (glueL σ LA).layer (glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, x⟩).toNode = (LA c).layer x.toNode := by
  rw [glueBranchN_toNode]; exact glueL_layer ..

theorem glueN_isChildOf_same (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x' x : GBranch (TA c)) :
    (glueBranchN σ TA ⟨c, x'⟩).IsChildOf (glueBranchN σ TA ⟨c, x⟩) ↔ x'.IsChildOf x := by
  simp only [GBranch.IsChildOf, glueBranchN_val, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq,
    true_and]

theorem glueN_not_isChildOf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) {c c' : Fin m}
    (h : c' ≠ c) (x' : GBranch (TA c')) (x : GBranch (TA c)) :
    ¬ (glueBranchN σ TA ⟨c', x'⟩).IsChildOf (glueBranchN σ TA ⟨c, x⟩) := by
  rintro ⟨h1, -⟩
  simp only [glueBranchN_val, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq] at h1
  exact h h1.1

theorem glueN_domain_iff (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (up : ∀ c, GBranch (LA c).garden.tree → ℝ) (fix : ∀ c, GBranch (LA c).garden.tree → Option ℝ)
    (τ : ∀ c, GBranch (LA c).garden.tree → ℝ) :
    gBr σ (fun c => (LA c).garden.tree) τ ∈
        kDomainFix (glueL σ LA) (gBr σ (fun c => (LA c).garden.tree) up) (gBr σ (fun c => (LA c).garden.tree) fix) ↔
      ∀ c, τ c ∈ kDomainFix (LA c) (up c) (fix c) := by
  constructor
  · intro h c x
    have hx := h (glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, x⟩)
    refine ⟨fun hf => ?_, fun x' hx' hor => ?_⟩
    · have := hx.1 (by simpa using hf)
      rw [glueL_layer_branch] at this
      simpa only [gBr_apply] using this
    · have := hx.2 (glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, x'⟩)
        ((glueN_isChildOf_same σ (fun c => (LA c).garden.tree) c x' x).2 hx') (by simpa using hor)
      simpa only [gBr_apply] using this
  · intro h br
    obtain ⟨⟨c, x⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective br
    refine ⟨fun hf => ?_, fun b' hb' hor => ?_⟩
    · have := (h c x).1 (by simpa using hf)
      rw [glueL_layer_branch]
      simpa only [gBr_apply] using this
    · obtain ⟨⟨c', x'⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective b'
      by_cases hc : c' = c
      · subst hc
        have := (h c' x).2 x' ((glueN_isChildOf_same σ (fun c => (LA c).garden.tree) c' x' x).1 hb') (by simpa using hor)
        simpa only [gBr_apply] using this
      · exact absurd hb' (glueN_not_isChildOf σ (fun c => (LA c).garden.tree) hc x' x)

/-- The free branching nodes of the glue are the free nodes of the components. -/
noncomputable def freeEquivN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (fix : ∀ c, GBranch (TA c) → Option ℝ) :
    (Σ c : Fin m, {x : GBranch (TA c) // fix c x = none}) ≃
      {b : GBranch (gT σ TA) // gBr σ TA fix b = none} :=
  Equiv.ofBijective (fun y => ⟨glueBranchN σ TA ⟨y.1, y.2.1⟩, by simpa using y.2.2⟩) (by
    constructor
    · rintro ⟨c, x, hx⟩ ⟨c', x', hx'⟩ h
      have h' := (glueBranchN σ TA).injective (congrArg Subtype.val h)
      simp only [Sigma.mk.injEq] at h'
      obtain ⟨rfl, h2⟩ := h'
      have h2 := eq_of_heq h2
      subst h2
      rfl
    · rintro ⟨b, hb⟩
      obtain ⟨⟨c, x⟩, rfl⟩ := (glueBranchN σ TA).surjective b
      exact ⟨⟨c, x, by simpa using hb⟩, rfl⟩)

theorem freeEquivN_apply (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (fix : ∀ c, GBranch (TA c) → Option ℝ) (c : Fin m) (x : {x : GBranch (TA c) // fix c x = none}) :
    ((freeEquivN σ TA fix ⟨c, x⟩).1) = glueBranchN σ TA ⟨c, x.1⟩ := rfl

theorem extendFix_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (fix : ∀ c, GBranch (GA c).tree → Option ℝ)
    (τ : {b : GBranch (glueGardenN σ GA).tree // gBr σ (fun c => (GA c).tree) fix b = none} → ℝ) :
    (glueGardenN σ GA).extendFix (gBr σ (fun c => (GA c).tree) fix) τ =
      gBr σ (fun c => (GA c).tree) (fun c => (GA c).extendFix (fix c)
        (fun x => τ (freeEquivN σ (fun c => (GA c).tree) fix ⟨c, x⟩))) := by
  funext b
  obtain ⟨⟨c, x⟩, rfl⟩ := (glueBranchN σ fun c => (GA c).tree).surjective b
  rw [gBr_apply]
  rcases hf : fix c x with _ | v
  · rw [extendFix_none _ _ _ _ (by simpa using hf), extendFix_none _ _ _ _ hf]
    rfl
  · rw [extendFix_some _ _ _ _ v (by simpa using hf), extendFix_some _ _ _ _ v hf]

end WaveTurbulence.Flower.CapsGlue
