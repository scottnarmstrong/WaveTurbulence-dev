/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueEquiv

/-!
# The one kernel of a glued garden is a product (TARGET (prooflayer1-1), (prooflayer1-2))

In the gluing situation `GlueData G G₁ G₂ X`, every factor of the one kernel `kernelK` (snapshot 7,
T Def `defkg`) splits along the branch equivalence and the node maps:

* `order_glue`, `zeta_glue`: the order adds, `ζ(𝒢)` multiplies;
* `epsDec_glue`, `phaseProd_glue`: the Wick factor and the phases multiply;
* `phaseIntegral_glue`: if the time domain is the product of the two time domains (the cross-piece
  constraints being implied by the layers), the phase integral is a product (Fubini);
* **`kernelK_glue`**: with the input factors split and absolutely summable decoration sums, the kernel
  is the product of the kernels of the two pieces.
-/

@[expose] public section

open MeasureTheory

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg

/-- Without flower parents the phase integral is the plain integral over all branching times. -/
theorem phaseIntegral_noFlower (L γ δ : ℝ) {w d : ℕ} (G : Garden w)
    (hnf : ∀ b : GBranch G.tree, ¬ G.IsFlowerParent b) (D : Set (GBranch G.tree → ℝ)) (s : ℝ)
    (kv : GNode G.tree → Mom d) :
    phaseIntegral L γ δ G D s kv = ∫ τ : GBranch G.tree → ℝ, D.indicator (phaseProd L γ δ G kv) τ := by
  let e₀ : G.FreeBranch ≃ GBranch G.tree := Equiv.subtypeUnivEquiv hnf
  let Φ : (G.FreeBranch → ℝ) ≃ᵐ (GBranch G.tree → ℝ) :=
    MeasurableEquiv.arrowCongr' e₀ (MeasurableEquiv.refl ℝ)
  have hΦ : MeasurePreserving Φ volume volume :=
    measurePreserving_arrowCongr' (fun _ => volume) (fun _ => volume) e₀ (MeasurableEquiv.refl ℝ)
      fun _ => MeasurePreserving.id volume
  have hext : ∀ τ : G.FreeBranch → ℝ, G.extendTime s τ = Φ τ := by
    intro τ
    funext b
    simp only [Garden.extendTime, dite_eq_right (hnf b), Φ, MeasurableEquiv.arrowCongr',
      MeasurableEquiv.coe_mk, Equiv.arrowCongr', Equiv.arrowCongr, Equiv.coe_fn_mk,
      Function.comp_apply, MeasurableEquiv.refl, e₀]
    rfl
  unfold phaseIntegral
  simp_rw [hext]
  exact hΦ.integral_comp' (fun τ => D.indicator (phaseProd L γ δ G kv) τ)

variable {w : ℕ} [NeZero w]

namespace GlueData

variable {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
variable (h : GlueData G G₁ G₂ X)
include h

theorem ofSum_inl_toNode (x : GBranch G₁.tree) : (h.ofSum (.inl x)).toNode = h.ι₁ x.toNode := rfl

theorem ofSum_inr_toNode (y : GBranch G₂.tree) : (h.ofSum (.inr y)).toNode = h.ι₂ y.toNode := rfl

theorem ofSum_inl_child (x : GBranch G₁.tree) (i : Fin 3) :
    (h.ofSum (.inl x)).child i = h.ι₁ (x.child i) := rfl

theorem ofSum_inr_child (y : GBranch G₂.tree) (i : Fin 3) :
    (h.ofSum (.inr y)).child i = h.ι₂ (y.child i) :=
  Subtype.ext (botAddr_hom X.lonePath y.1 [i]).symm

theorem sign_ι₁ (x : GNode G₁.tree) : G.sign (h.ι₁ x) = G₁.sign x := by
  obtain ⟨⟨j, p⟩, hp⟩ := x
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  show pathSign (G.sig 0) p = pathSign (G₁.sig 0) p
  rw [h.sig1]

theorem sign_ι₂ (y : GNode G₂.tree) : G.sign (h.ι₂ y) = G₂.sign y := by
  obtain ⟨⟨j, p⟩, hp⟩ := y
  show pathSign (G.sig (botAddr X.lonePath (j, p)).1) (botAddr X.lonePath (j, p)).2 =
    pathSign (G₂.sig j) p
  by_cases hj : j = 0
  · subst hj
    simp only [botAddr, ite_true]
    rw [Comb.pathSign_append, lonePath_sign, h.sig]
  · simp only [botAddr, hj, ite_false, h.sig]

theorem prod_branch {M : Type*} [CommMonoid M] (f : GBranch G.tree → M) :
    ∏ b, f b = (∏ x, f (h.ofSum (.inl x))) * ∏ y, f (h.ofSum (.inr y)) := by
  rw [← h.branchEquiv.symm.prod_comp, Fintype.prod_sum_type]
  rfl

theorem order_glue : G.order = G₁.order + G₂.order := by
  unfold Garden.order
  rw [← card_gbranch, ← card_gbranch, ← card_gbranch, Fintype.card_congr h.branchEquiv,
    Fintype.card_sum]

theorem zeta_glue : G.zeta = G₁.zeta * G₂.zeta := by
  unfold Garden.zeta
  rw [h.prod_branch]
  simp only [ofSum_inl_toNode, ofSum_inr_toNode, sign_ι₁, sign_ι₂]

theorem epsDec_glue {d : ℕ} (κ : GNode G.tree → (Fin d → ℤ)) :
    epsDec G κ = epsDec G₁ (κ ∘ h.ι₁) * epsDec G₂ (κ ∘ h.ι₂) := by
  unfold epsDec
  rw [h.prod_branch]
  simp only [ofSum_inl_child, ofSum_inr_child, Function.comp_apply]

theorem omegaNode_inl {d : ℕ} (kv : GNode G.tree → Mom d) (x : GBranch G₁.tree) :
    omegaNode G kv (h.ofSum (.inl x)) = omegaNode G₁ (kv ∘ h.ι₁) x := by
  simp only [omegaNode, ofSum_inl_child, ofSum_inl_toNode, Function.comp_apply]

theorem omegaNode_inr {d : ℕ} (kv : GNode G.tree → Mom d) (y : GBranch G₂.tree) :
    omegaNode G kv (h.ofSum (.inr y)) = omegaNode G₂ (kv ∘ h.ι₂) y := by
  simp only [omegaNode, ofSum_inr_child, ofSum_inr_toNode, Function.comp_apply]

theorem phaseProd_glue (L γ δ : ℝ) {d : ℕ} (kv : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) :
    phaseProd L γ δ G kv τ = phaseProd L γ δ G₁ (kv ∘ h.ι₁) (fun x => τ (h.ofSum (.inl x))) *
      phaseProd L γ δ G₂ (kv ∘ h.ι₂) (fun y => τ (h.ofSum (.inr y))) := by
  unfold phaseProd
  rw [h.prod_branch]
  simp only [omegaNode_inl, omegaNode_inr, ofSum_inl_toNode, ofSum_inr_toNode, sign_ι₁, sign_ι₂]

/-- **The phase integral of a glued garden is a product** when its time domain is the product of the
two time domains (Fubini). -/
theorem phaseIntegral_glue (L γ δ : ℝ) {d : ℕ}
    (hnf : ∀ b : GBranch G.tree, ¬ G.IsFlowerParent b)
    (hnf₁ : ∀ b : GBranch G₁.tree, ¬ G₁.IsFlowerParent b)
    (hnf₂ : ∀ b : GBranch G₂.tree, ¬ G₂.IsFlowerParent b)
    (D : Set (GBranch G.tree → ℝ)) (D₁ : Set (GBranch G₁.tree → ℝ)) (D₂ : Set (GBranch G₂.tree → ℝ))
    (hD : ∀ τ, τ ∈ D ↔ (fun x => τ (h.ofSum (.inl x))) ∈ D₁ ∧ (fun y => τ (h.ofSum (.inr y))) ∈ D₂)
    (s s₁ s₂ : ℝ) (kv : GNode G.tree → Mom d) :
    phaseIntegral L γ δ G D s kv =
      phaseIntegral L γ δ G₁ D₁ s₁ (kv ∘ h.ι₁) * phaseIntegral L γ δ G₂ D₂ s₂ (kv ∘ h.ι₂) := by
  rw [phaseIntegral_noFlower L γ δ G hnf, phaseIntegral_noFlower L γ δ G₁ hnf₁,
    phaseIntegral_noFlower L γ δ G₂ hnf₂]
  let Φ₁ : (GBranch G.tree → ℝ) ≃ᵐ (GBranch G₁.tree ⊕ GBranch G₂.tree → ℝ) :=
    MeasurableEquiv.arrowCongr' h.branchEquiv (MeasurableEquiv.refl ℝ)
  let Φ₂ := MeasurableEquiv.sumPiEquivProdPi (fun _ : GBranch G₁.tree ⊕ GBranch G₂.tree => ℝ)
  have hΦ₁ : MeasurePreserving Φ₁ volume volume :=
    measurePreserving_arrowCongr' (fun _ => volume) (fun _ => volume) h.branchEquiv
      (MeasurableEquiv.refl ℝ) fun _ => MeasurePreserving.id volume
  have hΦ₂ : MeasurePreserving Φ₂ volume volume := volume_measurePreserving_sumPiEquivProdPi _
  let Ψ := Φ₁.trans Φ₂
  have hΨ : MeasurePreserving Ψ volume volume := hΦ₂.comp hΦ₁
  let g : (GBranch G₁.tree → ℝ) × (GBranch G₂.tree → ℝ) → ℂ := fun z =>
    D₁.indicator (phaseProd L γ δ G₁ (kv ∘ h.ι₁)) z.1 * D₂.indicator (phaseProd L γ δ G₂ (kv ∘ h.ι₂)) z.2
  have key : ∀ τ : GBranch G.tree → ℝ, D.indicator (phaseProd L γ δ G kv) τ = g (Ψ τ) := by
    intro τ
    have e1 : (Ψ τ).1 = fun x => τ (h.ofSum (.inl x)) := rfl
    have e2 : (Ψ τ).2 = fun y => τ (h.ofSum (.inr y)) := rfl
    simp only [g, e1, e2]
    by_cases h1 : (fun x => τ (h.ofSum (.inl x))) ∈ D₁ <;>
      by_cases h2 : (fun y => τ (h.ofSum (.inr y))) ∈ D₂
    · rw [Set.indicator_of_mem ((hD τ).mpr ⟨h1, h2⟩), Set.indicator_of_mem h1,
        Set.indicator_of_mem h2, h.phaseProd_glue]
    · rw [Set.indicator_of_notMem (fun hm => h2 ((hD τ).mp hm).2), Set.indicator_of_notMem h2,
        mul_zero]
    · rw [Set.indicator_of_notMem (fun hm => h1 ((hD τ).mp hm).1), Set.indicator_of_notMem h1,
        zero_mul]
    · rw [Set.indicator_of_notMem (fun hm => h1 ((hD τ).mp hm).1), Set.indicator_of_notMem h1,
        zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall key), hΨ.integral_comp' g]
  exact integral_prod_mul (fun z₁ => D₁.indicator (phaseProd L γ δ G₁ (kv ∘ h.ι₁)) z₁)
    (fun z₂ => D₂.indicator (phaseProd L γ δ G₂ (kv ∘ h.ι₂)) z₂)

end GlueData

theorem noFlowerParent_of_noFlower {w : ℕ} {G : Garden w} (hfl : ∀ ℓ : GLeaf G.tree, ¬ G.IsFlower ℓ)
    (b : GBranch G.tree) : ¬ G.IsFlowerParent b := fun ⟨ℓ, hℓ, _⟩ => hfl ℓ hℓ

end WaveTurbulence.PL234
