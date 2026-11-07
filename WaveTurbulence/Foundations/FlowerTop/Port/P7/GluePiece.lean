/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueY6
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSwap
/-! FLOWER-P7: sums of six-tree kernels over a product piece `glue '' (A × B)` factor. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w d : ℕ}

theorem gRoot_restrict (σ : Fin a ⊕ Fin b ≃ Fin w) (n : Fin w → (Fin d → ℤ)) :
    gRoot σ (fun i => n (σ (.inl i))) (fun i => n (σ (.inr i))) = n := by
  funext c
  obtain ⟨s, rfl⟩ := σ.surjective c
  rcases s with i | i <;> simp [gRoot]

theorem up_tt_glue (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b) (tt : Fin w → ℝ) :
    (fun br => Sum.elim (fun x : GBranch LA.garden.tree => tt (σ (.inl x.1.1)))
      (fun x : GBranch LB.garden.tree => tt (σ (.inr x.1.1)))
      ((glueBranch σ LA.garden.tree LB.garden.tree).symm br)) = fun x => tt x.1.1 := by
  funext br
  obtain ⟨y, rfl⟩ := (glueBranch σ LA.garden.tree LB.garden.tree).surjective br
  rcases y with x | x <;> simp [glueBranch_inl, glueBranch_inr]

theorem plain_hlone {w : ℕ} (G : Garden w) (hG : G.IsPlain) (j : Fin w) :
    (Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsLone ℓ).card ≤ 1 := by
  rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun ℓ _ h => by
    have h2 := h.2
    unfold Garden.IsLone at h2
    rw [hG ℓ] at h2
    exact absurd h2 (by simp))]
  exact Nat.zero_le _

/-- The six-tree kernel of a glued garden factors (plain parts, summable inputs). -/
theorem kernelKgen_glue_const (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a)
    (LB : LayeredGarden b) (hA : LA.garden.IsPlain) (hB : LB.garden.IsPlain) (tt : Fin w → ℝ) (k : Mom d)
    (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q : ℕ, Summable fun m : Fin d → ℤ => |F q (k + latticePoint L m)|) :
    kernelKgen L γ δ F (glueLayered σ LA LB) (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0 =
      kernelKgen L γ δ F LA (fun _ => none) ∅ (fun _ => 1) (fun x => tt (σ (.inl x.1.1))) k (fun i => n (σ (.inl i))) 0 *
        kernelKgen L γ δ F LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt (σ (.inr x.1.1))) k (fun i => n (σ (.inr i))) 0 := by
  have hsA := summable_kgTerm L γ δ F LA (fun x => tt (σ (.inl x.1.1))) (fun _ => none) k
    (fun i => n (σ (.inl i))) 0 (plain_hlone _ hA) (fun ℓ _ => hF _)
  have hsB := summable_kgTerm L γ δ F LB (fun x => tt (σ (.inr x.1.1))) (fun _ => none) k
    (fun i => n (σ (.inr i))) 0 (plain_hlone _ hB) (fun ℓ _ => hF _)
  have := kernelKgen_glue L γ δ F σ LA LB (fun x => tt (σ (.inl x.1.1))) (fun x => tt (σ (.inr x.1.1))) k (fun i => n (σ (.inl i)))
    (fun i => n (σ (.inr i))) 0 hsA hsB
  rw [gRoot_restrict, up_tt_glue] at this
  exact this

/-- **Product pieces.**  The sum of the six-tree kernels over the glue image of `A × B` is the product of the sums. -/
theorem finsum_glue_piece (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (σ : Fin a ⊕ Fin b ≃ Fin w) (A : Set (LayeredGarden a))
    (B : Set (LayeredGarden b)) (hAf : A.Finite) (hBf : B.Finite)
    (hAp : ∀ LA ∈ A, LA.garden.IsPlain) (hBp : ∀ LB ∈ B, LB.garden.IsPlain) (tt : Fin w → ℝ) (k : Mom d)
    (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q : ℕ, Summable fun m : Fin d → ℤ => |F q (k + latticePoint L m)|) :
    ∑ᶠ y ∈ (fun x : LayeredGarden a × LayeredGarden b => glueLayered σ x.1 x.2) '' (A ×ˢ B),
        kernelKgen L γ δ F y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0 =
      (∑ᶠ LA ∈ A, kernelKgen L γ δ F LA (fun _ => none) ∅ (fun _ => 1) (fun x => tt (σ (.inl x.1.1))) k (fun i => n (σ (.inl i))) 0) *
        ∑ᶠ LB ∈ B, kernelKgen L γ δ F LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt (σ (.inr x.1.1))) k (fun i => n (σ (.inr i))) 0 := by
  classical
  have hinj : Set.InjOn (fun x : LayeredGarden a × LayeredGarden b => glueLayered σ x.1 x.2) (A ×ˢ B) := by
    intro x _ y _ h
    have := glueLayered_injective σ h
    exact Prod.ext this.1 this.2
  rw [finsum_mem_image hinj]
  rw [finsum_mem_eq_finite_toFinset_sum _ hAf, finsum_mem_eq_finite_toFinset_sum _ hBf,
    Finset.sum_mul_sum, finsum_mem_eq_finite_toFinset_sum _ (hAf.prod hBf)]
  rw [← Finset.sum_product']
  refine Finset.sum_congr ?_ fun x hx => ?_
  · ext x
    simp [Set.Finite.mem_toFinset, Finset.mem_product]
  · have hx' := Finset.mem_product.1 hx
    exact kernelKgen_glue_const L γ δ F σ x.1 x.2 (hAp _ (hAf.mem_toFinset.1 hx'.1))
      (hBp _ (hBf.mem_toFinset.1 hx'.2)) tt k n hF

/-- **Pieces indexed by an arbitrary set of pairs.** -/
theorem finsum_glue_image (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (σ : Fin a ⊕ Fin b ≃ Fin w)
    (P : Set (LayeredGarden a × LayeredGarden b))
    (hP : ∀ x ∈ P, x.1.garden.IsPlain ∧ x.2.garden.IsPlain) (tt : Fin w → ℝ) (k : Mom d)
    (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q : ℕ, Summable fun m : Fin d → ℤ => |F q (k + latticePoint L m)|) :
    ∑ᶠ y ∈ (fun x : LayeredGarden a × LayeredGarden b => glueLayered σ x.1 x.2) '' P,
        kernelKgen L γ δ F y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0 =
      ∑ᶠ x ∈ P, kernelKgen L γ δ F x.1 (fun _ => none) ∅ (fun _ => 1) (fun y => tt (σ (.inl y.1.1))) k
          (fun i => n (σ (.inl i))) 0 *
        kernelKgen L γ δ F x.2 (fun _ => none) ∅ (fun _ => 1) (fun y => tt (σ (.inr y.1.1))) k (fun i => n (σ (.inr i))) 0 := by
  have hinj : Set.InjOn (fun x : LayeredGarden a × LayeredGarden b => glueLayered σ x.1 x.2) P := by
    intro x _ y _ h
    have := glueLayered_injective σ h
    exact Prod.ext this.1 this.2
  rw [finsum_mem_image hinj]
  exact finsum_mem_congr rfl fun x hx => kernelKgen_glue_const L γ δ F σ x.1 x.2 (hP x hx).1 (hP x hx).2 tt k n hF

end WaveTurbulence.FlowerP7
