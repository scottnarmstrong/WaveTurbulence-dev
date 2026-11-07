/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Decomp
/-! FLOWER-P7: first-level pieces.  For a splitting `σ` with the first block containing tree `0` at index `i₀`,
the part of the carrier whose minimal closed block of tree `0` is the first block is a glue image, and the sum of
the six-tree kernels over it is a sum of products over a set of pairs of components. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

/-- The set of pairs of components of a first-level piece. -/
def Pairs1 (P : WTParams) (p N : ℕ) (kind : TreeKind) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3)) (i0 : Fin a) :
    Set (LayeredGarden a × LayeredGarden b) :=
  {x | x.1.garden.sig = (fun i => childSig (σ (.inl i))) ∧ x.2.garden.sig = (fun i => childSig (σ (.inr i))) ∧
    CompCond P p x.1 ∧ IrrAt x.1.garden i0 ∧ CompCond P p x.2 ∧
    x.1.garden.order + x.2.garden.order + 2 = N ∧
    VecKindOK (P.N (p + 1)) kind (glueVec σ (fun i => x.1.topOrder p i) (fun i => x.2.topOrder p i))}

theorem piece1_eq_image (P : WTParams) (p N : ℕ) (kind : TreeKind) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3))
    (i0 : Fin a) :
    {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden (σ (.inl i0)) (Finset.univ.image fun i => σ (.inl i))} =
      (fun x : LayeredGarden a × LayeredGarden b => glueLayered σ x.1 x.2) '' Pairs1 P p N kind σ i0 := by
  have h := piece_eq_image σ i0 (fun c => childSig c) (Y6Cond P p N kind) (CompCond P p) (CompCond P p)
    (fun LA LB => LA.garden.order + LB.garden.order + 2 = N ∧
      VecKindOK (P.N (p + 1)) kind (glueVec σ (fun i => LA.topOrder p i) (fun i => LB.topOrder p i)))
    (fun LA LB => glue_Y6Cond_iff P p N kind σ LA LB |>.trans
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩)
    (fun y hy => hy.1) (fun LA hA => hA.1)
  have e : {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden (σ (.inl i0)) (Finset.univ.image fun i => σ (.inl i))} =
      {y : LayeredGarden (2 * 3) | y.garden.sig = (fun c => childSig c) ∧ Y6Cond P p N kind y ∧
        MinimalAt y.garden (σ (.inl i0)) (Finset.univ.image fun i => σ (.inl i))} := by
    ext y
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨funext h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun c => congrFun h1 c, h2⟩, h3⟩
  rw [e, h]
  rfl

/-- **The sum over a first-level piece factors over the components.** -/
theorem piece1_sum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind) {a b : ℕ}
    (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3)) (i0 : Fin a) (tt : Fin (2 * 3) → ℝ) (k : Mom P.d) (n : Fin (2 * 3) → (Fin P.d → ℤ))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |F q (k + latticePoint P.L m)|) :
    ∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden (σ (.inl i0)) (Finset.univ.image fun i => σ (.inl i))},
        kernelKgen P.L P.γ P.δ F y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0 =
      ∑ᶠ x ∈ Pairs1 P p N kind σ i0,
        kernelKgen P.L P.γ P.δ F x.1 (fun _ => none) ∅ (fun _ => 1) (fun y => tt (σ (.inl y.1.1))) k (fun i => n (σ (.inl i))) 0 *
          kernelKgen P.L P.γ P.δ F x.2 (fun _ => none) ∅ (fun _ => 1) (fun y => tt (σ (.inr y.1.1))) k
            (fun i => n (σ (.inr i))) 0 := by
  rw [piece1_eq_image]
  exact finsum_glue_image P.L P.γ P.δ F σ (Pairs1 P p N kind σ i0) (fun x hx => ⟨hx.2.2.1.1, hx.2.2.2.2.1.1⟩) tt k n hF

end WaveTurbulence.FlowerP7
