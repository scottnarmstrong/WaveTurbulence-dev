/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Level1
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Regroup
/-! FLOWER-P7: the sum over a first-level piece as a regrouped sum over data pairs. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b : ℕ}

/-- The data of a component: its order and the vector of top orders of its trees. -/
def compData (p : ℕ) {w : ℕ} (L : LayeredGarden w) : ℕ × (Fin w → ℕ) := (L.garden.order, fun i => L.topOrder p i)

/-- The first components. -/
def Acomp1 (P : WTParams) (p N : ℕ) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3)) (i0 : Fin a) :
    Set (LayeredGarden a) :=
  {LA | LA.garden.sig = (fun i => childSig (σ (.inl i))) ∧ CompCond P p LA ∧ IrrAt LA.garden i0 ∧
    LA.garden.order ≤ N}

/-- The second components. -/
def Bcomp1 (P : WTParams) (p N : ℕ) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3)) :
    Set (LayeredGarden b) :=
  {LB | LB.garden.sig = (fun i => childSig (σ (.inr i))) ∧ CompCond P p LB ∧ LB.garden.order ≤ N}

/-- The joint condition on the data. -/
def Joint1 (P : WTParams) (p N : ℕ) (kind : TreeKind) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3))
    (d : ℕ × (Fin a → ℕ)) (e : ℕ × (Fin b → ℕ)) : Prop :=
  d.1 + e.1 + 2 = N ∧ VecKindOK (P.N (p + 1)) kind (glueVec σ d.2 e.2)

open scoped Classical in
noncomputable instance (P : WTParams) (p N : ℕ) (kind : TreeKind) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3))
    (d : ℕ × (Fin a → ℕ)) (e : ℕ × (Fin b → ℕ)) : Decidable (Joint1 P p N kind σ d e) :=
  Classical.propDecidable _

theorem Acomp1_finite (P : WTParams) (p N : ℕ) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3)) (i0 : Fin a) :
    (Acomp1 P p N σ i0).Finite :=
  (Canon.finite_layeredGardens a N p).subset fun LA h => ⟨h.2.2.2, h.2.1.2.1.1⟩

theorem Bcomp1_finite (P : WTParams) (p N : ℕ) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3)) :
    (Bcomp1 P p N (a := a) σ).Finite :=
  (Canon.finite_layeredGardens b N p).subset fun LB h => ⟨h.2.2, h.2.1.2.1.1⟩

theorem Pairs1_eq (P : WTParams) (p N : ℕ) (kind : TreeKind) {a b : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3))
    (i0 : Fin a) :
    Pairs1 P p N kind σ i0 =
      {x | x ∈ Acomp1 P p N σ i0 ×ˢ Bcomp1 P p N (a := a) σ ∧
        Joint1 P p N kind σ (compData p x.1) (compData p x.2)} := by
  ext x
  simp only [Pairs1, Acomp1, Bcomp1, Joint1, compData, Set.mem_setOf_eq, Set.mem_prod]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨⟨h1, h3, h4, by omega⟩, h2, h5, by omega⟩, h6, h7⟩
  · rintro ⟨⟨⟨h1, h3, h4, -⟩, h2, h5, -⟩, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

open scoped Classical in
/-- **Norm bound for a first-level piece** from bounds on the slice sums of the two components. -/
theorem piece1_norm_le (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind) {a b : ℕ}
    (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3)) (i0 : Fin a) (tt : Fin (2 * 3) → ℝ) (k : Mom P.d)
    (n : Fin (2 * 3) → (Fin P.d → ℤ))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |F q (k + latticePoint P.L m)|)
    (RA : ℕ × (Fin a → ℕ) → Prop) (RB : ℕ × (Fin b → ℕ) → Prop)
    (hJ : ∀ d e, Joint1 P p N kind σ d e → RA d ∧ RB e)
    (bA : ℕ × (Fin a → ℕ) → ℝ) (bB : ℕ × (Fin b → ℕ) → ℝ)
    (hA : ∀ d ∈ (Acomp1_finite P p N σ i0).toFinset.image (compData p), RA d →
      ‖∑ LA ∈ (Acomp1_finite P p N σ i0).toFinset.filter (fun LA => compData p LA = d),
        kernelKgen P.L P.γ P.δ F LA (fun _ => none) ∅ (fun _ => 1) (fun x => tt (σ (.inl x.1.1))) k (fun i => n (σ (.inl i))) 0‖ ≤ bA d)
    (hB : ∀ e ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.image (compData p), RB e →
      ‖∑ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
        kernelKgen P.L P.γ P.δ F LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt (σ (.inr x.1.1))) k (fun i => n (σ (.inr i))) 0‖ ≤ bB e) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧
        MinimalAt y.garden (σ (.inl i0)) (Finset.univ.image fun i => σ (.inl i))},
        kernelKgen P.L P.γ P.δ F y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      ∑ d ∈ (Acomp1_finite P p N σ i0).toFinset.image (compData p),
        ∑ e ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.image (compData p),
          if Joint1 P p N kind σ d e then bA d * bB e else 0 := by
  rw [piece1_sum P F p N kind σ i0 tt k n hF, Pairs1_eq]
  have hfin : {x : LayeredGarden a × LayeredGarden b | x ∈ Acomp1 P p N σ i0 ×ˢ Bcomp1 P p N (a := a) σ ∧
      Joint1 P p N kind σ (compData p x.1) (compData p x.2)}.Finite :=
    ((Acomp1_finite P p N σ i0).prod (Bcomp1_finite P p N (a := a) σ)).subset fun x hx => hx.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hset : hfin.toFinset = ((Acomp1_finite P p N σ i0).toFinset ×ˢ (Bcomp1_finite P p N (a := a) σ).toFinset).filter
      (fun x => Joint1 P p N kind σ (compData p x.1) (compData p x.2)) := by
    ext x
    simp [Set.Finite.mem_toFinset, Finset.mem_product]
  rw [hset]
  exact norm_pairs_le _ _ (compData p) (compData p) (Joint1 P p N kind σ) _ _ RA RB hJ bA bB hA hB

end WaveTurbulence.FlowerP7
