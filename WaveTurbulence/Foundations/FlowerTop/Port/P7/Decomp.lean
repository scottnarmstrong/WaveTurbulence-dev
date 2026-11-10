/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSwap
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Shapes
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.PieceEq
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueY6
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GluePiece
/-! FLOWER-P7: the decapitated carrier `Y6Set` as a set of layered gardens, and its partition by the minimal
closed block of tree `0`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

/-- The decapitated carrier. -/
def Y6Set (P : WTParams) (p N : ℕ) (kind : TreeKind) : Set (LayeredGarden (2 * 3)) :=
  {y | (∀ c, y.garden.sig c = childSig c) ∧ Y6Cond P p N kind y}

theorem Y6Set_finite (P : WTParams) (p N : ℕ) (kind : TreeKind) : (Y6Set P p N kind).Finite := by
  refine (Canon.finite_layeredGardens (2 * 3) N p).subset fun y hy => ⟨?_, hy.2.2.1.1⟩
  have := hy.2.2.2.2.1
  omega

theorem Y6Set_plain (P : WTParams) (p N : ℕ) (kind : TreeKind) {y : LayeredGarden (2 * 3)}
    (h : y ∈ Y6Set P p N kind) : y.garden.IsPlain := h.2.1

/-- The sum over `CapSrc` with the six-tree condition is the sum over `Y6Set`. -/
theorem finsum_capSrc_eq (P : WTParams) (p N : ℕ) (kind : TreeKind) (f : LayeredGarden (2 * 3) → ℂ) :
    ∑ᶠ (y : CapSrc p) (_ : Y6Cond P p N kind y.1), f y.1 = ∑ᶠ y ∈ Y6Set P p N kind, f y := by
  classical
  have hset : Y6Set P p N kind = (Subtype.val : CapSrc p → LayeredGarden (2 * 3)) ''
      {y : CapSrc p | Y6Cond P p N kind y.1} := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h1, h2.2.1.1⟩, h2, rfl⟩
    · rintro ⟨y', h, rfl⟩
      exact ⟨y'.2.1, h⟩
  rw [hset, finsum_mem_image Subtype.val_injective.injOn]
  rfl

/-- **`coupleSum … true` over the carrier `Y6Set`.** -/
theorem coupleSum_true_Y6 (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind) (t : ℝ)
    (k : Mom P.d)
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |F q (k + latticePoint P.L n)|) :
    coupleSum P F p N kind true t k =
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d, outerWeight P.L P.γ P.δ k t n.1 *
        ∑ᶠ y ∈ Y6Set P p N kind,
          kernelKgen P.L P.γ P.δ F y (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 := by
  rw [coupleSum_true_swap P F p N kind t k hF]
  congr 2
  funext n
  rw [finsum_capSrc_eq P p N kind (fun y => kernelKgen P.L P.γ P.δ F y (fun _ => none) ∅ (fun _ => 1)
    (fun _ => t) k n.1 0)]

/-- The ten admissible components as a `Finset`. -/
def shapeFin : Finset (Finset (Fin (2 * 3))) := shapeList.toFinset

/-- **Partition of the carrier by the minimal closed block of tree `0`.** -/
theorem finsum_Y6_partition (P : WTParams) (p N : ℕ) (kind : TreeKind) (f : LayeredGarden (2 * 3) → ℂ) :
    ∑ᶠ y ∈ Y6Set P p N kind, f y =
      ∑ S ∈ shapeFin, ∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 S}, f y := by
  classical
  have hfin := Y6Set_finite P p N kind
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : ∀ S ∈ shapeFin, {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 S}.Finite := fun S _ =>
    hfin.subset fun y hy => hy.1
  have e1 : ∀ S ∈ shapeFin, ∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 S}, f y =
      ∑ y ∈ hfin.toFinset, if MinimalAt y.garden 0 S then f y else 0 := by
    intro S hS
    rw [finsum_mem_eq_finite_toFinset_sum _ (hsub S hS), ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp [Set.Finite.mem_toFinset]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy' : y ∈ Y6Set P p N kind := hfin.mem_toFinset.1 hy
  obtain ⟨S, hSl, hS⟩ := exists_shape y.garden (Y6Set_plain P p N kind hy') hy'.1
  rw [Finset.sum_eq_single S]
  · simp [hS]
  · intro S' _ hne
    have : ¬ MinimalAt y.garden 0 S' := fun h =>
      hne (minimal_closed_unique y.garden (Y6Set_plain P p N kind hy') 0 h hS)
    simp [this]
  · intro h
    exact absurd (by simpa [shapeFin] using hSl) h

end WaveTurbulence.FlowerP7
