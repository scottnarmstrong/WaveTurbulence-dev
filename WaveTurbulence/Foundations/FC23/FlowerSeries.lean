/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerConvergence
public import WaveTurbulence.Foundations.FC23.ExponentialExtraction
/-! Exact convergent source sums for the real polynomial flower family. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset GraftGen Polynomial

variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

def flowerSeriesIndex : Type :=
  Σ LG : flowerCarrier P p N kind pat ζ, GenDecoration LG.1.garden P.d (fun _ => n) n'

def flowerSeriesTerm
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (i : flowerSeriesIndex P p N kind pat ζ n n') : ℂ :=
  (coupling P.d P.L P.γ P.δ : ℂ) ^ i.1.1.garden.order * i.1.1.garden.zeta *
    kernelGenFactor P.L P.γ P.δ F i.1.1 (i.1.1.fixPat pat t s)
      (if dagger.isSome then univ.filter i.1.1.garden.IsFlowerParent else ∅)
      (fun k => weight i.1.1 k * (dagger.elim 1 fun c => i.1.1.sibWeight c k))
      (fun _ => t) 0 i.2

theorem flowerSeries_summable
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hs : ∀ LG : flowerCarrier P p N kind pat ζ, Summable fun κ =>
      flowerSeriesTerm P F p N kind pat dagger ζ t s n n' weight ⟨LG, κ⟩) :
    Summable (flowerSeriesTerm P F p N kind pat dagger ζ t s n n' weight) := by
  let : Finite (flowerCarrier P p N kind pat ζ) := (flowerCarrier_finite P p N kind pat ζ).to_subtype
  let := Fintype.ofFinite (flowerCarrier P p N kind pat ζ)
  apply Summable.of_norm
  apply (summable_sigma_of_nonneg (fun i => norm_nonneg _)).mpr
  exact ⟨fun LG => (hs LG).norm, (hasSum_fintype _).summable⟩

/-- The frozen outer finsum and convergent decoration sums combine exactly. -/
theorem flowerWeighted_eq_series
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hs : ∀ LG : flowerCarrier P p N kind pat ζ, Summable fun κ =>
      flowerSeriesTerm P F p N kind pat dagger ζ t s n n' weight ⟨LG, κ⟩) :
    flowerWeighted P F p N kind pat dagger weight ζ t s n n' =
      ∑' i, flowerSeriesTerm P F p N kind pat dagger ζ t s n n' weight i := by
  let : Finite (flowerCarrier P p N kind pat ζ) := (flowerCarrier_finite P p N kind pat ζ).to_subtype
  have hf := flowerSeries_summable P F p N kind pat dagger ζ t s n n' weight hs
  refine Eq.trans ?_ hf.tsum_sigma.symm
  simp only [flowerSeriesTerm, tsum_mul_left]
  change (∑ᶠ LG ∈ flowerCarrier P p N kind pat ζ,
    flowerKernel P F p pat dagger weight t s n n' LG) =
      ∑' LG : flowerCarrier P p N kind pat ζ, flowerKernel P F p pat dagger weight t s n n' LG.1
  rw [← finsum_set_coe_eq_finsum_mem, tsum_eq_finsum (Set.toFinite _)]

def flowerBondWeight (LG : LayeredGarden w) (M : ℝ) (tail small : Fin w → Bool)
    (k : GNode LG.garden.tree → Mom P.d) : ℝ :=
  ∏ a : GNode LG.garden.tree,
    if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬LG.IsFlowerNode a then
      chi0 (‖k a‖ / (if tail a.1.1 && small a.1.1 then M / 2 else M)) else 1

def flowerPolynomialK (M : ℝ) (tail small : Fin w → Bool) :
    flowerSeriesIndex P p N kind pat ζ n n' → ℂ :=
  flowerSeriesTerm P F p N kind pat dagger ζ t s n n' (flowerBondWeight P p · M tail small)

def flowerPolynomialQ (M A : ℝ) (tail : Fin w → Bool)
    (i : flowerSeriesIndex P p N kind pat ζ n n') (j : Fin w) : ℂ[X] :=
  treeLeafPolynomial i.1.1 p M A tail (cosetDecoration i.1.1.garden P.L 0 i.2.1) j

/-- Pointwise factorization on the actual decorated flower carrier. -/
theorem flowerSeries_polynomial_term (M A : ℝ) (tail small : Fin w → Bool) (z : Fin w → ℝ)
    (i : flowerSeriesIndex P p N kind pat ζ n n') :
    flowerSeriesTerm P F p N kind pat dagger ζ t s n n'
      (fun LG k => flowerFamilyWeight LG p M A tail small z k) i =
      flowerPolynomialK P F p N kind pat dagger ζ t s n n' M tail small i *
        ∏ j, (flowerPolynomialQ P p N kind pat ζ n n' M A tail i j).eval (z j : ℂ) := by
  rw [show (∏ j, (flowerPolynomialQ P p N kind pat ζ n n' M A tail i j).eval (z j : ℂ)) = _ from
    treeLeafPolynomial_product i.1.1 p M A tail _ z]
  unfold flowerPolynomialK flowerSeriesTerm flowerBondWeight flowerFamilyWeight kernelGenFactor
  push_cast
  simp only [apply_ite, Complex.ofReal_one]
  ring

end WaveTurbulence.FC23
