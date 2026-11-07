/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerCutBound
/-! The weighted uniform flower family `UniformFlowerFamilyW` (an extra weight `W`, `|W| ≤ 1`),
and the convergent polynomial-family bookkeeping for it. Generalizes main's `FC23.FlowerSeries`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FamilyW
open Finset GraftGen Polynomial WaveTurbulence.FC23

/-- The FC23 uniform flower family, with every weight multiplied by an extra `W`. -/
def UniformFlowerFamilyW (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (M A : ℝ) (ρ : Fin w → ℝ) (B : ℝ) : Prop :=
  ∀ tail small : Fin w → Bool, ∀ z : Fin w → ℝ, (∀ j, z j ∈ Set.Icc (0 : ℝ) (ρ j)) →
    ‖flowerWeighted P F p N kind pat dagger
      (fun LG k => W LG k * flowerFamilyWeight LG p M A tail small z k) ζ t s n n'‖ ≤ B

theorem familyW_one (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (M A : ℝ) (ρ : Fin w → ℝ) (B : ℝ) :
    UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' (fun _ _ => 1) M A ρ B ↔
      FC23UniformFlowerFamily P F p N kind pat dagger ζ t s n n' M A ρ B := by
  unfold UniformFlowerFamilyW FC23UniformFlowerFamily
  simp only [one_mul]

variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

/-- Pulling the extra weight out of a series term. -/
theorem flowerSeriesTerm_mul
    (W g : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (i : flowerSeriesIndex P p N kind pat ζ n n') :
    flowerSeriesTerm P F p N kind pat dagger ζ t s n n' (fun LG k => W LG k * g LG k) i =
      (W i.1.1 (cosetDecoration i.1.1.garden P.L 0 i.2.1) : ℂ) *
        flowerSeriesTerm P F p N kind pat dagger ζ t s n n' g i := by
  unfold flowerSeriesTerm kernelGenFactor
  push_cast
  ring

/-- Polynomial coefficients of the `W`-weighted family: `W` evaluated on the coset decoration. -/
def flowerPolynomialKW
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (M : ℝ)
    (tail small : Fin w → Bool) : flowerSeriesIndex P p N kind pat ζ n n' → ℂ :=
  fun i => (W i.1.1 (cosetDecoration i.1.1.garden P.L 0 i.2.1) : ℂ) *
    flowerPolynomialK P F p N kind pat dagger ζ t s n n' M tail small i

theorem flowerSeries_polynomial_termW
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (M A : ℝ) (tail small : Fin w → Bool) (z : Fin w → ℝ)
    (i : flowerSeriesIndex P p N kind pat ζ n n') :
    flowerSeriesTerm P F p N kind pat dagger ζ t s n n'
      (fun LG k => W LG k * flowerFamilyWeight LG p M A tail small z k) i =
      flowerPolynomialKW P F p N kind pat dagger ζ t s n n' W M tail small i *
        ∏ j, (flowerPolynomialQ P p N kind pat ζ n n' M A tail i j).eval (z j : ℂ) := by
  rw [flowerSeriesTerm_mul P F p N kind pat dagger ζ t s n n' W
    (fun LG k => flowerFamilyWeight LG p M A tail small z k) i,
    flowerSeries_polynomial_term P F p N kind pat dagger ζ t s n n' M A tail small z i]
  unfold flowerPolynomialKW
  ring

/-- Bounded-weight summability of the `W`-weighted family summands. -/
theorem flower_family_summableW {p w : ℕ}
    (LG : LayeredGarden w) (hc : IsCanonH (p + 1) LG)
    (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hW : ∀ k, |W LG k| ≤ 1)
    (M A : ℝ) (tail small : Fin w → Bool) (z : Fin w → ℝ) (t s : ℝ)
    (n n' : Fin P.d → ℤ)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|) :
    Summable (kernelGenFactor P.L P.γ P.δ F LG (LG.fixPat pat t s)
      (if dagger.isSome then univ.filter LG.garden.IsFlowerParent else ∅)
      (fun k => (W LG k * flowerFamilyWeight LG p M A tail small z k) *
        (dagger.elim 1 fun c => LG.sibWeight c k)) (fun _ => t) 0 (n := fun _ => n) (nfl := n')) := by
  apply summable_kernelGenFactor_bounded (C :=
    (1 + 2 * ∑ j, |z j|) ^ Fintype.card (GLeaf LG.garden.tree))
  · positivity
  · intro k
    have h1 := flowerFamilyWeight_abs_le LG p M A tail small z k
    have hs : |(dagger.elim 1 fun c => LG.sibWeight c k)| ≤ 1 := by
      cases dagger with
      | none => norm_num
      | some c => exact sibWeight_abs_le LG c k
    rw [abs_mul, abs_mul]
    calc _ ≤ 1 * (1 + 2 * ∑ j, |z j|) ^ Fintype.card (GLeaf LG.garden.tree) * 1 :=
          mul_le_mul (mul_le_mul (hW k) h1 (abs_nonneg _) zero_le_one) hs (abs_nonneg _)
            (by positivity)
      _ = _ := by ring
  · intro l hl
    have he := hc.1.2.1 l (by rw [hl]; simp)
    change LG.garden.mark l = some MarkTag.equal at he
    rw [hl] at he
    cases he
  · simpa only [zero_add] using hF

theorem flowerW_eq_polynomialFamily
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hW : ∀ LG k, |W LG k| ≤ 1) (M A : ℝ) (tail small : Fin w → Bool) (z : Fin w → ℝ)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|) :
    flowerWeighted P F p N kind pat dagger
      (fun LG k => W LG k * flowerFamilyWeight LG p M A tail small z k) ζ t s n n' =
      polynomialFamily (flowerPolynomialKW P F p N kind pat dagger ζ t s n n' W M tail small)
        (flowerPolynomialQ P p N kind pat ζ n n' M A tail) (fun j => (z j : ℂ)) := by
  rw [flowerWeighted_eq_series]
  · exact tsum_congr (flowerSeries_polynomial_termW P F p N kind pat dagger ζ t s n n' W M A tail
      small z)
  · intro LG
    exact (flower_family_summableW P F LG.1 LG.2.1 pat dagger W (hW LG.1) M A tail small z t s n n'
      hF).mul_left ((coupling P.d P.L P.γ P.δ : ℂ) ^ LG.1.garden.order * LG.1.garden.zeta)

theorem uniformFlowerFamilyW_evaluationBox
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hW : ∀ LG k, |W LG k| ≤ 1) (M A : ℝ) (ρ : Fin w → ℝ) (B : ℝ)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (H : UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' W M A ρ B)
    (tail small : Fin w → Bool) :
    FC23UniformEvaluationBox
      (flowerPolynomialKW P F p N kind pat dagger ζ t s n n' W M tail small)
      (flowerPolynomialQ P p N kind pat ζ n n' M A tail) ρ B := by
  intro z hz
  constructor
  · have hs := flowerSeries_summable P F p N kind pat dagger ζ t s n n'
      (fun LG k => W LG k * flowerFamilyWeight LG p M A tail small z k) (fun LG =>
        (flower_family_summableW P F LG.1 LG.2.1 pat dagger W (hW LG.1) M A tail small z t s n n'
          hF).mul_left ((coupling P.d P.L P.γ P.δ : ℂ) ^ LG.1.garden.order * LG.1.garden.zeta))
    exact hs.congr (flowerSeries_polynomial_termW P F p N kind pat dagger ζ t s n n' W M A tail
      small z)
  · rw [← flowerW_eq_polynomialFamily P F p N kind pat dagger ζ t s n n' W hW M A tail small z hF]
    exact H tail small z hz
end WaveTurbulence.Flower.FamilyW
