/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.GardenExtraction
public import WaveTurbulence.Foundations.FC23.ExtractionConvergence
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhaseCoordinates
/-! The conditional FC2 estimate on the literal frozen cut1 flower sum. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset Polynomial GraftGen
variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

def flowerExtractedTerm (M A : ℝ) (e : Fin w → Fin 3)
    (i : flowerSeriesIndex P p N kind pat ζ n n') : ℂ :=
  flowerPolynomialK P F p N kind pat dagger ζ t s n n' M
    (fun j => cutChoiceTail (e j)) (fun j => cutChoiceSmall (e j)) i *
    ∏ j, ((flowerPolynomialQ P p N kind pat ζ n n' M A (fun j => cutChoiceTail (e j)) i j).eval
      (cutChoicePoint (e j) : ℂ) -
      (flowerPolynomialQ P p N kind pat ζ n n' M A (fun j => cutChoiceTail (e j)) i j).eval 0)

theorem flowerSeriesTerm_weight
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (i : flowerSeriesIndex P p N kind pat ζ n n') :
    flowerSeriesTerm P F p N kind pat dagger ζ t s n n' weight i =
      (weight i.1.1 (cosetDecoration i.1.1.garden P.L 0 i.2.1) : ℂ) *
        flowerSeriesTerm P F p N kind pat dagger ζ t s n n' (fun _ _ => 1) i := by
  unfold flowerSeriesTerm kernelGenFactor
  push_cast
  ring

theorem flowerPolynomialQ_global_degree (M A : ℝ) (tail : Fin w → Bool)
    (i : flowerSeriesIndex P p N kind pat ζ n n') (j : Fin w) :
    (flowerPolynomialQ P p N kind pat ζ n n' M A tail i j).natDegree ≤ 2 * N + 1 := by
  have hj : (i.1.1.garden.tree j).order ≤ i.1.1.garden.order :=
    single_le_sum (f := fun j => (i.1.1.garden.tree j).order) (fun _ _ => Nat.zero_le _) (mem_univ j)
  have ho := i.1.2.2.2.1
  exact (treeLeafPolynomial_degree _ _ _ _ _ _ _).trans ((freeTreeLeaves_card_le _ j).trans (by omega))

theorem flowerSeries_cut_extraction (r : ℕ) (A : ℝ) (hL : 0 < P.L) (hA : 0 < A)
    (hscale : ((2 * N + 1 : ℕ) : ℝ) * A ≤ (2 ^ (r + 1) * P.L) / 4)
    (i : flowerSeriesIndex P p N kind pat ζ n n') :
    flowerSeriesTerm P F p N kind pat dagger ζ t s n n'
      (fun LG k => LG.cutWeight1P p P.L (r + 1) k) i =
      ∑ e : Fin w → Fin 3, (∏ j, (cutChoiceSign (e j) : ℂ)) *
        flowerExtractedTerm P F p N kind pat dagger ζ t s n n' (2 ^ (r + 1) * P.L) A e i := by
  let k := cosetDecoration i.1.1.garden P.L 0 i.2.1
  have hcard (j : Fin w) : (freeTreeLeaves i.1.1 j).card ≤ 2 * N + 1 := by
    have hj : (i.1.1.garden.tree j).order ≤ i.1.1.garden.order :=
      single_le_sum (f := fun j => (i.1.1.garden.tree j).order) (fun _ _ => Nat.zero_le _) (mem_univ j)
    have ho := i.1.2.2.2.1
    exact (freeTreeLeaves_card_le _ j).trans (by omega)
  have he := native_garden_extraction P i.1.1 p i.1.2.1 r A hL hA k
    (RegAsymp.isDecoration_coset i.2.2.1 P.L 0)
    (fun j => (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard j) hA.le).trans hscale)
  rw [flowerSeriesTerm_weight, he, sum_mul]
  apply sum_congr rfl
  intro e _
  unfold flowerExtractedTerm flowerPolynomialK
  conv_rhs => rw [flowerSeriesTerm_weight]
  dsimp only [flowerPolynomialQ, k]
  ring

end WaveTurbulence.FC23
