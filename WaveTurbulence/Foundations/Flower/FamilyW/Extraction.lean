/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FamilyW.Family
/-! The `W`-weighted extraction: Lemma-level generalization of main's `FC23.FlowerExtraction` and
`FC23.FlowerCutBound` (cut1 bounds for `W · cutWeight1P`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FamilyW
open Finset Polynomial GraftGen WaveTurbulence.FC23

variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)

def flowerExtractedTermW (M A : ℝ) (e : Fin w → Fin 3)
    (i : flowerSeriesIndex P p N kind pat ζ n n') : ℂ :=
  flowerPolynomialKW P F p N kind pat dagger ζ t s n n' W M
    (fun j => cutChoiceTail (e j)) (fun j => cutChoiceSmall (e j)) i *
    ∏ j, ((flowerPolynomialQ P p N kind pat ζ n n' M A (fun j => cutChoiceTail (e j)) i j).eval
      (cutChoicePoint (e j) : ℂ) -
      (flowerPolynomialQ P p N kind pat ζ n n' M A (fun j => cutChoiceTail (e j)) i j).eval 0)

theorem flowerSeries_cut_extractionW (r : ℕ) (A : ℝ) (hL : 0 < P.L) (hA : 0 < A)
    (hscale : ((2 * N + 1 : ℕ) : ℝ) * A ≤ (2 ^ (r + 1) * P.L) / 4)
    (i : flowerSeriesIndex P p N kind pat ζ n n') :
    flowerSeriesTerm P F p N kind pat dagger ζ t s n n'
      (fun LG k => W LG k * LG.cutWeight1P p P.L (r + 1) k) i =
      ∑ e : Fin w → Fin 3, (∏ j, (cutChoiceSign (e j) : ℂ)) *
        flowerExtractedTermW P F p N kind pat dagger ζ t s n n' W (2 ^ (r + 1) * P.L) A e i := by
  rw [flowerSeriesTerm_mul P F p N kind pat dagger ζ t s n n' W
    (fun LG k => LG.cutWeight1P p P.L (r + 1) k) i,
    flowerSeries_cut_extraction P F p N kind pat dagger ζ t s n n' r A hL hA hscale i, mul_sum]
  apply sum_congr rfl
  intro e _
  unfold flowerExtractedTermW flowerExtractedTerm flowerPolynomialKW
  ring

theorem flowerExtractedTermW_summable (M A ρ B : ℝ) (hρ : 1 ≤ ρ)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (hW : ∀ LG k, |W LG k| ≤ 1)
    (H : UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' W M A (fun _ => ρ) B)
    (e : Fin w → Fin 3) :
    Summable (flowerExtractedTermW P F p N kind pat dagger ζ t s n n' W M A e) :=
  tensor_extraction_summable _ _ (fun _ => 2 * N + 1) (fun _ => by omega)
    (flowerPolynomialQ_global_degree P p N kind pat ζ n n' M A _) (fun _ => ρ)
    (fun _ => lt_of_lt_of_le zero_lt_one hρ) _ _
    (uniformFlowerFamilyW_evaluationBox P F p N kind pat dagger ζ t s n n' W hW M A
      (fun _ => ρ) B hF H _ _)

theorem flowerExtractedTermW_bound (M A ρ B : ℝ) (hρ : 1 ≤ ρ) (hB : 0 ≤ B)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (hW : ∀ LG k, |W LG k| ≤ 1)
    (H : UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' W M A (fun _ => ρ) B)
    (e : Fin w → Fin 3) :
    ‖∑' i, flowerExtractedTermW P F p N kind pat dagger ζ t s n n' W M A e i‖ ≤
      (4 * Real.exp 1) ^ (w * (2 * N + 1)) * (((2 * N + 1 : ℕ) : ℝ) / ρ) ^ w * B := by
  apply tensor_common_degree_gain _ _ (by omega)
    (flowerPolynomialQ_global_degree P p N kind pat ζ n n' M A _) hρ _ _ hB
    (uniformFlowerFamilyW_evaluationBox P F p N kind pat dagger ζ t s n n' W hW M A
      (fun _ => ρ) B hF H _ _)
  intro j
  unfold cutChoicePoint
  split_ifs <;> norm_num

theorem cut1_bound_of_familyW (r : ℕ) (A ρ B : ℝ)
    (hL : 0 < P.L) (hA : 0 < A) (hρ : 1 ≤ ρ) (hB : 0 ≤ B)
    (hscale : ((2 * N + 1 : ℕ) : ℝ) * A ≤ (2 ^ (r + 1) * P.L) / 4)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (hW : ∀ LG k, |W LG k| ≤ 1)
    (H : UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' W
      (2 ^ (r + 1) * P.L) A (fun _ => ρ) B) :
    ‖flowerWeighted P F p N kind pat dagger
        (fun LG k => W LG k * LG.cutWeight1P p P.L (r + 1) k) ζ t s n n'‖ ≤
      (3 : ℝ) ^ w * (4 * Real.exp 1) ^ (w * (2 * N + 1)) *
        (((2 * N + 1 : ℕ) : ℝ) / ρ) ^ w * B := by
  let E := flowerExtractedTermW P F p N kind pat dagger ζ t s n n' W (2 ^ (r + 1) * P.L) A
  let c (e : Fin w → Fin 3) : ℂ := ∏ j, (cutChoiceSign (e j) : ℂ)
  have hs (e : Fin w → Fin 3) : Summable (E e) :=
    flowerExtractedTermW_summable P F p N kind pat dagger ζ t s n n' W _ A ρ B hρ hF hW H e
  have hc (e : Fin w → Fin 3) : ‖c e‖ = 1 := by
    dsimp only [c]
    rw [norm_prod]
    apply prod_eq_one
    intro j _
    unfold cutChoiceSign
    split_ifs <;> norm_num
  have ht := flowerSeries_cut_extractionW P F p N kind pat dagger ζ t s n n' W r A hL hA hscale
  have hall : Summable (flowerSeriesTerm P F p N kind pat dagger ζ t s n n'
      (fun LG k => W LG k * LG.cutWeight1P p P.L (r + 1) k)) := by
    apply (summable_sum (fun e (_ : e ∈ univ) => (hs e).mul_left (c e))).congr
    intro i
    exact (ht i).symm
  rw [flowerWeighted_eq_series P F p N kind pat dagger ζ t s n n' _
    (fun LG => hall.sigma_factor LG)]
  simp_rw [ht]
  rw [Summable.tsum_finsetSum (fun e _ => (hs e).mul_left (c e))]
  simp only [tsum_mul_left]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _e : Fin w → Fin 3,
        (4 * Real.exp 1) ^ (w * (2 * N + 1)) * (((2 * N + 1 : ℕ) : ℝ) / ρ) ^ w * B := by
      apply sum_le_sum
      intro e _
      rw [norm_mul, hc e, one_mul]
      exact flowerExtractedTermW_bound P F p N kind pat dagger ζ t s n n' W _ A ρ B hρ hB hF hW H e
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]; ring

/-- The `j1 = 0` endpoint of the `W`-weighted family. -/
theorem cut1_zero_bound_of_familyW (A ρ B : ℝ) (hρ : 1 ≤ ρ)
    (H : UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' W P.L A (fun _ => ρ) B) :
    ‖flowerWeighted P F p N kind pat dagger
        (fun LG k => W LG k * LG.cutWeight1P p P.L 0 k) ζ t s n n'‖ ≤ B := by
  have he : flowerWeighted P F p N kind pat dagger
      (fun LG k => W LG k * LG.cutWeight1P p P.L 0 k) ζ t s n n' =
      flowerWeighted P F p N kind pat dagger
      (fun LG k => W LG k *
        flowerFamilyWeight LG p P.L A (fun _ => false) (fun _ => false) (fun _ => 1) k)
      ζ t s n n' := by
    rw [flowerWeighted_eq_sum, flowerWeighted_eq_sum]
    apply sum_congr rfl
    intro LG hLG
    have hc := ((flowerCarrier_finite P p N kind pat ζ).mem_toFinset.mp hLG).1
    unfold flowerKernel
    congr 1
    funext k
    dsimp only
    rw [native_garden_zero P LG p hc A k]
  rw [he]
  exact H (fun _ => false) (fun _ => false) (fun _ => 1) (fun _ => ⟨zero_le_one, hρ⟩)
end WaveTurbulence.Flower.FamilyW
