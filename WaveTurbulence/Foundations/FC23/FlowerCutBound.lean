/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerExtraction
/-! Conditional cut1 bounds from the actual unsliced FC3 family. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset Polynomial
variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

/-- The complete local FC2 bound. All convergence, carrier and auxiliary-cutoff
identities are derived; the sole analytic family bound is FC23UniformFlowerFamily. -/
theorem cut1_bound_of_uniformFlowerFamily (r : ℕ) (A ρ B : ℝ)
    (hL : 0 < P.L) (hA : 0 < A) (hρ : 1 ≤ ρ) (hB : 0 ≤ B)
    (hscale : ((2 * N + 1 : ℕ) : ℝ) * A ≤ (2 ^ (r + 1) * P.L) / 4)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (H : FC23UniformFlowerFamily P F p N kind pat dagger ζ t s n n'
      (2 ^ (r + 1) * P.L) A (fun _ => ρ) B) :
    ‖flowerSumP P F p N kind pat dagger (some (r + 1)) none ζ t s n n'‖ ≤
      (3 : ℝ) ^ w * (4 * Real.exp 1) ^ (w * (2 * N + 1)) *
        (((2 * N + 1 : ℕ) : ℝ) / ρ) ^ w * B := by
  let E := flowerExtractedTerm P F p N kind pat dagger ζ t s n n' (2 ^ (r + 1) * P.L) A
  let c (e : Fin w → Fin 3) : ℂ := ∏ j, (cutChoiceSign (e j) : ℂ)
  have hs (e : Fin w → Fin 3) : Summable (E e) :=
    flowerExtractedTerm_summable P F p N kind pat dagger ζ t s n n' _ A ρ B hρ hF H e
  have hc (e : Fin w → Fin 3) : ‖c e‖ = 1 := by
    dsimp only [c]
    rw [norm_prod]
    apply prod_eq_one
    intro j _
    unfold cutChoiceSign
    split_ifs <;> norm_num
  have ht := flowerSeries_cut_extraction P F p N kind pat dagger ζ t s n n' r A hL hA hscale
  have hall : Summable (flowerSeriesTerm P F p N kind pat dagger ζ t s n n'
      (fun LG k => LG.cutWeight1P p P.L (r + 1) k)) := by
    apply (summable_sum (fun e (_ : e ∈ univ) => (hs e).mul_left (c e))).congr
    intro i
    exact (ht i).symm
  rw [← flowerWeighted_cut1, flowerWeighted_eq_series P F p N kind pat dagger ζ t s n n' _
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
      exact flowerExtractedTerm_bound P F p N kind pat dagger ζ t s n n' _ A ρ B hρ hB hF H e
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]; ring

/-- The j1=0 endpoint follows directly from the same family interface. -/
theorem cut1_zero_bound_of_uniformFlowerFamily (A ρ B : ℝ) (hρ : 1 ≤ ρ)
    (H : FC23UniformFlowerFamily P F p N kind pat dagger ζ t s n n' P.L A (fun _ => ρ) B) :
    ‖flowerSumP P F p N kind pat dagger (some 0) none ζ t s n n'‖ ≤ B := by
  have he : flowerWeighted P F p N kind pat dagger
      (fun LG k => LG.cutWeight1P p P.L 0 k) ζ t s n n' =
      flowerWeighted P F p N kind pat dagger
      (fun LG k => flowerFamilyWeight LG p P.L A (fun _ => false) (fun _ => false) (fun _ => 1) k)
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
  rw [← flowerWeighted_cut1, he]
  exact H (fun _ => false) (fun _ => false) (fun _ => 1) (fun _ => ⟨zero_le_one, hρ⟩)
end WaveTurbulence.FC23
