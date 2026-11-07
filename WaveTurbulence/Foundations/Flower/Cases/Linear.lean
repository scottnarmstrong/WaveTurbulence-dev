/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FamilyW.Family
/-! # Linearity of `flowerWeighted` in a bounded weight. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Cases
open Finset GraftGen WaveTurbulence.FC23

variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

/-- The decoration series of a bounded weight is summable, carrier by carrier. -/
theorem summable_term_bounded
    (g : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hg : ∀ LG k, |g LG k| ≤ 1)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (LG : flowerCarrier P p N kind pat ζ) :
    Summable fun κ => flowerSeriesTerm P F p N kind pat dagger ζ t s n n' g ⟨LG, κ⟩ := by
  have key : Summable (kernelGenFactor P.L P.γ P.δ F LG.1 (LG.1.fixPat pat t s)
      (if dagger.isSome then univ.filter LG.1.garden.IsFlowerParent else ∅)
      (fun k => g LG.1 k * (dagger.elim 1 fun c => LG.1.sibWeight c k)) (fun _ => t) 0
      (n := fun _ => n) (nfl := n')) := by
    apply summable_kernelGenFactor_bounded (C := 1)
    · exact zero_le_one
    · intro k
      have hs : |(dagger.elim 1 fun c => LG.1.sibWeight c k)| ≤ 1 := by
        cases dagger with
        | none => norm_num
        | some c => exact sibWeight_abs_le LG.1 c k
      rw [abs_mul]
      calc _ ≤ 1 * 1 := mul_le_mul (hg LG.1 k) hs (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · intro l hl
      have he := LG.2.1.1.2.1 l (by rw [hl]; simp)
      change LG.1.garden.mark l = some MarkTag.equal at he
      rw [hl] at he
      cases he
    · simpa only [zero_add] using hF
  refine (key.mul_left ((coupling P.d P.L P.γ P.δ : ℂ) ^ LG.1.garden.order * LG.1.garden.zeta)).congr
    fun κ => ?_
  rfl

/-- `flowerWeighted` is linear in bounded weights. -/
theorem flowerWeighted_finset_sum {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (g : ι → ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hg : ∀ i LG k, |g i LG k| ≤ 1)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|) :
    flowerWeighted P F p N kind pat dagger (fun LG k => ∑ i ∈ S, c i * g i LG k) ζ t s n n' =
      ∑ i ∈ S, (c i : ℂ) * flowerWeighted P F p N kind pat dagger (g i) ζ t s n n' := by
  have hs (i : ι) := summable_term_bounded P F p N kind pat dagger ζ t s n n' (g i) (hg i) hF
  have hterm : ∀ i : flowerSeriesIndex P p N kind pat ζ n n',
      flowerSeriesTerm P F p N kind pat dagger ζ t s n n' (fun LG k => ∑ i ∈ S, c i * g i LG k) i =
        ∑ j ∈ S, (c j : ℂ) * flowerSeriesTerm P F p N kind pat dagger ζ t s n n' (g j) i := by
    intro i
    unfold flowerSeriesTerm kernelGenFactor
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsc : ∀ LG : flowerCarrier P p N kind pat ζ, Summable fun κ =>
      flowerSeriesTerm P F p N kind pat dagger ζ t s n n' (fun LG k => ∑ i ∈ S, c i * g i LG k) ⟨LG, κ⟩ := by
    intro LG
    exact (summable_sum fun j _ => (hs j LG).mul_left (c j : ℂ)).congr fun κ => (hterm ⟨LG, κ⟩).symm
  rw [flowerWeighted_eq_series P F p N kind pat dagger ζ t s n n' _ hsc]
  simp_rw [flowerWeighted_eq_series P F p N kind pat dagger ζ t s n n' _ (hs _)]
  simp_rw [hterm]
  have hall : ∀ j ∈ S, Summable fun i => (c j : ℂ) *
      flowerSeriesTerm P F p N kind pat dagger ζ t s n n' (g j) i := fun j _ =>
    (flowerSeries_summable P F p N kind pat dagger ζ t s n n' (g j) (hs j)).mul_left _
  rw [Summable.tsum_finsetSum hall]
  simp only [tsum_mul_left]

end WaveTurbulence.Flower.Cases
