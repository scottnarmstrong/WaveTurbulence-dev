/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FamilyW.Family
public import WaveTurbulence.Foundations.FlowerTop.FamilyWeightLimit
/-! The plain-clause limit `M = 2^j L → ∞` for the `W`-weighted family: generalizes
`FlowerTop.flowerWeighted_tendsto_one` and the limit step of `FlowerTop.flowerCasePlain_of_uniform`.
(`FC23.prefixP_small_moment` carries no weight and is used unchanged.) -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FamilyW
open Filter Topology Set WaveTurbulence.FC23 WaveTurbulence.FlowerTop

variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ)

theorem flowerWeighted_tendsto_W (hL : 0 < P.L)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (hW : ∀ LG k, |W LG k| ≤ 1) :
    Tendsto (fun j : ℕ => flowerWeighted P F p N kind pat dagger
      (fun LG k => W LG k *
        flowerFamilyWeight LG p (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
          (fun _ => false) (fun _ => false) (fun _ => 0) k) ζ t s n n') atTop
      (𝓝 (flowerWeighted P F p N kind pat dagger W ζ t s n n')) := by
  simp only [flowerWeighted_eq_sum]
  refine tendsto_finsetSum _ fun LG hLG => ?_
  have hLG' := (flowerCarrier_finite P p N kind pat ζ).mem_toFinset.mp hLG
  have hn : ∀ ℓ, LG.garden.mark ℓ ≠ some MarkTag.lower := by
    intro ℓ h
    have hm : LG.garden.mark ℓ ≠ none := by rw [h]; simp
    have := hLG'.1.1.2.1 ℓ hm
    rw [Garden.IsFlower] at this
    rw [h] at this
    exact absurd (Option.some.inj this) (by decide)
  have hg : ∀ k, |(dagger.elim 1 fun c => LG.sibWeight c k)| ≤ 1 := by
    intro k
    cases dagger with
    | none => simp
    | some c =>
      have := sibWeight_mem LG c k
      simp only [Option.elim]
      rw [abs_of_nonneg this.1]; exact this.2
  unfold flowerKernel
  refine kernelKgen_tendsto_wt P.L P.γ P.δ F LG _ _ _ 0 _ _ hn
    (fun q => by simpa only [zero_add] using hF q)
    (fun j k => (W LG k * flowerFamilyWeight LG p (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
        (fun _ => false) (fun _ => false) (fun _ => 0) k) * (dagger.elim 1 fun c => LG.sibWeight c k))
    (fun k => W LG k * (dagger.elim 1 fun c => LG.sibWeight c k)) ?_ ?_
  · intro j k
    have hm := family_weight_mem LG p (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ))) k
    rw [abs_mul, abs_mul, abs_of_nonneg hm.1]
    calc _ ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul (hW LG k) hm.2 hm.1 zero_le_one) (hg k) (abs_nonneg _)
            (by norm_num)
      _ = 1 := by norm_num
  · intro k
    exact tendsto_const_nhds.congr'
      ((family_weight_eventually_one LG p P.L hL N k).mono fun _ h => by simp only [h, mul_one])

/-- **Plain clause from the `W`-weighted family bound**, by letting `M = 2^j L → ∞`: if the family
bound `B` holds at `z = 0` for every dyadic scale, the unclipped `W`-weighted flower sum obeys `B`. -/
theorem plain_of_familyW (hL : 0 < P.L)
    (hF : ∀ q, Summable fun m : Fin P.d → ℤ => |F q (latticePoint P.L m)|)
    (hW : ∀ LG k, |W LG k| ≤ 1) (ρ : ℕ → Fin w → ℝ) (hρ : ∀ j i, 0 ≤ ρ j i) (B : ℝ)
    (H : ∀ j : ℕ, UniformFlowerFamilyW P F p N kind pat dagger ζ t s n n' W
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ))) (ρ j) B) :
    ‖flowerWeighted P F p N kind pat dagger W ζ t s n n'‖ ≤ B :=
  le_of_tendsto' ((continuous_norm.tendsto _).comp
    (flowerWeighted_tendsto_W P F p N kind pat dagger ζ t s n n' W hL hF hW)) fun j =>
    H j (fun _ => false) (fun _ => false) (fun _ => 0) (fun i => ⟨le_rfl, hρ j i⟩)
end WaveTurbulence.Flower.FamilyW
