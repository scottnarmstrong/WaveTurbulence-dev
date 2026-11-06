/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Assembly1
/-! # The spliced kernel is bounded by the number of classes times the product of ladder bounds (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset MeasureTheory Set
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The class of a decoration: its bond labels off the internal darts of the ladders. -/
noncomputable def kappa (S : ι → Finset (GBranch G.tree)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) : GardenDart G → (Fin d → ℤ) :=
  fun x => if IntDart S x then 0 else bondIndex G z.1 x

omit [Fintype ι] [DecidableEq ι] in
lemma kappa_eq_iff (S : ι → Finset (GBranch G.tree)) {roots : Fin w → (Fin d → ℤ)}
    (z z' : GenDecoration G d roots 0) : kappa S z = kappa S z' ↔ AgreeOff S z z' := by
  constructor
  · intro h x hx
    have := congrFun h x
    simpa [kappa, hx] using this
  · intro h
    funext x
    by_cases hx : IntDart S x
    · simp [kappa, hx]
    · simp [kappa, hx, h x hx]

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_Lam (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (L γ η δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (z₀ : GenDecoration G d roots 0)
    (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1))) (i : ι) :
    Continuous (Lam D S L γ η δ base z₀ T i) := by
  unfold Lam
  refine continuous_finsetSum _ (fun ζ _ => continuous_const.mul ?_)
  exact continuous_ladderPhase D (S i) L γ δ base ζ.1.1

/-- Pointwise (in the times) bound of the fibre sums by the product of the local lattice sums. -/
theorem fibre_norm_le (hP : G.IsPlain) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (S : ι → Finset (GBranch G.tree))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (hH : ∀ i, Disjoint (S i) D.hinges)
    {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z₀ : GenDecoration G d roots 0) (Zc : Finset (GenDecoration G d roots 0))
    (hZ : ∀ z, AgreeOff S z z₀ → splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 → z ∈ Zc)
    (hZ' : ∀ z ∈ Zc, AgreeOff S z z₀)
    (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1)))
    (hT : ∀ i ζ, ζ ∉ T i → ladderWeight D (S i) L γ η base ζ.1.1 = 0)
    (t : GBranch G.tree → ℝ) :
    ‖∑ z ∈ Zc, splicedMomentumAmplitude G D L γ η base z.1 * globalPhase D L γ δ base z.1 t‖ ≤
      ∏ i, ‖Lam D S L γ η δ base z₀ T i (fun v : S i => t v.1)‖ := by
  rw [fibre_factor hP D S hS hH hL.ne' γ η δ base roots z₀ Zc hZ hZ' T hT t, norm_mul, norm_mul]
  have h1 : ‖restAmp D S L γ η base z₀.1‖ ≤ 1 := norm_restAmp_le_one D hD S L γ η base z₀.1
  have h2 : ‖∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z₀.1 v * t v : ℝ) *
      Complex.I)‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one (fun v _ => Complex.norm_exp_ofReal_mul_I _)
  rw [h2, mul_one, norm_prod]
  exact mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) h1

end WaveTurbulence.CoarseSpliced
