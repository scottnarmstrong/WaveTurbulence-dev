/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeHalfCellCountableMass
public import WaveTurbulence.Foundations.RegAsymp.CountableCellSingularRepresentation

/-! # Original ordinary-cell factors and lawful countable singular recombination -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT

variable {I U : Type*} [MeasurableSpace U] {d n : ℕ}

/-- The original physical ordinary-cell factors in each actual source half cell. -/
def treeHalfCellOrdinaryFn (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (i : TreeHalfCellOrdinaryIndex z) (τ : (Fin n → Mom d) × (Fin n → Mom d))
    (x y : Fin n → Mom d) : ℂ :=
  ∏ j, cellFn (NTSP.intVec (i.2.val j).1) (NTSP.intVec (i.2.val j).2)
    (τ.1 j) (τ.2 j) (x j) (y j)

/-- The original ordinary factors after every singular pair integration. -/
def treeHalfCellOrdinaryOp (J : Finset (Fin n))
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (i : TreeHalfCellOrdinaryIndex z) (τ : (Fin n → Mom d) × (Fin n → Mom d)) : ℂ :=
  ∏ j, cellOp J j (NTSP.intVec (i.2.val j).1) (NTSP.intVec (i.2.val j).2) (τ.1 j) (τ.2 j)

theorem norm_treeHalfCellOrdinaryFn_le_one (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (i : TreeHalfCellOrdinaryIndex z) (τ : (Fin n → Mom d) × (Fin n → Mom d))
    (x y : Fin n → Mom d) : ‖treeHalfCellOrdinaryFn z i τ x y‖ ≤ 1 := by
  rw [treeHalfCellOrdinaryFn,norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_cellFn_le _ _ _ _ _ _)

theorem stronglyMeasurable_treeHalfCellOrdinaryFn
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (i : TreeHalfCellOrdinaryIndex z) (x y : Fin n → Mom d) :
    StronglyMeasurable (fun τ => treeHalfCellOrdinaryFn z i τ x y) := by
  apply Continuous.stronglyMeasurable
  unfold treeHalfCellOrdinaryFn
  apply continuous_finsetProd
  intro j _
  exact (continuous_cellFn_all _ _).comp
    (f := fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      (((τ.1 j),(τ.2 j)),((x j),(y j)))) (by fun_prop)

theorem norm_treeHalfCellOrdinaryOp_le (J : Finset (Fin n)) {M : ℝ}
    (hb : ∀ (j : Fin n) (p q ξ η : Mom d), ‖cellOp J j p q ξ η‖ ≤ M)
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (i : TreeHalfCellOrdinaryIndex z) (τ : (Fin n → Mom d) × (Fin n → Mom d)) :
    ‖treeHalfCellOrdinaryOp J z i τ‖ ≤ M^n := by
  rw [treeHalfCellOrdinaryOp,norm_prod]
  apply (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hb j _ _ _ _)).trans_eq
  simp

theorem stronglyMeasurable_treeHalfCellOrdinaryOp (hd : 3 ≤ d) (J : Finset (Fin n))
    (z : I → (Fin n × Fin 2) → Fin d → ℤ) (i : TreeHalfCellOrdinaryIndex z) :
    StronglyMeasurable (treeHalfCellOrdinaryOp J z i) :=
  stronglyMeasurable_cellOp_array hd J i.2.val

/-- The countable kernel uses exactly the actual joint half-cell Fourier coefficients. -/
def treeHalfCellCountableKernel (μ : Measure U)
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (a : I → U → ℂ) (x y : Fin n → Mom d) : ℂ :=
  ∑' i : TreeHalfCellOrdinaryIndex z,
    ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
      treeHalfCellCountableCoefficient z β γ a i p*treeHalfCellOrdinaryFn z i p.2 x y ∂μ.prod volume

/-- Original first-moment masses justify all actual singular integrations through the
countable half-cell Fourier representation. -/
theorem singInt_treeHalfCellCountableKernel_eq [Countable I] (μ : Measure U) [SFinite μ]
    (hd : 3 ≤ d) (hn : 0 < n) (J : Finset (Fin n))
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
    (a : I → U → ℂ) (ha : ∀ c, StronglyMeasurable (a c))
    (hi : ∀ c, Integrable (fun u => ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ)
    (hs : Summable (fun c => ∫ u, ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖))) ∂μ)) :
    singInt J (treeHalfCellCountableKernel μ z β γ a) =
      ∑' i : TreeHalfCellOrdinaryIndex z,
        ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
          treeHalfCellCountableCoefficient z β γ a i p*treeHalfCellOrdinaryOp J z i p.2 ∂μ.prod volume := by
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  exact singInt_countableCellMixture (d := d) (n := n)
    (I := TreeHalfCellOrdinaryIndex z)
    (U := U × ((Fin n → Mom d) × (Fin n → Mom d))) (μ.prod volume) hd J
    (fun i j => NTSP.intVec (i.2.val j).1) (fun i j => NTSP.intVec (i.2.val j).2)
    (fun _ p => p.2.1) (fun _ p => p.2.2) (fun _ => measurable_snd.fst) (fun _ => measurable_snd.snd)
    (treeHalfCellCountableCoefficient z β γ a)
    (stronglyMeasurable_treeHalfCellCountableCoefficient z β γ hβ hγ a ha)
    (integrable_treeHalfCellCountableCoefficient μ hn z β γ hβ hγ a ha hi)
    (summable_integral_norm_treeHalfCellCountableCoefficient μ hn z β γ hβ hγ a ha hi hs)

end WaveTurbulence.RA1Leafwise
