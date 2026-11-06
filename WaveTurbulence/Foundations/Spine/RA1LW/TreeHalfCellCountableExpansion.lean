/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeHalfCellCountableOutput
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellSingularFubini

/-! # Exact finite ordinary-cell expansion inside each original countable half cell -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset

variable {I U : Type*} [MeasurableSpace U] (μ : Measure U) [SFinite μ] {d n : ℕ}
  (hn : 0 < n) (z : I → (Fin n × Fin 2) → Fin d → ℤ)
  (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
  (a : I → U → ℂ) (ha : ∀ c, StronglyMeasurable (a c))
  (hi : ∀ c, Integrable (fun u => ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ)
  (hs : Summable (fun c => ∫ u, ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖))) ∂μ))

include hn hβ hγ ha hi hs

/-- The actual parameter integral of one source half cell is its finite ordinary-cell
Fourier representation. Joint L1 is derived from the original first modulation moments. -/
theorem tree_halfCell_integral_eq_ordinary_cells (c : I) (x y : Fin n → Mom d) :
    (∫ u, a c u*halfCellAmplitude (z c) (β u) (γ u) x y ∂μ) =
      ∑ pq : halfCellOrdinaryCells (z c),
        ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
          treeHalfCellCountableCoefficient z β γ a ⟨c,pq⟩ p*
            treeHalfCellOrdinaryFn z ⟨c,pq⟩ p.2 x y ∂μ.prod volume := by
  classical
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  have hF := (tree_halfCell_countableFn_integrable_summable μ hn z β γ hβ hγ a ha hi hs x y).1
  have he := integral_fintype_integral_eq_tsum_integral_prod μ volume
    (fun pq : halfCellOrdinaryCells (z c) =>
      fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
        treeHalfCellCountableCoefficient z β γ a ⟨c,pq⟩ p*treeHalfCellOrdinaryFn z ⟨c,pq⟩ p.2 x y)
    (fun pq => hF ⟨c,pq⟩)
  rw [tsum_fintype] at he
  apply Eq.trans ?_ he
  apply integral_congr_ae
  apply ae_of_all
  intro u
  dsimp only
  let f := fun pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
      (a c u*fourierW (halfCellAmplitude (z c) (β u) (γ u)) τ.1 τ.2)*
        ∏ j, cellFn (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2)
          (τ.1 j) (τ.2 j) (x j) (y j)
  change a c u*halfCellAmplitude (z c) (β u) (γ u) x y =
    ∑ pq : halfCellOrdinaryCells (z c), f pq.val
  rw [sum_coe_sort,halfCellAmplitude_eq_sum_cellFn hn,mul_sum]
  dsimp only [f]
  apply sum_congr rfl
  intro pq _
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => by ring)

/-- Recombining every ordinary singular output of one half cell is exactly its actual
singular parameter integral; no singular convergence or arbitrary PV linearity is assumed. -/
theorem tree_halfCell_ordinary_ops_eq_integral (hd : 3 ≤ d) (J : Finset (Fin n)) (c : I) :
    (∑ pq : halfCellOrdinaryCells (z c),
      ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
        treeHalfCellCountableCoefficient z β γ a ⟨c,pq⟩ p*treeHalfCellOrdinaryOp J z ⟨c,pq⟩ p.2
          ∂μ.prod volume) =
      ∫ u, a c u*singInt J (halfCellAmplitude (z c) (β u) (γ u)) ∂μ := by
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  have hh := singInt_countableCellMixture (d := d) (n := n)
    (I := halfCellOrdinaryCells (z c))
    (U := U × ((Fin n → Mom d) × (Fin n → Mom d))) (μ.prod volume) hd J
    (fun pq j => NTSP.intVec (pq.val j).1) (fun pq j => NTSP.intVec (pq.val j).2)
    (fun _ p => p.2.1) (fun _ p => p.2.2) (fun _ => measurable_snd.fst) (fun _ => measurable_snd.snd)
    (fun pq => treeHalfCellCountableCoefficient z β γ a ⟨c,pq⟩)
    (fun pq => stronglyMeasurable_treeHalfCellCountableCoefficient z β γ hβ hγ a ha ⟨c,pq⟩)
    (fun pq => integrable_treeHalfCellCountableCoefficient μ hn z β γ hβ hγ a ha hi ⟨c,pq⟩)
    ((hasSum_fintype (fun pq : halfCellOrdinaryCells (z c) =>
      ∫ p, ‖treeHalfCellCountableCoefficient z β γ a ⟨c,pq⟩ p‖ ∂μ.prod volume)).summable)
  change singInt J (fun x y => ∑' pq : halfCellOrdinaryCells (z c),
    ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
      treeHalfCellCountableCoefficient z β γ a ⟨c,pq⟩ p*treeHalfCellOrdinaryFn z ⟨c,pq⟩ p.2 x y ∂μ.prod volume) =
    ∑' pq : halfCellOrdinaryCells (z c),
      ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
        treeHalfCellCountableCoefficient z β γ a ⟨c,pq⟩ p*treeHalfCellOrdinaryOp J z ⟨c,pq⟩ p.2 ∂μ.prod volume at hh
  have hk : (fun x y => ∑' pq : halfCellOrdinaryCells (z c),
      ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
        treeHalfCellCountableCoefficient z β γ a ⟨c,pq⟩ p*treeHalfCellOrdinaryFn z ⟨c,pq⟩ p.2 x y ∂μ.prod volume) =
      (fun x y => ∫ u, a c u*halfCellAmplitude (z c) (β u) (γ u) x y ∂μ) := by
    funext x y
    rw [tsum_fintype]
    exact (tree_halfCell_integral_eq_ordinary_cells μ hn z β γ hβ hγ a ha hi hs c x y).symm
  rw [hk,tsum_fintype] at hh
  exact hh.symm.trans (singInt_integral_halfCellAmplitude μ hd hn J (z c) β γ hβ hγ (a c) (ha c) (hi c))

end WaveTurbulence.RA1Leafwise
