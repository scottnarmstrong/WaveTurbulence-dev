/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFourierMixture
public import WaveTurbulence.Foundations.RegAsymp.FiniteCellSingularFubini

/-! # Actual half-cell singular integration commutes with the leaf parameter integral -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset

/-- No growing full-kernel derivative assumption is needed to exchange
actual singular integration with the parameter integral of half-cells. -/
theorem singInt_integral_halfCellAmplitude {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    (J : Finset (Fin n)) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
    (a : U → ℂ) (ha : StronglyMeasurable a)
    (hi : Integrable (fun u => ‖a u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ) :
    singInt J (fun x y => ∫ u, a u*halfCellAmplitude z (β u) (γ u) x y ∂μ) =
      ∫ u, a u*singInt J (halfCellAmplitude z (β u) (γ u)) ∂μ := by
  classical
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  have hm := stronglyMeasurable_halfCellFourierMixture z β γ hβ hγ a ha
  have hf := (halfCellFourierMixture_integrable_mass μ hn z β γ hβ hγ a ha hi).1
  have h0 (u : U) (x y : Fin n → Mom d) :
      a u*halfCellAmplitude z (β u) (γ u) x y =
      ∑ pq : halfCellOrdinaryCells z, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        (a u*fourierW (halfCellAmplitude z (β u) (γ u)) τ.1 τ.2)*
          ∏ j, cellFn (NTSP.intVec (pq.val j).1) (NTSP.intVec (pq.val j).2)
            (τ.1 j) (τ.2 j) (x j) (y j) := by
    let f := fun pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
      ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        (a u*fourierW (halfCellAmplitude z (β u) (γ u)) τ.1 τ.2)*
          ∏ j, cellFn (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2)
            (τ.1 j) (τ.2 j) (x j) (y j)
    change a u*halfCellAmplitude z (β u) (γ u) x y = ∑ pq : halfCellOrdinaryCells z, f pq.val
    rw [sum_coe_sort,halfCellAmplitude_eq_sum_cellFn hn,mul_sum]
    dsimp only [f]
    apply sum_congr rfl
    intro pq _
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro τ
    dsimp only
    ring
  have h1 (u : U) : a u*singInt J (halfCellAmplitude z (β u) (γ u)) =
      ∑ pq : halfCellOrdinaryCells z, ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        (a u*fourierW (halfCellAmplitude z (β u) (γ u)) τ.1 τ.2)*
          ∏ j, cellOp J j (NTSP.intVec (pq.val j).1) (NTSP.intVec (pq.val j).2)
            (τ.1 j) (τ.2 j) := by
    let f := fun pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
      ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
        (a u*fourierW (halfCellAmplitude z (β u) (γ u)) τ.1 τ.2)*
          ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)
    change a u*singInt J (halfCellAmplitude z (β u) (γ u)) = ∑ pq : halfCellOrdinaryCells z, f pq.val
    rw [sum_coe_sort,singInt_halfCellAmplitude_eq hd hn,mul_sum]
    dsimp only [f]
    apply sum_congr rfl
    intro pq _
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro τ
    dsimp only
    ring
  have hh := singInt_integral_finiteCellMixture μ volume hd J
    (fun pq : halfCellOrdinaryCells z => fun j => NTSP.intVec (pq.val j).1)
    (fun pq : halfCellOrdinaryCells z => fun j => NTSP.intVec (pq.val j).2)
    (fun _pq => fun uv : U × ((Fin n → Mom d) × (Fin n → Mom d)) => uv.2.1)
    (fun _pq => fun uv : U × ((Fin n → Mom d) × (Fin n → Mom d)) => uv.2.2)
    (fun _ => measurable_snd.fst) (fun _ => measurable_snd.snd)
    (fun _pq => fun uv : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      a uv.1*fourierW (halfCellAmplitude z (β uv.1) (γ uv.1)) uv.2.1 uv.2.2)
    (fun _ => hm) (fun _ => hf)
  have hleft : (fun (x y : Fin n → Mom d) => ∫ u,
      a u*halfCellAmplitude z (β u) (γ u) x y ∂μ) =
      (fun x y => ∫ u, ∑ pq : halfCellOrdinaryCells z,
        ∫ τ : (Fin n → Mom d) × (Fin n → Mom d),
          (a u*fourierW (halfCellAmplitude z (β u) (γ u)) τ.1 τ.2)*
            ∏ j, cellFn (NTSP.intVec (pq.val j).1) (NTSP.intVec (pq.val j).2)
              (τ.1 j) (τ.2 j) (x j) (y j) ∂volume ∂μ) := by
    funext x y
    exact integral_congr_ae (ae_of_all _ (fun u => h0 u x y))
  rw [hleft,hh]
  exact integral_congr_ae (ae_of_all _ (fun u => (h1 u).symm))

end WaveTurbulence.RegAsymp
