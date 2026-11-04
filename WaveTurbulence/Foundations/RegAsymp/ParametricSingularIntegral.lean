/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.ParametricFourierAmplitude

/-! # Measurability of singular integrals for a fixed spatial cell box

The source singular operator is represented by a finite sum of ordinary
Fourier integrals. The cell box is fixed before the parameter varies.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT

/-- The cell multipliers are jointly measurable in the full Fourier array. -/
theorem stronglyMeasurable_cellOp_array {d n : ℕ} (hd : 3 ≤ d) (J : Finset (Fin n))
    (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    StronglyMeasurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)) := by
  classical
  apply Finset.stronglyMeasurable_fun_prod
  intro j _
  have hm : Measurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => (τ.1 j,τ.2 j)) :=
    ((measurable_pi_apply j).comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)
  have hbase := stronglyMeasurable_cellOp hd J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2)
  have hcomp := hbase.comp_measurable hm
  change StronglyMeasurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
    cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j))
  exact hcomp

/-- A jointly measurable amplitude family with Fourier inversion and
common triangular support has a measurable actual singular integral. -/
theorem stronglyMeasurable_singInt_fixed_support {P : Type*} [MeasurableSpace P]
    {d n : ℕ} (hd : 3 ≤ d) (J : Finset (Fin n))
    {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    {a b : Fin n → Mom d} {lam : Fin n → ℝ}
    {W : P → (Fin n → Mom d) → (Fin n → Mom d) → ℂ}
    (hW : StronglyMeasurable (fun p : P × ((Fin n → Mom d) × (Fin n → Mom d)) => W p.1 p.2.1 p.2.2))
    (hWs : ∀ p x y, W p x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam)
    (hF : ∀ p, Integrable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) => fourierW (W p) τ.1 τ.2))
    (hinv : ∀ p x y, W p x y = ∫ τ, fourierW (W p) τ.1 τ.2*wPhase x y τ) :
    StronglyMeasurable (fun p => singInt J (W p)) := by
  classical
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  let Q := (cellBox_finite hxs hys a b lam).toFinset
  have he (p : P) : singInt J (W p) = ∑ pq ∈ Q,
      ∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW (W p) τ.1 τ.2 *
        ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j) :=
    singInt_eq hd J Q (hF p) (W_eq_sum_appFac hxs hys (hWs p) (hinv p) J)
  simp_rw [he]
  apply Finset.stronglyMeasurable_fun_sum
  intro pq _
  have hc := stronglyMeasurable_cellOp_array hd J pq
  exact ((stronglyMeasurable_fourierW_parameter hW).mul (hc.comp_measurable measurable_snd)).integral_prod_right'

end WaveTurbulence.RegAsymp
