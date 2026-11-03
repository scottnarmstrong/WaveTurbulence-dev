/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearBandWeight
public import WaveTurbulence.Foundations.WeylSums.FiniteBandCount

/-! # The bilinear lattice energy-band count -/

public section
open MeasureTheory Set Finset
namespace WaveTurbulence.WeylSums

/-- Radius-two momentum balls and one bilinear energy constraint. -/
@[expose] def bilinearBandSet {d : ℕ} (L : ℝ) (a b : Mom d) (β τ : ℝ) :
    Set ((Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | ‖latticePoint L q.1-a‖ ≤ 2 ∧ ‖latticePoint L q.2-b‖ ≤ 2 ∧
    |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-β| ≤ τ}

theorem finite_bilinearBandSet {d : ℕ} {L : ℝ} (hL : 0 < L) (a b : Mom d) (β τ : ℝ) :
    (bilinearBandSet L a b β τ).Finite := by
  apply (finite_bilinearBandWeight hL a b).subset
  intro q hq
  change bilinearBandWeight L a b q ≠ 0
  rw [bilinearBandWeight_eq_one L a b q hq.1 hq.2.1]
  exact one_ne_zero

/-- The band count is `O(τ L^(2d))` whenever its Fourier window lies below
`L²`. The real centers and the energy center are completely uniform. -/
theorem exists_bilinear_band_count_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ : ℝ, 2 ≤ L → 0 < τ → 1/τ ≤ L^2 →
      ∀ a b : Mom d, ∀ β : ℝ,
      ((bilinearBandSet L a b β τ).ncard : ℝ) ≤ C*τ*L^(2*(d : ℝ)) := by
  obtain ⟨C₀,hC₀,hcount⟩ := exists_finite_band_count_bound
  obtain ⟨C₁,hC₁,hint⟩ := exists_bilinearBandWeight_integral_bound d hd
  refine ⟨C₀*C₁,mul_pos hC₀ hC₁,?_⟩
  intro L τ hL hτ hwindow a b β
  classical
  have hLp : 0 < L := by linarith
  let w := bilinearBandWeight L a b
  let E := fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
    inner ℝ (latticePoint L q.1) (latticePoint L q.2)-β
  have hw := finite_bilinearBandWeight hLp a b
  have hS := finite_bilinearBandSet hLp a b β τ
  let I := hw.toFinset
  let S := hS.toFinset
  have hSI : S ⊆ I := by
    intro q hq
    have hq' := hS.mem_toFinset.mp hq
    apply hw.mem_toFinset.mpr
    change w q ≠ 0
    rw [show w q = 1 from bilinearBandWeight_eq_one L a b q hq'.1 hq'.2.1]
    exact one_ne_zero
  have hweight (q : (Fin d → ℤ) × (Fin d → ℤ)) (hq : q ∈ S) : 1 ≤ w q := by
    have hq' := hS.mem_toFinset.mp hq
    rw [show w q = 1 from bilinearBandWeight_eq_one L a b q hq'.1 hq'.2.1]
  have hband (q : (Fin d → ℤ) × (Fin d → ℤ)) (hq : q ∈ S) : |E q| ≤ τ :=
    (hS.mem_toFinset.mp hq).2.2
  have hc := hcount I S w E τ hτ hSI (fun q hq => bilinearBandWeight_nonneg L a b q) hweight hband
  have hfull (s : ℝ) : (∑' q : (Fin d → ℤ) × (Fin d → ℤ), (w q : ℂ)*
      e (s*inner ℝ (latticePoint L q.1) (latticePoint L q.2))) =
      ∑ q ∈ I, (w q : ℂ)*e (s*inner ℝ (latticePoint L q.1) (latticePoint L q.2)) := by
    apply tsum_eq_sum
    intro q hq
    have hz : w q = 0 := by
      by_contra hz
      exact hq (hw.mem_toFinset.mpr hz)
    simp [hz]
  have hnorm (s : ℝ) : ‖finiteEnergySum I w E s‖ =
      ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ), (w q : ℂ)*
        e (s*inner ℝ (latticePoint L q.1) (latticePoint L q.2))‖ := by
    have heq : finiteEnergySum I w E s = e (-s*β)*
        ∑' q : (Fin d → ℤ) × (Fin d → ℤ), (w q : ℂ)*
          e (s*inner ℝ (latticePoint L q.1) (latticePoint L q.2)) := by
      rw [hfull,mul_sum]
      apply sum_congr rfl
      intro q hq
      have he : s*E q = (-s*β)+s*inner ℝ (latticePoint L q.1) (latticePoint L q.2) := by dsimp [E]; ring
      rw [he,e_add]
      ring
    rw [heq,norm_mul,norm_e,one_mul]
  obtain ⟨hi,hb⟩ := hint L hL a b
  have hiF : IntegrableOn (fun s => ‖finiteEnergySum I w E s‖) {s : ℝ | |s| ≤ L^2} := by
    simpa only [hnorm,w] using hi
  have hmass : (∫ s in {s : ℝ | |s| ≤ 1/τ}, ‖finiteEnergySum I w E s‖) ≤ C₁*L^(2*(d : ℝ)) := by
    calc
      _ ≤ ∫ s in {s : ℝ | |s| ≤ L^2}, ‖finiteEnergySum I w E s‖ :=
        setIntegral_mono_set hiF (Filter.Eventually.of_forall (fun s => norm_nonneg _))
          (Filter.Eventually.of_forall (fun s hs => hs.trans hwindow))
      _ ≤ _ := by simpa only [hnorm,w] using hb
  rw [Set.ncard_eq_toFinset_card _ hS]
  exact hc.trans ((mul_le_mul_of_nonneg_left hmass (mul_nonneg hC₀.le hτ.le)).trans_eq (by ring))

end WaveTurbulence.WeylSums
