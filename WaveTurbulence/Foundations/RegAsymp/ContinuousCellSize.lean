/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.AppCellBound

/-! # Derivative-only size bound for the continuous NT cell integral

The high temporal frequencies in DH23 Prop6.1 require a crude bound
without the maximum-coordinate moment. Only the literal L1 symbol norm
and the regularity needed for Fourier inversion enter this estimate.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset WithLp
open scoped ENNReal ContDiff FourierTransform

/-- The continuous cell integral has its natural μ⁻ⁿ size without any
moment assumption on the temporal symbol. -/
theorem exists_continuous_cell_size_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι],
      ∀ (J : Finset ι) (Kj : ι → ℕ) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (D : ℕ → ℝ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ D → (∀ k, 0 ≤ D k) →
      ∀ D0 : ℝ, (∫ Ω, ‖Ψ Ω‖) ≤ D0 → ∀ μ : ℝ, 1 < μ → ∀ c : CellData d ι,
      (∀ j, μ*((‖c.p j‖+Real.sqrt d)*(‖c.q j‖+Real.sqrt d)) ≤ 2^Kj j) →
      ‖multiInt μ (truncProfile J Kj Ψ) c.p c.q c.ξ c.ζ‖ ≤
        (K/μ)^Fintype.card ι*D0 := by
  obtain ⟨M,hM0,hM⟩ := exists_pvCell hd
  let K := max M (cellCa d)
  have hK1 : 1 ≤ K := (one_le_cellCa d).trans (le_max_right _ _)
  refine ⟨K,hK1,?_⟩
  intro ι _ _ J Kj Ψ D hΨ hD hD0 D0 hD0' μ hμ c hK
  have hμ0 : 0 < μ := by linarith
  have hμi : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμ0.le
  have hD00 : 0 ≤ D0 := (integral_nonneg (fun _ => norm_nonneg _)).trans hD0'
  let g : ι → ℝ → ℂ := fun i t => cellInt (c.p i) (c.q i) (c.ξ i) (c.ζ i) (μ*t)
  let Pt : ι → ℂ := fun j => pvTrunc μ (cellFn (c.p j) (c.q j) (c.ξ j) (c.ζ j))
  let B := ∫ b : {j // j ∉ J} → ℝ, 𝓕 Ψ (toLp 2 b)*∏ i : {j // j ∉ J}, g i (b i)
  have hrep := isFourierRep_truncProfile (d := d) (by omega) J Kj hΨ hD hD0
  have hmain : multiInt μ (truncProfile J Kj Ψ) c.p c.q c.ξ c.ζ =
      (∏ j ∈ J, ((μ⁻¹:ℂ)*Pt j))*B := by
    rw [multiInt_eq μ hrep,integral_truncProfileHat_split J Kj Ψ g]
    congr 1
    exact prod_congr rfl (fun j _ => jfactor_eq hμ0 (hK j) _ _)
  have hPt (j : ι) : ‖Pt j‖ ≤ K :=
    ((hM _ _ _ _).1 μ hμ).trans (le_max_left _ _)
  have hCa : 0 ≤ cellCa d := zero_le_one.trans (one_le_cellCa d)
  have hB : ‖B‖ ≤ D0*(μ⁻¹*K)^Fintype.card {j // j ∉ J} := by
    have hh := norm_B_le hd hμ0 hD0'
      (fun i : {j // j ∉ J} => c.p i) (fun i : {j // j ∉ J} => c.q i)
      (fun i : {j // j ∉ J} => c.ξ i) (fun i : {j // j ∉ J} => c.ζ i)
    apply hh.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (le_max_right _ _) hμi) _) hD00
  have hprod : ‖∏ j ∈ J, ((μ⁻¹:ℂ)*Pt j)‖ ≤ (μ⁻¹*K)^J.card := by
    apply (Finset.norm_prod_le _ _).trans
    calc
      _ ≤ ∏ _j ∈ J, μ⁻¹*K := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => by
        rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hμ0]
        exact mul_le_mul_of_nonneg_left (hPt j) hμi)
      _ = _ := by simp
  have hcard : J.card+Fintype.card {j // j ∉ J} = Fintype.card ι := by
    rw [Fintype.card_subtype_compl,Fintype.card_coe]
    have hh := card_le_univ J
    omega
  rw [hmain,norm_mul]
  calc
    _ ≤ (μ⁻¹*K)^J.card*(D0*(μ⁻¹*K)^Fintype.card {j // j ∉ J}) :=
      mul_le_mul hprod hB (norm_nonneg _) (by positivity)
    _ = (μ⁻¹*K)^Fintype.card ι*D0 := by rw [← hcard,pow_add]; ring
    _ = _ := by rw [div_eq_mul_inv,mul_comm K μ⁻¹]

end WaveTurbulence.RegAsymp
