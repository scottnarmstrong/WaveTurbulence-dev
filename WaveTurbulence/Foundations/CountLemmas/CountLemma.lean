/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairCount
public import WaveTurbulence.Foundations.CountLemmas.TripleCount

/-! # TARGET Lemma A.8 in the exact audited B1.7 form -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.8 (DH23 Lemma A.2(1),(3)), copied from audited B1.7.
The proof is independent of η, so η₀=1 is a valid witness. The constant is
uniform in δ, while L₀ may depend on its fixed value. -/
theorem countLemma_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀,
    ∀ c₀ : ℝ, 1 ≤ c₀ → ∃ C : ℝ, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α β : ℝ,
    ∀ (nr nv : Fin d → ℤ) (Pr : ℝ), (Pr = 0 ∨ Pr ∈ Icc L⁻¹ 1) →
      (Pr = 0 → nr = 0) →
      (0 < Pr → Pr < 1 → c₀⁻¹ * Pr ≤ ‖latticePoint L nr‖ ∧ ‖latticePoint L nr‖ ≤ c₀ * Pr) →
      (Pr = 1 → c₀⁻¹ ≤ ‖latticePoint L nr‖ ∧ ‖latticePoint L nr‖ ≤ c₀) →
    ∀ ax ay az : Mom d, ∀ ξsel : Fin 3, ∀ ζsel : Fin 3,
      let r := latticePoint L nr
      let v := latticePoint L nv
      let 𝔛 := min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr)
      let tol := δ⁻¹ * L ^ (-2 * γ)
      let S₁ : Set ((Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L ax q.1 ∧ NearLattice L ay q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2) - α| ≤ tol ∧
        |inner ℝ r (![latticePoint L q.1, latticePoint L q.2,
            latticePoint L q.1 + latticePoint L q.2] ξsel) - β| ≤ tol}
      let S₂ : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L ax q.1 ∧
        NearLattice L ay q.2.1 ∧ NearLattice L az q.2.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ tol ∧
        |inner ℝ (![latticePoint L q.1 - v, latticePoint L q.1 + latticePoint L q.2.1 - v,
            latticePoint L q.1 + latticePoint L q.2.1 - v - latticePoint L q.2.2] ζsel)
          (latticePoint L q.2.2) - β| ≤ tol}
      (S₁.Finite ∧ (S₁.ncard : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * 𝔛⁻¹) ∧
      (S₂.Finite ∧ (S₂.ncard : ℝ) ≤
        C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))) := by
  intro d hd γ hγ
  refine ⟨1,zero_lt_one,?_⟩
  intro η hη c hc
  obtain ⟨Cp,hCp,hpair⟩ := coupledPair_bound d hd γ hγ c hc
  obtain ⟨Ct,Rt,hCt,htriple⟩ := coupledTriple_bound d hd γ hγ
  refine ⟨max Cp Ct,?_⟩
  intro δ hδ
  obtain ⟨Rp,hpairδ⟩ := hpair δ hδ
  refine ⟨max (max Rp Rt) 1,?_⟩
  intro L hL α β nr nv P hP _hPzero hmid hend ax ay az ξsel ζsel
  have hL1 : 1 ≤ L := (le_max_right (max Rp Rt) 1).trans hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hδp := hδ.1
  have hP0 : 0 ≤ P := by
    rcases hP with rfl | hP
    · exact le_rfl
    · exact (inv_pos.mpr hLp).le.trans hP.1
  have hr : 0 < P → c⁻¹*P ≤ ‖latticePoint L nr‖ := by
    intro hPp
    by_cases hP1 : P < 1
    · exact (hmid hPp hP1).1
    · have hPmem : P ∈ Icc L⁻¹ 1 := hP.resolve_left (ne_of_gt hPp)
      have heq : P = 1 := le_antisymm hPmem.2 (le_of_not_gt hP1)
      simpa only [heq,mul_one] using (hend heq).1
  obtain ⟨hfp,hbp⟩ := hpairδ L ((le_max_left Rp Rt).trans ((le_max_left (max Rp Rt) 1).trans hL))
    ax ay (latticePoint L nr) α β ξsel P hP hr
  obtain ⟨hft,hbt⟩ := htriple L ((le_max_right Rp Rt).trans ((le_max_left (max Rp Rt) 1).trans hL))
    δ hδ ax ay az nv ζsel α β
  have hX : 0 ≤ (min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ :=
    inv_nonneg.mpr (le_min (sq_nonneg _) (by positivity))
  have hmp : Cp*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ ≤
      max Cp Ct*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Cp Ct) (inv_nonneg.mpr hδp.le)) (by positivity)) hX
  have hmt : Ct*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) ≤
      max Cp Ct*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right Cp Ct) (sq_nonneg _)) (by positivity)
  exact ⟨⟨hfp,hbp.trans hmp⟩,⟨hft,hbt.trans hmt⟩⟩


end WaveTurbulence.CountLemmas
