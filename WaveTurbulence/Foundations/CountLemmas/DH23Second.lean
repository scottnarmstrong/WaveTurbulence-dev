/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.SecondPairSelectors
public import WaveTurbulence.Foundations.CountLemmas.CoupledSets

/-! # DH23 Lemma A.2(2), including the critical γ=4/5 saving -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- DH23 Lemma A.2(2), TeX L2061 and L2080–L2085. The explicit η₀ realizes
the standing smallness hierarchy. The nonzero dyadic scale P is at least one
lattice spacing; only its lower norm comparison is needed. The threshold
may depend on fixed δ, uniformly over P and all spatial/energy centers.
The proof uses the unconditional circle exponent 27/41 rather than Huxley. -/
theorem dh23_second_pair_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀, (4 : ℝ)/5-10*η < γ →
    ∀ c : ℝ, 1 ≤ c → ∃ C : ℝ, 0 < C ∧
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α β : ℝ,
    ∀ nr : Fin d → ℤ, ∀ P ∈ Icc L⁻¹ 1, c⁻¹*P ≤ ‖latticePoint L nr‖ →
    ∀ a b : Mom d, ∀ ξsel : Fin 3,
      (coupledPairSet L a b (latticePoint L nr) α β (δ⁻¹*L^(-2*γ)) ξsel).Finite ∧
      ((coupledPairSet L a b (latticePoint L nr) α β (δ⁻¹*L^(-2*γ)) ξsel).ncard : ℝ) ≤
        C*δ⁻¹^2*L^(2*((d : ℝ)-γ)-(1-γ)-20*η) := by
  intro d hd γ hγ
  refine ⟨secondPairEta0 γ,secondPairEta0_pos hγ.2,?_⟩
  intro η hη hcritical c hc
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  refine ⟨1,zero_lt_one,?_⟩
  intro δ hδ
  obtain ⟨R,hR⟩ := exists_second_pair_selector_bound d hd c γ η hcpos hγ.2 hη.1 hη.2 hcritical δ hδ.1
  refine ⟨max R 2,?_⟩
  intro L hL α β nr P hP hr a b ξsel
  have hL2 : 2 ≤ L := (le_max_right R 2).trans hL
  have hLp : 0 < L := by linarith only [hL2]
  have hgap : c⁻¹*L⁻¹ ≤ ‖latticePoint L nr‖ :=
    (mul_le_mul_of_nonneg_left hP.1 (inv_nonneg.mpr hcpos.le)).trans hr
  have hf := finite_coupledPairSet hLp a b (latticePoint L nr) α β (δ⁻¹*L^(-2*γ)) ξsel
  refine ⟨hf,?_⟩
  have hb := hR L ((le_max_left R 2).trans hL) a b (latticePoint L nr) α β hgap ξsel hf.toFinset
    (fun q hq => hf.mem_toFinset.mp hq)
  rw [← Set.ncard_eq_toFinset_card _ hf] at hb
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hδsq : 1 ≤ δ⁻¹^2 := by nlinarith only [hδi]
  have heq : 2*((d : ℝ)-γ)-(1-γ)-20*η = 2*(d : ℝ)-γ-1-20*η := by ring
  rw [heq,one_mul]
  apply hb.trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hδsq
    (by positivity : 0 ≤ L^(2*(d : ℝ)-γ-1-20*η))

end WaveTurbulence.CountLemmas
