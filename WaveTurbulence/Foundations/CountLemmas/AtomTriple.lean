/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.LatticeSets
public import WaveTurbulence.Foundations.WeylSums.ThreeVectorCount

/-! # TARGET Lemma A.9: the three-vector item -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- Conjunct reordering identifies the exact audited draft set with the
proved conservation/energy set. -/
theorem atomTripleSet_eq {d : ℕ} (L : ℝ) (a b c : Mom d)
    (nk : Fin d → ℤ) (β τ : ℝ) :
    atomTripleSet L a b c nk β τ = WeylSums.threeVectorBandSet L nk a b c β τ := by
  ext q
  change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  tauto

/-- DH23 Lemma A.3(2), TARGET Lemma A.9, three-vector item in the exact B1.8
carrier and unit-ball convention. Constants are uniform in δ and all centers. -/
theorem atomTriple_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ β : ℝ,
    ∀ nk : Fin d → ℤ, ∀ a b c : Mom d,
      (atomTripleSet L a b c nk β (δ⁻¹ * L^(-2*γ))).Finite ∧
      ((atomTripleSet L a b c nk β (δ⁻¹ * L^(-2*γ))).ncard : ℝ) ≤
        C * δ⁻¹ * L^(2*((d : ℝ)-γ)) := by
  intro d hd γ hγ
  obtain ⟨C,R,hR⟩ := WeylSums.three_vector_lattice_count d hd γ hγ
  refine ⟨C,max R 1,?_⟩
  intro L hL δ hδ β nk a b c
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_right R 1).trans hL)
  refine ⟨finite_atomTripleSet hLp a b c nk β _,?_⟩
  rw [atomTripleSet_eq]
  simpa only [Nat.card_coe_set_eq] using
    hR L ((le_max_left R 1).trans hL) δ hδ nk a b c β

end WaveTurbulence.CountLemmas
