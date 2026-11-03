/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PositiveAtom
public import WaveTurbulence.Foundations.CountLemmas.NegativeAtom
public import WaveTurbulence.Foundations.CountLemmas.AtomTriple

/-! # TARGET Lemma A.9 in the exact audited B1.8 form -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.9 (DH23 Lemma A.3(1),(2)), copied from audited B1.8.
The difference sign requires nonzero conserved momentum; the large-difference
item uses the approved reading of the source's `r`. -/
theorem atomCountLemma_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ min γ (1 - γ) / 2 →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ β : ℝ, ∀ nk : Fin d → ℤ, ∀ a₁ a₂ a₃ : Mom d,
      let k := latticePoint L nk
      let tol := δ⁻¹ * L ^ (-2 * γ)
      let S₂ (ε : ℤˣ) : Set ((Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L a₁ q.1 ∧
        NearLattice L a₂ q.2 ∧ q.1 + (ε : ℤ) • q.2 = nk ∧
        |‖latticePoint L q.1‖ ^ 2 + (ε : ℤ) * ‖latticePoint L q.2‖ ^ 2 - β| ≤ tol}
      let S₃ : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L a₁ q.1 ∧
        NearLattice L a₂ q.2.1 ∧ NearLattice L a₃ q.2.2 ∧ q.1 - q.2.1 + q.2.2 = nk ∧
        |‖latticePoint L q.1‖ ^ 2 - ‖latticePoint L q.2.1‖ ^ 2 + ‖latticePoint L q.2.2‖ ^ 2 - β| ≤
          tol}
      (∀ ε : ℤˣ, (S₂ ε).Finite) ∧
      (∀ ε : ℤˣ, (ε = -1 → nk ≠ 0) →
        ((S₂ ε).ncard : ℝ) ≤ C * δ⁻¹ * min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ))) ∧
      (L ^ (-γ + η) ≤ ‖k‖ → ((S₂ (-1)).ncard : ℝ) ≤ C * δ⁻¹ * L ^ ((d : ℝ) - γ - η)) ∧
      (S₃.Finite ∧ (S₃.ncard : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) := by
  intro d hd γ hγ η hη hηmax
  obtain ⟨Ct,R,ht⟩ := atomTriple_bound d hd γ hγ
  let Kp : ℝ := 3^(d-2)*(2*(6*Real.pi+1284002))
  let Kn : ℝ := 2*3^d
  let Ks : ℝ := 3^(d-1)*((d : ℝ)+1)
  let C : ℝ := max Ct (max Kp (max Kn (max Ks (3^d))))
  have hCt : Ct ≤ C := le_max_left _ _
  have hKp : Kp ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hKn : Kn ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKs : Ks ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  have hKb : (3 : ℝ)^d ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨C,max R 1,?_⟩
  intro L hL δ hδ β nk a₁ a₂ a₃
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hmono {A B e : ℝ} (hAB : A ≤ B) : A*δ⁻¹*L^e ≤ B*δ⁻¹*L^e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB (by positivity)) (by positivity)
  dsimp only
  refine ⟨fun ε => finite_atomPairSet hLp a₁ a₂ nk β _ ε,?_,?_,?_⟩
  · intro ε hnk
    rcases Int.units_eq_one_or ε with rfl | rfl
    · have hp := positive_atom_energy_bound (by omega : 2 ≤ d) hL1 hδ hγ.2.le a₁ a₂ nk β
      have he := hp.trans (hmono hKp)
      have hc := atomPair_trivial_bound hLp a₁ a₂ nk β (δ⁻¹*L^(-2*γ)) 1
      have hb : (2*L+1)^d ≤ (3 : ℝ)^d*L^d := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith only [hL1]) d
      have hspace : ((atomPairSet L a₁ a₂ nk β (δ⁻¹*L^(-2*γ)) 1).ncard : ℝ) ≤ C*δ⁻¹*L^d := by
        apply (hc.trans hb).trans
        have hcc : (3 : ℝ)^d ≤ C*δ⁻¹ := hKb.trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hδi
            ((pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) d).trans hKb))
        exact mul_le_mul_of_nonneg_right hcc (by positivity)
      rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ C*δ⁻¹)]
      exact le_min hspace he
    · have hn := negative_atom_bound hL1 hδ hγ.2.le a₁ a₂ nk (hnk rfl) β
      exact hn.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKn (by positivity)) (by positivity))
  · intro hgap
    have hη' : η ≤ 1-γ := hηmax.trans (by
      have hh := min_le_right γ (1-γ)
      linarith only [hh,hγ.2])
    exact (negative_atom_large_bound (by omega : 0 < d) hL1 hδ hη' a₁ a₂ nk β hgap).trans (hmono hKs)
  · obtain ⟨hf,hb⟩ := ht L ((le_max_left R 1).trans hL) δ hδ β nk a₁ a₂ a₃
    exact ⟨hf,hb.trans (hmono hCt)⟩

end WaveTurbulence.CountLemmas
