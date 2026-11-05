/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSurvivorAmplitude
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickTraceCoefficient

/-! # Actual resonant energies on the Wick coordinate planes -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ApproxNT WithLp

/-- The literal scaled lattice inner products in the NT source profile. -/
def wickLatticeEnergy {d n : ℕ} (L μ : ℝ)
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) (j : Fin n) : ℝ :=
  μ*inner ℝ (latticePoint L (θ j).1) (latticePoint L (θ j).2)

/-- Every removed energy vanishes on the whole parametrized plane. -/
theorem wickLatticeEnergy_insert_zero {d n : ℕ} (L μ : ℝ) (σ : Fin n → Fin 4)
    (u : WickPatternCoordinates d σ) {j : Fin n} (hj : j ∈ wickTracedLinks σ) :
    wickLatticeEnergy L μ (wickPatternInsert σ u) j = 0 :=
  wickPattern_energy_zero L μ (prod_wickPatternTerm_insert_ne_zero σ u) hj

/-- The two surviving enumerations preserve exactly the same original label. -/
theorem wickSurvivorEquiv_symm_val {n : ℕ} (σ : Fin n → Fin 4)
    (i : Fin (Fintype.card {j : Fin n // j ∉ wickTracedLinks σ})) :
    ((wickSurvivorEquiv σ).symm i).val =
      ((survivingEnergyEquiv (wickTracedLinks σ)).symm i).val := rfl

/-- A source pattern meeting a special link vanishes identically, before
any coefficient estimate or summation. -/
theorem resProfile_wickPatternInsert_eq_zero {d n : ℕ} (L μ : ℝ)
    (σ : Fin n → Fin 4) (u : WickPatternCoordinates d σ)
    (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (h : ¬Disjoint (wickTracedLinks σ) J) :
    resProfile J Ψ (wickLatticeEnergy L μ (wickPatternInsert σ u)) = 0 := by
  by_contra hp
  exact h (wickTracedLinks_disjoint_special L μ (prod_wickPatternTerm_insert_ne_zero σ u) J Ψ hp)

/-- The actual source profile on a Wick slice is exactly the smaller NT
profile of the simultaneous trace. It is independent of all free traced vectors. -/
theorem resProfile_wickPatternInsert {d n : ℕ} (L μ : ℝ)
    (σ : Fin n → Fin 4) (u : WickPatternCoordinates d σ)
    (J : Finset (Fin n)) (h : Disjoint (wickTracedLinks σ) J)
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L μ (wickPatternInsert σ u)) =
      resProfile (survivingSpecial (wickTracedLinks σ) J)
        (fun Ω => survivingTraceCoefficient (wickTracedLinks σ) J h C (ofLp Ω) lam)
        (fun i => μ*inner ℝ (latticePoint L (u.1 ((wickSurvivorEquiv σ).symm i)).1)
          (latticePoint L (u.1 ((wickSurvivorEquiv σ).symm i)).2)) := by
  rw [← resProfile_survivingTraceCoefficient (wickTracedLinks σ) J h C
    (wickLatticeEnergy L μ (wickPatternInsert σ u))
    (fun j hj => wickLatticeEnergy_insert_zero L μ σ u hj) lam]
  congr 1
  funext i
  have hj := ((survivingEnergyEquiv (wickTracedLinks σ)).symm i).property
  have h0 : σ ((survivingEnergyEquiv (wickTracedLinks σ)).symm i).val = 0 := by
    simpa only [wickTracedLinks,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hj
  simp only [wickLatticeEnergy,wickPatternInsert,dite_eq_left h0]
  rfl

end WaveTurbulence.RegAsymp
