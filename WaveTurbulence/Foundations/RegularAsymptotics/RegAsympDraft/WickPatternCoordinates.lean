/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickPatternSupport

/-! # Exact independent coordinates on source Wick zero planes -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset

/-- Untraced links keep both original vectors; single-zero links keep one.
The both-zero state introduces no free variable. -/
abbrev WickPatternCoordinates (d : ℕ) {n : ℕ} (σ : Fin n → Fin 4) :=
  ({j : Fin n // σ j = 0} → (Fin d → ℤ) × (Fin d → ℤ)) ×
    ({j : Fin n // σ j = 1 ∨ σ j = 2} → Fin d → ℤ)

/-- Insert exactly the zero vectors selected by a four-state source pattern. -/
def wickPatternInsert {d n : ℕ} (σ : Fin n → Fin 4) (u : WickPatternCoordinates d σ)
    (j : Fin n) : (Fin d → ℤ) × (Fin d → ℤ) :=
  if h0 : σ j = 0 then u.1 ⟨j,h0⟩
  else if h1 : σ j = 1 then (0,u.2 ⟨j,Or.inl h1⟩)
  else if h2 : σ j = 2 then (u.2 ⟨j,Or.inr h2⟩,0)
  else (0,0)

/-- Every inserted coordinate satisfies the literal source constraint. -/
theorem wickPatternConstraint_insert {d n : ℕ} (σ : Fin n → Fin 4)
    (u : WickPatternCoordinates d σ) (j : Fin n) :
    wickPatternConstraint (wickPatternInsert σ u) j (σ j) := by
  generalize he : σ j = c
  fin_cases c <;> simp [wickPatternConstraint,wickPatternInsert,he]

/-- Recover the original unconstrained coordinates, with no loss of multiplicity. -/
def wickPatternExtract {d n : ℕ} (σ : Fin n → Fin 4)
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) : WickPatternCoordinates d σ :=
  (fun j => θ j.val, fun j => if σ j.val = 1 then (θ j.val).2 else (θ j.val).1)

theorem wickPatternExtract_insert {d n : ℕ} (σ : Fin n → Fin 4)
    (u : WickPatternCoordinates d σ) : wickPatternExtract σ (wickPatternInsert σ u) = u := by
  apply Prod.ext
  · funext j
    simp [wickPatternExtract,wickPatternInsert,j.property]
  · funext j
    rcases j.property with h1 | h2
    · simp [wickPatternExtract,wickPatternInsert,h1]
    · simp [wickPatternExtract,wickPatternInsert,h2]

theorem wickPatternInsert_extract {d n : ℕ} (σ : Fin n → Fin 4)
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (hθ : ∀ j, wickPatternConstraint θ j (σ j)) :
    wickPatternInsert σ (wickPatternExtract σ θ) = θ := by
  funext j
  have hj := hθ j
  generalize he : σ j = c at hj
  fin_cases c
  · simp [wickPatternInsert,wickPatternExtract,he]
  · have hz : (θ j).1 = 0 := by simpa [wickPatternConstraint] using hj
    simp [wickPatternInsert,wickPatternExtract,he,← hz]
  · have hz : (θ j).2 = 0 := by simpa [wickPatternConstraint] using hj
    simp [wickPatternInsert,wickPatternExtract,he,← hz]
  · have hz : (θ j).1 = 0 ∧ (θ j).2 = 0 := by simpa [wickPatternConstraint] using hj
    simpa only [wickPatternInsert,he,show (3:Fin 4) ≠ 0 by decide,
      show (3:Fin 4) ≠ 1 by decide,show (3:Fin 4) ≠ 2 by decide,dite_false]
      using (Prod.ext hz.1 hz.2).symm

/-- A literal bijection between the independent vectors and the constrained
source lattice. No inequality or oscillatory cancellation is discarded. -/
def wickPatternEquiv {d n : ℕ} (σ : Fin n → Fin 4) :
    WickPatternCoordinates d σ ≃
      {θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) // ∀ j, wickPatternConstraint θ j (σ j)} where
  toFun u := ⟨wickPatternInsert σ u,wickPatternConstraint_insert σ u⟩
  invFun θ := wickPatternExtract σ θ.val
  left_inv := wickPatternExtract_insert σ
  right_inv θ := Subtype.ext (wickPatternInsert_extract σ θ.val θ.property)

/-- The pattern product is its constant signed coefficient on exactly its
coordinate plane. -/
theorem prod_wickPatternTerm_eq_indicator {d n : ℕ} (σ : Fin n → Fin 4)
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    (∏ j, wickPatternTerm θ j (σ j)) =
      {θ | ∀ j, wickPatternConstraint θ j (σ j)}.indicator
        (fun _ => ∏ j, wickPatternCoefficient (σ j)) θ := by
  classical
  simp only [Set.indicator,Set.mem_ofPred_eq]
  by_cases h : ∀ j, wickPatternConstraint θ j (σ j)
  · rw [ite_eq_left h]
    apply prod_congr rfl
    intro j _
    exact ite_eq_left (h j)
  · rw [ite_eq_right h]
    obtain ⟨j,hj⟩ := not_forall.mp h
    apply prod_eq_zero (mem_univ j)
    exact ite_eq_right hj

/-- Exact source lattice reindexing for one Wick pattern. The untraced
oscillatory sum is retained, with no absolute-value relaxation. -/
theorem tsum_wickPatternTerm_mul {d n : ℕ} (σ : Fin n → Fin 4)
    (f : (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) → ℂ) :
    (∑' θ, (∏ j, wickPatternTerm θ j (σ j))*f θ) =
      (∏ j, wickPatternCoefficient (σ j)) * ∑' u : WickPatternCoordinates d σ,
        f (wickPatternInsert σ u) := by
  classical
  let P := {θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) | ∀ j, wickPatternConstraint θ j (σ j)}
  have he : (∑' u : WickPatternCoordinates d σ, f (wickPatternInsert σ u)) =
      ∑' θ : P, f θ.val :=
    (wickPatternEquiv (d := d) σ).tsum_eq (fun θ => f θ.val)
  have hs : (∑' θ : P, f θ.val) = ∑' θ, P.indicator f θ := _root_.tsum_subtype P f
  rw [he,hs,← tsum_mul_left]
  apply tsum_congr
  intro θ
  rw [prod_wickPatternTerm_eq_indicator]
  by_cases h : ∀ j, wickPatternConstraint θ j (σ j)
  · simp [P,h]
  · simp [P,h]

/-- Each traced link introduces at most one free lattice vector. -/
theorem card_wickPattern_single_le {n : ℕ} (σ : Fin n → Fin 4) :
    Fintype.card {j : Fin n // σ j = 1 ∨ σ j = 2} ≤ (wickTracedLinks σ).card := by
  classical
  have h := Fintype.card_subtype_mono (fun j : Fin n => σ j = 1 ∨ σ j = 2)
    (fun j => σ j ≠ 0) (fun j hj => by rcases hj with h | h <;> simp [h])
  simpa only [Fintype.card_subtype,wickTracedLinks] using h

theorem wickPatternCoefficient_ne_zero (c : Fin 4) : wickPatternCoefficient c ≠ 0 := by
  fin_cases c <;> norm_num [wickPatternCoefficient]

/-- No coordinate-plane multiplicity vanishes on its own parametrization. -/
theorem prod_wickPatternTerm_insert_ne_zero {d n : ℕ} (σ : Fin n → Fin 4)
    (u : WickPatternCoordinates d σ) :
    (∏ j, wickPatternTerm (wickPatternInsert σ u) j (σ j)) ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro j _
  simpa only [wickPatternTerm,wickPatternConstraint_insert,dite_true,ite_true]
    using wickPatternCoefficient_ne_zero (σ j)

end WaveTurbulence.RegAsymp
