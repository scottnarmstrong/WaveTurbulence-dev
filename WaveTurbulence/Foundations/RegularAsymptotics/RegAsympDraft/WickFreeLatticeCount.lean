/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickPatternCoordinates
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellLatticeCount

/-! # The actual finite free-vector count on a Wick coordinate plane -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset Incoh

/-- The remaining half-cell center on a single-zero link. -/
def wickFreeCenter {d n : ℕ} (σ : Fin n → Fin 4)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (j : {j : Fin n // σ j = 1 ∨ σ j = 2}) : Fin d → ℤ :=
  if σ j.val = 1 then z (j.val,1) else z (j.val,0)

/-- Only the single-zero states require a free vector count. -/
def wickFreeLatticeBox {d n : ℕ} (L : ℝ) (σ : Fin n → Fin 4)
    (z : (Fin n × Fin 2) → Fin d → ℤ) :
    Finset ({j : Fin n // σ j = 1 ∨ σ j = 2} → Fin d → ℤ) :=
  Fintype.piFinset (fun j => halfCellLatticeBox L (wickFreeCenter σ z j))

/-- Nonzero actual source amplitudes force every free vector into its
literal fixed half-cell box, uniformly in the surviving NT variables. -/
theorem mem_wickFreeLatticeBox {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d) (u : WickPatternCoordinates d σ)
    (hW : halfCellAmplitude z β γ
      (fun j => latticePoint L (wickPatternInsert σ u j).1)
      (fun j => latticePoint L (wickPatternInsert σ u j).2) ≠ 0) :
    u.2 ∈ wickFreeLatticeBox L σ z := by
  classical
  rw [wickFreeLatticeBox,Fintype.mem_piFinset]
  intro j
  unfold halfCellAmplitude at hW
  obtain ⟨hx,hy⟩ := mul_ne_zero_iff.mp hW
  rcases j.property with h1 | h2
  · have hh := (prod_ne_zero_iff.mp hy) j.val (mem_univ _)
    have hc : halfLinkCell (z (j.val,1)) (latticePoint L (wickPatternInsert σ u j.val).2) ≠ 0 := by
      intro hz
      exact hh (by rw [hz,smul_zero])
    have hmem := mem_halfCellLatticeBox hL hc
    simpa [wickPatternInsert,wickFreeCenter,h1] using hmem
  · have hh := (prod_ne_zero_iff.mp hx) j.val (mem_univ _)
    have hc : halfLinkCell (z (j.val,0)) (latticePoint L (wickPatternInsert σ u j.val).1) ≠ 0 := by
      intro hz
      exact hh (by rw [hz,smul_zero])
    have hmem := mem_halfCellLatticeBox hL hc
    simpa [wickPatternInsert,wickFreeCenter,h2] using hmem

/-- The actual trace loss is at most one lattice vector per traced link,
including the both-zero intersections with no free vector. -/
theorem card_wickFreeLatticeBox_le {d n : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    ((wickFreeLatticeBox L σ z).card:ℝ) ≤ (2^d*L^d)^(wickTracedLinks σ).card := by
  classical
  rw [wickFreeLatticeBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    _ ≤ ∏ _j : {j : Fin n // σ j = 1 ∨ σ j = 2}, (2^d*L^d) :=
      prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => card_halfCellLatticeBox_le hL (wickFreeCenter σ z j))
    _ = (2^d*L^d)^Fintype.card {j : Fin n // σ j = 1 ∨ σ j = 2} := by simp
    _ ≤ _ := by
      have hbase : (1:ℝ) ≤ 2^d*L^d := by
        simpa only [one_mul] using mul_le_mul (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ 2^d)
          (one_le_pow₀ hL : (1:ℝ) ≤ L^d) zero_le_one (by positivity)
      exact pow_le_pow_right₀ hbase (card_wickPattern_single_le σ)

end WaveTurbulence.RegAsymp
