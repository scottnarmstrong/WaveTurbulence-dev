/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AlphaCount
/-! Triangles, part 7 (FINALCOUNT-G2): lattice-point counts: boxes, slabs `{u : |n·u| ≤ r}` (DH23 Lemma `basiccount`
(1), used at L1793: the number of `k` in a unit ball with `r·k` in an interval of length `ℓ` is
`≲ L^{d-1} + ℓ L^{d} |r|^{-1}` for `|r| ≥ L^{-1}`) and gap balls. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {d : ℕ}

theorem mem_alphaN_of_norm_le (L : ℝ) (hL : 0 < L) (r₀ : Mom d) (ρ : ℝ) (n : Fin d → ℤ)
    (hb : ‖latticePoint L n - r₀‖ ≤ ρ) : n ∈ alphaN d L r₀ ρ := by
  unfold alphaN
  rw [Fintype.mem_piFinset]
  intro i
  have h1 : ‖(latticePoint L n - r₀) i‖ ≤ ‖latticePoint L n - r₀‖ := PiLp.norm_apply_le _ i
  have h2 : (latticePoint L n - r₀) i = (n i : ℝ) / L - r₀ i := rfl
  rw [h2, Real.norm_eq_abs] at h1
  have h3 := abs_le.mp (h1.trans hb)
  rw [Finset.mem_Icc]
  have e1 : (n i : ℝ) = L * ((n i : ℝ) / L) := by field_simp
  constructor
  · exact Int.ceil_le.mpr (by nlinarith [h3.1])
  · exact Int.le_floor.mpr (by nlinarith [h3.2])

/-- The box `[-m, m]^d` of integer vectors. -/
def boxF (d m : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m

theorem card_boxF (m : ℕ) : (boxF d m).card = (2 * m + 1) ^ d := by
  unfold boxF
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1; omega

theorem mem_boxF {m : ℕ} {u : Fin d → ℤ} : u ∈ boxF d m ↔ ∀ i, |u i| ≤ m := by
  unfold boxF
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_Icc, abs_le]

/-- The slab `{u ∈ box : |n · u| ≤ r}`. -/
noncomputable def slabF (d : ℕ) (n : Fin d → ℤ) (m : ℕ) (r : ℝ) : Finset (Fin d → ℤ) :=
  (boxF d m).filter fun u => |∑ i, (n i : ℝ) * (u i : ℝ)| ≤ r

theorem card_slabF (n : Fin d → ℤ) (hn : n ≠ 0) (m : ℕ) (r : ℝ) :
    (slabF d n m r).card ≤ (⌊2 * r⌋₊ + 1) * (2 * m + 1) ^ (d - 1) := by
  classical
  by_cases hr : r < 0
  · have : slabF d n m r = ∅ := by
      unfold slabF
      rw [Finset.filter_eq_empty_iff]
      intro u _ h; exact absurd (h.trans_lt hr) (not_lt.mpr (abs_nonneg _))
    rw [this]; simp
  push Not at hr
  obtain ⟨i0, hi0⟩ : ∃ i0, n i0 ≠ 0 := by
    by_contra h; push Not at h; exact hn (funext h)
  let ψ : (Fin d → ℤ) → ℤ × ({j // j ≠ i0} → ℤ) := fun u => (∑ i, n i * u i, fun j => u j.1)
  have hcard : (Finset.Icc (-⌊r⌋) ⌊r⌋ ×ˢ (Fintype.piFinset fun _ : {j // j ≠ i0} => Finset.Icc (-(m : ℤ)) m)).card
      ≤ (⌊2 * r⌋₊ + 1) * (2 * m + 1) ^ (d - 1) := by
    rw [Finset.card_product, Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ]
    have h1 : (Fintype.card {j : Fin d // j ≠ i0}) = d - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]; simp
    rw [h1]
    refine Nat.mul_le_mul ?_ ?_
    · have : ⌊r⌋ + 1 + ⌊r⌋ ≤ ⌊2 * r⌋ + 1 := by
        have := Int.floor_le r
        have h2 : (⌊r⌋ : ℝ) + ⌊r⌋ ≤ 2 * r := by linarith
        have h3 : ⌊r⌋ + ⌊r⌋ ≤ ⌊2 * r⌋ := Int.le_floor.mpr (by push_cast; linarith)
        linarith
      have h4 := Int.natCast_floor_eq_floor (a := 2 * r) (by linarith)
      omega
    · apply le_of_eq; congr 1; omega
  refine le_trans (Finset.card_le_card_of_injOn ψ ?_ ?_) hcard
  · intro u hu
    rw [Finset.mem_coe] at hu
    unfold slabF at hu
    rw [Finset.mem_filter, mem_boxF] at hu
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Fintype.mem_piFinset]
    have habs := abs_le.mp hu.2
    have hs : (((∑ i, n i * u i : ℤ)) : ℝ) = ∑ i, (n i : ℝ) * (u i : ℝ) := by push_cast; rfl
    refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
    · have h1 : -r ≤ (((∑ i, n i * u i : ℤ)) : ℝ) := by rw [hs]; exact habs.1
      have h2 : (-⌊r⌋ : ℤ) ≤ ∑ i, n i * u i := by
        have : (⌈-r⌉ : ℤ) ≤ ∑ i, n i * u i := Int.ceil_le.mpr h1
        rwa [Int.ceil_neg] at this
      exact h2
    · have h1 : (((∑ i, n i * u i : ℤ)) : ℝ) ≤ r := by rw [hs]; exact habs.2
      exact Int.le_floor.mpr h1
    · have := hu.1 j.1
      simp only [Finset.mem_Icc, abs_le] at this ⊢
      exact ⟨by linarith [this.1], this.2⟩
  · intro u hu u' hu' h
    simp only [ψ, Prod.mk.injEq] at h
    obtain ⟨hs, hj⟩ := h
    funext i
    by_cases hi : i = i0
    · subst hi
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hs
      have : ∑ x ∈ Finset.univ.erase i, n x * u x = ∑ x ∈ Finset.univ.erase i, n x * u' x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have := congrFun hj ⟨x, (Finset.mem_erase.mp hx).1⟩
        simp only at this
        rw [this]
      rw [this] at hs
      have h2 : n i * u i = n i * u' i := by linarith
      exact mul_left_cancel₀ hi0 h2
    · exact congrFun hj ⟨i, hi⟩

theorem inner_latticePoint (L : ℝ) (a b : Fin d → ℤ) :
    inner ℝ (latticePoint L a) (latticePoint L b) = (∑ i, (a i : ℝ) * (b i : ℝ)) / L ^ 2 := by
  simp only [latticePoint, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [star_trivial, WithLp.ofLp_toLp, Pi.star_apply]
  ring

end WaveTurbulence.FinalCount
