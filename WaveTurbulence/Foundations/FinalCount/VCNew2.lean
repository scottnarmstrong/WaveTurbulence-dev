/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew1
public import WaveTurbulence.Foundations.CountLemmas.AtomCount
/-! # VINE-COUNT part 24 (session 4): the slab count `≲ ν δ⁻¹ L^{d-γ+γ₀}` (TARGET Lemma `atomcountlem`, `atomcountbd`,
the difference sign `ε = -1` with `k = r ≠ 0`), radius-`4` localised. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- The lattice points of a radius-`4` ball in the slab `|2⟨r, z⟩ - β'| ≤ tol`. -/
def slabSet (L : ℝ) (cen : Mom d) (r : Fin d → ℤ) (β' tol : ℝ) : Set (Fin d → ℤ) :=
  {z | Near4 L cen z ∧ |2 * inner ℝ (latticePoint L r) (latticePoint L z) - β'| ≤ tol}

/-- Unit-ball version, from `atomCountLemma_bound` with `δ' = δ/ν`. -/
theorem slab1_count (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ ν : ℝ, 1 ≤ ν → ∀ n₀ : Fin d → ℤ, n₀ ≠ 0 →
      ∀ (a : Mom d) (β' : ℝ),
      {z : Fin d → ℤ | NearLattice L a z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)}.Finite ∧
      (({z : Fin d → ℤ | NearLattice L a z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)}.ncard : ℝ) ≤
        C * ν * δ⁻¹ * min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ))) := by
  have hγ0 := hγ.1
  have hγ1 := hγ.2
  have hη : 0 < min γ (1 - γ) / 2 := by
    have : 0 < min γ (1 - γ) := lt_min hγ0 (by linarith)
    linarith
  obtain ⟨C, L₀, h⟩ := atomCountLemma_bound d hd γ hγ (min γ (1 - γ) / 2) hη le_rfl
  refine ⟨max C 0, max L₀ 1, le_max_right _ _, fun L hL δ hδ ν hν n₀ hn a β' => ?_⟩
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hL₀ : L ≥ L₀ := (le_max_left _ _).trans hL
  have hν0 : 0 < ν := by linarith
  have hδ' : δ / ν ∈ Ioc (0 : ℝ) 1 := ⟨div_pos hδ.1 hν0, by
    rw [div_le_one hν0]; exact hδ.2.trans hν⟩
  have h' := h L hL₀ (δ / ν) hδ' (β' - ‖latticePoint L n₀‖ ^ 2) n₀ a (a - latticePoint L n₀) 0
  obtain ⟨hfin, hb, -, -⟩ := h'
  have hfin1 := hfin (-1)
  have hb1 := hb (-1) (fun _ => hn)
  simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, Int.reduceNeg] at hfin1 hb1
  have htol : (δ / ν)⁻¹ * L ^ (-2 * γ) = ν * δ⁻¹ * L ^ (-2 * γ) := by
    rw [inv_div]; ring
  set A : Set (Fin d → ℤ) := {z : Fin d → ℤ | NearLattice L a z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)} with hA
  let f : (Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ) := fun z => (z, z - n₀)
  have hmaps : ∀ z ∈ A, f z ∈ {q : (Fin d → ℤ) × (Fin d → ℤ) | NearLattice L a q.1 ∧
        NearLattice L (a - latticePoint L n₀) q.2 ∧ q.1 + -q.2 = n₀ ∧
        |‖latticePoint L q.1‖ ^ 2 + (-1 : ℤ) * ‖latticePoint L q.2‖ ^ 2 - (β' - ‖latticePoint L n₀‖ ^ 2)| ≤
          (δ / ν)⁻¹ * L ^ (-2 * γ)} := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    refine ⟨h1, ?_, ?_, ?_⟩
    · unfold NearLattice at h1 ⊢
      simp only [f, latticePoint_sub]
      convert h1 using 2; abel
    · simp [f, sub_eq_add_neg]
    · rw [htol]
      simp only [f, latticePoint_sub]
      have e : ‖latticePoint L z‖ ^ 2 + (-1 : ℤ) * ‖latticePoint L z - latticePoint L n₀‖ ^ 2 -
          (β' - ‖latticePoint L n₀‖ ^ 2) = 2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β' := by
        rw [norm_sub_sq_real, real_inner_comm]
        push_cast; ring
      rw [e]; exact h2
  have hinj : Set.InjOn f A := fun z _ z' _ h => (Prod.ext_iff.mp h).1
  have hAfin : A.Finite := hfin1.of_injOn hmaps hinj
  refine ⟨hAfin, ?_⟩
  have hc := Set.ncard_le_ncard_of_injOn f hmaps hinj (ht := hfin1)
  have hCm : C ≤ max C 0 := le_max_left _ _
  have hmin : 0 ≤ min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ)) := by
    positivity
  calc (A.ncard : ℝ) ≤ C * (δ / ν)⁻¹ * min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ)) := (Nat.cast_le.mpr hc).trans hb1
    _ ≤ max C 0 * ν * δ⁻¹ * min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ)) := by
        rw [inv_div]
        have e : max C 0 * ν * δ⁻¹ = max C 0 * (ν / δ) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm (div_nonneg hν0.le hδ.1.le)) hmin

theorem min_pow_le (hd : ℕ) {L γ : ℝ} (hL : 1 ≤ L) :
    min (L ^ hd) (L ^ ((hd : ℝ) + 1 - 2 * γ)) ≤ L ^ ((hd : ℝ) - γ + min γ (1 - γ)) := by
  have hL0 : 0 < L := by linarith
  rcases le_total γ (1 - γ) with h | h
  · rw [min_eq_left h]
    refine (min_le_left _ _).trans (le_of_eq ?_)
    rw [← Real.rpow_natCast]; congr 1; ring
  · rw [min_eq_right h]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    congr 1; ring

/-- **The slab count** (radius-`4` ball): at most `N_d C ν δ⁻¹ L^{d-γ+γ₀}` lattice points. -/
theorem slab_count (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ ν : ℝ, 1 ≤ ν → ∀ n₀ : Fin d → ℤ, n₀ ≠ 0 →
      ∀ (cen : Mom d) (β' : ℝ),
      (slabSet L cen n₀ β' (ν * δ⁻¹ * L ^ (-2 * γ))).Finite ∧
      ((slabSet L cen n₀ β' (ν * δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤
        (coverNum d : ℝ) * C * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ)) := by
  obtain ⟨C, L₀, hC0, h⟩ := slab1_count hd hγ
  refine ⟨C, max L₀ 1, hC0, le_max_right _ _, fun L hL δ hδ ν hν n₀ hn cen β' => ?_⟩
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hL₀ : L ≥ L₀ := (le_max_left _ _).trans hL
  have hν0 : 0 < ν := by linarith
  have hsub : slabSet L cen n₀ β' (ν * δ⁻¹ * L ^ (-2 * γ)) ⊆ ⋃ t : coverSet d,
      {z : Fin d → ℤ | NearLattice L (cen + t.1) z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)} := by
    intro z hz
    obtain ⟨t, ht, h1⟩ := near4_sub L hz.1
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, h1, hz.2⟩
  have hU := fun t : coverSet d => h L hL₀ δ hδ ν hν n₀ hn (cen + t.1) β'
  have hfin : (⋃ t : coverSet d, {z : Fin d → ℤ | NearLattice L (cen + t.1) z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)}).Finite :=
    Set.finite_iUnion fun t => (hU t).1
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_iUnion_le_of_fintype (fun t : coverSet d =>
      {z : Fin d → ℤ | NearLattice L (cen + t.1) z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)})
  have hmin := min_pow_le d (γ := γ) hL1
  have hX : 0 ≤ C * ν * δ⁻¹ := by
    have := hδ.1; positivity
  have h3 : ∀ t : coverSet d, (({z : Fin d → ℤ | NearLattice L (cen + t.1) z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)}.ncard : ℕ) : ℝ) ≤
      C * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ)) := fun t =>
    (hU t).2.trans (mul_le_mul_of_nonneg_left hmin hX)
  calc _ ≤ ((⋃ t : coverSet d, {z : Fin d → ℤ | NearLattice L (cen + t.1) z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)}).ncard : ℝ) := by
        exact_mod_cast h1
    _ ≤ ((∑ t : coverSet d, ({z : Fin d → ℤ | NearLattice L (cen + t.1) z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)}.ncard : ℕ)) : ℝ) := by
        exact_mod_cast h2
    _ = ∑ t : coverSet d, (({z : Fin d → ℤ | NearLattice L (cen + t.1) z ∧
        |2 * inner ℝ (latticePoint L n₀) (latticePoint L z) - β'| ≤ ν * δ⁻¹ * L ^ (-2 * γ)}.ncard : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ _t : coverSet d, C * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ)) := Finset.sum_le_sum fun t _ => h3 t
    _ = _ := by simp [coverNum]; ring

end WaveTurbulence.VineCount
