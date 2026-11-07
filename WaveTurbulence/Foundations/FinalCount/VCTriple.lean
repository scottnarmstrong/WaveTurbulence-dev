/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCPair
/-! # VINE-COUNT part 3: the triple count of the normal-vine core `(u₁, u₂, u₃)` (DH23 `basiccount0` (3), L2048),
via TARGET Lemma A.8 `countLemma_bound` (2), with the radius-`4` localisation. -/
@[expose] public section
set_option autoImplicit false
open Set Finset
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- The core triple set: `lin` is the linear case `⟨u₁,u₃⟩`, otherwise the nonlinear case `⟨u₃, u₁+u₂-u₃⟩`. -/
def TripleSet1 (L : ℝ) (c0 c1 c2 : Mom d) (lin : Bool) (α β τ : ℝ) :
    Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | NearLattice L c0 q.1 ∧ NearLattice L c1 q.2.1 ∧ NearLattice L c2 q.2.2 ∧
    |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ τ ∧
    |inner ℝ (if lin then latticePoint L q.1
        else latticePoint L q.1 + latticePoint L q.2.1 - latticePoint L q.2.2) (latticePoint L q.2.2) - β| ≤ τ}

def TripleSet (L : ℝ) (c0 c1 c2 : Mom d) (lin : Bool) (α β τ : ℝ) :
    Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | Near4 L c0 q.1 ∧ Near4 L c1 q.2.1 ∧ Near4 L c2 q.2.2 ∧
    |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ τ ∧
    |inner ℝ (if lin then latticePoint L q.1
        else latticePoint L q.1 + latticePoint L q.2.1 - latticePoint L q.2.2) (latticePoint L q.2.2) - β| ≤ τ}

theorem tripleSet1_count (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ (c0 c1 c2 : Mom d) (lin : Bool) (α β : ℝ),
      (TripleSet1 L c0 c1 c2 lin α β (δ⁻¹ * L ^ (-2 * γ))).Finite ∧
      ((TripleSet1 L c0 c1 c2 lin α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤
        C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)) := by
  obtain ⟨η₀, hη₀, hη⟩ := countLemma_bound d hd γ hγ
  obtain ⟨C, hC⟩ := hη η₀ ⟨hη₀, le_rfl⟩ 1 le_rfl
  refine ⟨max C 0, le_max_right _ _, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hC δ hδ
  refine ⟨max L₀ (Real.exp 1), fun L hL c0 c1 c2 lin α β => ?_⟩
  have hLL : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hL0 : 0 < L := by linarith
  have hδ0 := hδ.1
  have h := (hL₀ L hLL α β 0 0 0 (Or.inl rfl) (fun _ => rfl) (fun h => absurd h (lt_irrefl _))
    (fun h => absurd h (by norm_num)) c0 c1 c2 0 (if lin then 0 else 2)).2
  have hset : TripleSet1 L c0 c1 c2 lin α β (δ⁻¹ * L ^ (-2 * γ)) =
      {q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) | NearLattice L c0 q.1 ∧ NearLattice L c1 q.2.1 ∧
        NearLattice L c2 q.2.2 ∧ |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ δ⁻¹ * L ^ (-2 * γ) ∧
        |inner ℝ (![latticePoint L q.1 - latticePoint L (0 : Fin d → ℤ),
            latticePoint L q.1 + latticePoint L q.2.1 - latticePoint L (0 : Fin d → ℤ),
            latticePoint L q.1 + latticePoint L q.2.1 - latticePoint L (0 : Fin d → ℤ) - latticePoint L q.2.2]
            (if lin then 0 else 2)) (latticePoint L q.2.2) - β| ≤ δ⁻¹ * L ^ (-2 * γ)} := by
    ext q
    cases lin <;> simp [TripleSet1, latticePoint_zero]
  rw [hset]
  refine ⟨h.1, h.2.trans ?_⟩
  have ha : 0 ≤ δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) := by positivity
  have h1 : L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) ≤ L ^ (3 * ((d : ℝ) - γ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by
      have : 0 ≤ min γ (1 - γ) := le_min hγ.1.le (by linarith [hγ.2])
      linarith)
  have h2 := mul_le_mul_of_nonneg_right (le_max_left C 0) ha
  calc _ = C * (δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))) := by ring
    _ ≤ max C 0 * (δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))) := h2
    _ ≤ max C 0 * (δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (le_max_right _ _)
    _ = _ := by ring

/-- The radius-`4` triple count. -/
theorem tripleSet_count (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ (c0 c1 c2 : Mom d) (lin : Bool) (α β : ℝ),
      (TripleSet L c0 c1 c2 lin α β (δ⁻¹ * L ^ (-2 * γ))).Finite ∧
      ((TripleSet L c0 c1 c2 lin α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤
        C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)) := by
  obtain ⟨C, hC0, hC⟩ := tripleSet1_count hd hγ
  refine ⟨(coverNum d : ℝ) ^ 3 * C, by positivity, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hC δ hδ
  refine ⟨L₀, fun L hL c0 c1 c2 lin α β => ?_⟩
  set X := C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)) with hX
  have hsub : TripleSet L c0 c1 c2 lin α β (δ⁻¹ * L ^ (-2 * γ)) ⊆
      ⋃ i : coverSet d × coverSet d × coverSet d,
        TripleSet1 L (c0 + i.1.1) (c1 + i.2.1.1) (c2 + i.2.2.1) lin α β (δ⁻¹ * L ^ (-2 * γ)) := by
    intro q hq
    obtain ⟨n1, n2, n3, i1, i2⟩ := hq
    obtain ⟨t1, ht1, h1⟩ := near4_sub L n1
    obtain ⟨t2, ht2, h2⟩ := near4_sub L n2
    obtain ⟨t3, ht3, h3⟩ := near4_sub L n3
    exact Set.mem_iUnion.mpr ⟨(⟨t1, ht1⟩, ⟨t2, ht2⟩, ⟨t3, ht3⟩), h1, h2, h3, i1, i2⟩
  have hfin : (⋃ i : coverSet d × coverSet d × coverSet d,
        TripleSet1 L (c0 + i.1.1) (c1 + i.2.1.1) (c2 + i.2.2.1) lin α β (δ⁻¹ * L ^ (-2 * γ))).Finite :=
    Set.finite_iUnion fun i => (hL₀ L hL _ _ _ lin α β).1
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_iUnion_le_of_fintype (fun i : coverSet d × coverSet d × coverSet d =>
        TripleSet1 L (c0 + i.1.1) (c1 + i.2.1.1) (c2 + i.2.2.1) lin α β (δ⁻¹ * L ^ (-2 * γ)))
  have h3 : ∑ i : coverSet d × coverSet d × coverSet d, ((TripleSet1 L (c0 + i.1.1) (c1 + i.2.1.1) (c2 + i.2.2.1)
        lin α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤ ∑ _i : coverSet d × coverSet d × coverSet d, X :=
    Finset.sum_le_sum fun i _ => (hL₀ L hL _ _ _ lin α β).2
  calc _ ≤ ((⋃ i : coverSet d × coverSet d × coverSet d,
        TripleSet1 L (c0 + i.1.1) (c1 + i.2.1.1) (c2 + i.2.2.1) lin α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) := by
        exact_mod_cast h1
    _ ≤ ((∑ i : coverSet d × coverSet d × coverSet d, (TripleSet1 L (c0 + i.1.1) (c1 + i.2.1.1) (c2 + i.2.2.1)
        lin α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℕ) : ℝ) := by exact_mod_cast h2
    _ = ∑ i : coverSet d × coverSet d × coverSet d, ((TripleSet1 L (c0 + i.1.1) (c1 + i.2.1.1) (c2 + i.2.2.1)
        lin α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) := by push_cast; rfl
    _ ≤ _ := h3
    _ = (coverNum d : ℝ) ^ 3 * C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)) := by
        simp [hX, coverNum, pow_succ]
        ring

end WaveTurbulence.VineCount
