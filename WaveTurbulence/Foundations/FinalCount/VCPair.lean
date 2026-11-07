/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCLattice
/-! # VINE-COUNT part 2: the pair count of one chart rung `(x_j, y_j)` (DH23 Lemma `basiccount0` (1), L2048--L2070,
via TARGET Lemma A.8 `countLemma_bound`), with signed coefficients `ζ₀ x + ζ₁ y` of the contract and the radius-`4`
localisation of the chart coordinates. -/
@[expose] public section
set_option autoImplicit false
open Set Finset
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.CountLemmas

variable {d : ℕ}

theorem latticePoint_add (L : ℝ) (n m : Fin d → ℤ) : latticePoint L (n + m) = latticePoint L n + latticePoint L m := by
  ext i; simp [latticePoint, add_div]

theorem latticePoint_neg (L : ℝ) (n : Fin d → ℤ) : latticePoint L (-n) = -latticePoint L n := by
  ext i; simp [latticePoint, neg_div]

theorem latticePoint_sub (L : ℝ) (n m : Fin d → ℤ) : latticePoint L (n - m) = latticePoint L n - latticePoint L m := by
  ext i; simp [latticePoint, sub_div]

theorem latticePoint_zero (L : ℝ) : latticePoint L (0 : Fin d → ℤ) = 0 := by
  ext i; simp [latticePoint]

theorem latticePoint_smul (L : ℝ) (ε : ℤ) (n : Fin d → ℤ) : latticePoint L (ε • n) = (ε : ℝ) • latticePoint L n := by
  ext i; simp [latticePoint, mul_div_assoc]

/-- The pair set of one chart rung (unit-ball version). -/
def PairSet1 (L : ℝ) (cx cy : Mom d) (r : Mom d) (ζ0 ζ1 : ℤ) (α β τ : ℝ) : Set ((Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | NearLattice L cx q.1 ∧ NearLattice L cy q.2 ∧ |inner ℝ (latticePoint L q.1) (latticePoint L q.2) - α| ≤ τ ∧
    |inner ℝ r ((ζ0 : ℝ) • latticePoint L q.1 + (ζ1 : ℝ) • latticePoint L q.2) - β| ≤ τ}

/-- The pair set of one chart rung (radius-`4` version). -/
def PairSet (L : ℝ) (cx cy : Mom d) (r : Mom d) (ζ0 ζ1 : ℤ) (α β τ : ℝ) : Set ((Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | Near4 L cx q.1 ∧ Near4 L cy q.2 ∧ |inner ℝ (latticePoint L q.1) (latticePoint L q.2) - α| ≤ τ ∧
    |inner ℝ r ((ζ0 : ℝ) • latticePoint L q.1 + (ζ1 : ℝ) • latticePoint L q.2) - β| ≤ τ}

theorem ncard_le_of_injOn_finite {α β : Type*} {A : Set α} {S : Set β} (f : α → β) (hf : ∀ a ∈ A, f a ∈ S)
    (hinj : Function.Injective f) (hS : S.Finite) : A.Finite ∧ A.ncard ≤ S.ncard := by
  refine ⟨?_, Set.ncard_le_ncard_of_injOn f hf hinj.injOn hS⟩
  exact (hS.preimage hinj.injOn).subset fun a ha => hf a ha

/-- The consequence of main's `coupledPair_bound` (the first counting inequality of Lemma A.8), constants made explicit.
Only the lower norm comparison `c₀⁻¹ Pr ≤ ‖r‖` is used (no upper bound on `‖r‖`, also not at `Pr = 1`). -/
theorem pair_unit (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {c₀ : ℝ} (hc₀ : 1 ≤ c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ (nr : Fin d → ℤ) (Pr : ℝ),
      (Pr = 0 ∨ Pr ∈ Icc L⁻¹ 1) → (0 < Pr → c₀⁻¹ * Pr ≤ ‖latticePoint L nr‖) →
      ∀ (ax ay : Mom d) (α β : ℝ) (ξsel : Fin 3),
        ({q : (Fin d → ℤ) × (Fin d → ℤ) | NearLattice L ax q.1 ∧ NearLattice L ay q.2 ∧
          |inner ℝ (latticePoint L q.1) (latticePoint L q.2) - α| ≤ δ⁻¹ * L ^ (-2 * γ) ∧
          |inner ℝ (latticePoint L nr)
            (![latticePoint L q.1, latticePoint L q.2, latticePoint L q.1 + latticePoint L q.2] ξsel) - β|
            ≤ δ⁻¹ * L ^ (-2 * γ)}).Finite ∧
        (({q : (Fin d → ℤ) × (Fin d → ℤ) | NearLattice L ax q.1 ∧ NearLattice L ay q.2 ∧
          |inner ℝ (latticePoint L q.1) (latticePoint L q.2) - α| ≤ δ⁻¹ * L ^ (-2 * γ) ∧
          |inner ℝ (latticePoint L nr)
            (![latticePoint L q.1, latticePoint L q.2, latticePoint L q.1 + latticePoint L q.2] ξsel) - β|
            ≤ δ⁻¹ * L ^ (-2 * γ)}.ncard : ℝ) ≤
          C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * (min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr))⁻¹) := by
  obtain ⟨C, hC, hpair⟩ := coupledPair_bound d hd γ hγ c₀ hc₀
  refine ⟨C, hC.le, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hpair δ hδ
  exact ⟨L₀, fun L hL nr Pr hP hlow ax ay α β ξsel =>
    hL₀ L hL ax ay (latticePoint L nr) α β ξsel Pr hP (fun h => by simpa using hlow h)⟩

theorem abs_sign_mul_sub {s i β : ℝ} (hs : s = 1 ∨ s = -1) : |s * i - β| = |i - s * β| := by
  rcases hs with rfl | rfl
  · simp
  · rw [show (-1 : ℝ) * i - β = -(i - (-1) * β) by ring, abs_neg]

theorem ncard_real_le_of_map {α β : Type*} {A : Set α} {S : Set β} (f : α → β) (hf : ∀ a ∈ A, f a ∈ S)
    (hinj : Function.Injective f) (hS : S.Finite) {B : ℝ} (hB : (S.ncard : ℝ) ≤ B) :
    A.Finite ∧ (A.ncard : ℝ) ≤ B := by
  obtain ⟨h1, h2⟩ := ncard_le_of_injOn_finite f hf hinj hS
  exact ⟨h1, le_trans (by exact_mod_cast h2) hB⟩

/-- Unit-ball pair count with the signed coefficients `(ζ₀, ζ₁) ≠ 0` of the contract. -/
theorem pairSet1_count (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {c₀ : ℝ} (hc₀ : 1 ≤ c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ (nr : Fin d → ℤ) (Pr : ℝ),
      (Pr = 0 ∨ Pr ∈ Icc L⁻¹ 1) → (0 < Pr → c₀⁻¹ * Pr ≤ ‖latticePoint L nr‖) →
      ∀ (cx cy : Mom d) (α β : ℝ) (ζ0 ζ1 : ℤ), (ζ0 = 0 ∨ ζ0 = 1 ∨ ζ0 = -1) → (ζ1 = 0 ∨ ζ1 = 1 ∨ ζ1 = -1) →
        (ζ0 ≠ 0 ∨ ζ1 ≠ 0) →
        (PairSet1 L cx cy (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ))).Finite ∧
        ((PairSet1 L cx cy (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤
          C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * (min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr))⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := pair_unit hd hγ hc₀
  refine ⟨C, hC0, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hC δ hδ
  refine ⟨L₀, fun L hL nr Pr hP hlow cx cy α β ζ0 ζ1 hζ0 hζ1 hne => ?_⟩
  have hU := hL₀ L hL nr Pr hP hlow
  set r := latticePoint L nr with hr
  have hi1 : ∀ (a b : Mom d) (s t : ℝ), inner ℝ r (s • a + t • b) = s * inner ℝ r a + t * inner ℝ r b := by
    intro a b s t
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  by_cases h1 : ζ1 = 0
  · have hz0 : (ζ0 : ℝ) = 1 ∨ (ζ0 : ℝ) = -1 := by
      rcases hζ0 with h | h | h
      · exact absurd h (hne.resolve_right (not_not.2 h1))
      · left; simp [h]
      · right; simp [h]
    obtain ⟨hf, hb⟩ := hU cx cy α ((ζ0 : ℝ) * β) 0
    refine ncard_real_le_of_map id (fun q hq => ?_) Function.injective_id hf hb
    obtain ⟨n1, n2, i1, i2⟩ := hq
    refine ⟨n1, n2, i1, ?_⟩
    simp only [Matrix.cons_val_zero]
    rw [h1, Int.cast_zero, hi1] at i2
    simp only [zero_mul, add_zero] at i2
    rw [abs_sign_mul_sub hz0] at i2
    simpa using i2
  · by_cases h0 : ζ0 = 0
    · have hz1 : (ζ1 : ℝ) = 1 ∨ (ζ1 : ℝ) = -1 := by
        rcases hζ1 with h | h | h
        · exact absurd h h1
        · left; simp [h]
        · right; simp [h]
      obtain ⟨hf, hb⟩ := hU cx cy α ((ζ1 : ℝ) * β) 1
      refine ncard_real_le_of_map id (fun q hq => ?_) Function.injective_id hf hb
      obtain ⟨n1, n2, i1, i2⟩ := hq
      refine ⟨n1, n2, i1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h0, Int.cast_zero, hi1] at i2
      simp only [zero_mul, zero_add] at i2
      rw [abs_sign_mul_sub hz1] at i2
      simpa using i2
    · have hz0 : (ζ0 : ℝ) = 1 ∨ (ζ0 : ℝ) = -1 := by
        rcases hζ0 with h | h | h
        · exact absurd h h0
        · left; simp [h]
        · right; simp [h]
      have hz1 : ζ1 = 1 ∨ ζ1 = -1 := by
        rcases hζ1 with h | h | h
        · exact absurd h h1
        · exact Or.inl h
        · exact Or.inr h
      have hz0' : ζ0 = 1 ∨ ζ0 = -1 := by
        rcases hζ0 with h | h | h
        · exact absurd h h0
        · exact Or.inl h
        · exact Or.inr h
      set ε : ℤ := ζ0 * ζ1 with hε
      have hεu : ε = 1 ∨ ε = -1 := by
        rcases hz0' with h | h <;> rcases hz1 with h' | h' <;> simp [hε, h, h']
      have hε0 : ε ≠ 0 := by rcases hεu with h | h <;> simp [h]
      have hζ1ε : (ζ1 : ℝ) = (ζ0 : ℝ) * (ε : ℝ) := by
        rcases hz0' with h | h <;> rcases hz1 with h' | h' <;> simp [hε, h, h']
      have hεabs : |(ε : ℝ)| = 1 := by rcases hεu with h | h <;> simp [h]
      obtain ⟨hf, hb⟩ := hU cx ((ε : ℝ) • cy) ((ε : ℝ) * α) ((ζ0 : ℝ) * β) 2
      refine ncard_real_le_of_map (fun q => (q.1, ε • q.2)) (fun q hq => ?_) ?_ hf hb
      · obtain ⟨n1, n2, i1, i2⟩ := hq
        refine ⟨n1, ?_, ?_, ?_⟩
        · unfold NearLattice at n2 ⊢
          rw [latticePoint_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, hεabs, one_mul]
          exact n2
        · simp only [latticePoint_smul, real_inner_smul_right]
          rw [← mul_sub, abs_mul, hεabs, one_mul]
          exact i1
        · simp only [Matrix.cons_val_two, latticePoint_smul]
          have : (ζ0 : ℝ) • latticePoint L q.1 + (ζ1 : ℝ) • latticePoint L q.2 =
              (ζ0 : ℝ) • (latticePoint L q.1 + (ε : ℝ) • latticePoint L q.2) := by
            rw [smul_add, smul_smul, ← hζ1ε]
          rw [this, real_inner_smul_right, abs_sign_mul_sub hz0] at i2
          simpa using i2
      · intro q q' h
        have h' : (q.1, ε • q.2) = (q'.1, ε • q'.2) := h
        have h1 : q.1 = q'.1 := (Prod.mk.inj h').1
        have h2 : ε • q.2 = ε • q'.2 := (Prod.mk.inj h').2
        exact Prod.ext h1 (smul_right_injective _ hε0 h2)

/-- The radius-`4` pair count: `N_d²` unit-ball counts. -/
theorem pairSet_count (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {c₀ : ℝ} (hc₀ : 1 ≤ c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ (nr : Fin d → ℤ) (Pr : ℝ),
      (Pr = 0 ∨ Pr ∈ Icc L⁻¹ 1) → (0 < Pr → c₀⁻¹ * Pr ≤ ‖latticePoint L nr‖) →
      ∀ (cx cy : Mom d) (α β : ℝ) (ζ0 ζ1 : ℤ), (ζ0 = 0 ∨ ζ0 = 1 ∨ ζ0 = -1) → (ζ1 = 0 ∨ ζ1 = 1 ∨ ζ1 = -1) →
        (ζ0 ≠ 0 ∨ ζ1 ≠ 0) →
        (PairSet L cx cy (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ))).Finite ∧
        ((PairSet L cx cy (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤
          C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * (min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr))⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := pairSet1_count hd hγ hc₀
  refine ⟨(coverNum d : ℝ) ^ 2 * C, by positivity, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hC δ hδ
  refine ⟨L₀, fun L hL nr Pr hP hlow cx cy α β ζ0 ζ1 hζ0 hζ1 hne => ?_⟩
  have hU := hL₀ L hL nr Pr hP hlow
  set X := C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * (min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr))⁻¹ with hX
  have hsub : PairSet L cx cy (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ)) ⊆
      ⋃ i : coverSet d × coverSet d,
        PairSet1 L (cx + i.1.1) (cy + i.2.1) (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ)) := by
    intro q hq
    obtain ⟨n1, n2, i1, i2⟩ := hq
    obtain ⟨t1, ht1, h1⟩ := near4_sub L n1
    obtain ⟨t2, ht2, h2⟩ := near4_sub L n2
    exact Set.mem_iUnion.mpr ⟨(⟨t1, ht1⟩, ⟨t2, ht2⟩), h1, h2, i1, i2⟩
  have hfin : (⋃ i : coverSet d × coverSet d,
        PairSet1 L (cx + i.1.1) (cy + i.2.1) (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ))).Finite :=
    Set.finite_iUnion fun i => (hU _ _ α β ζ0 ζ1 hζ0 hζ1 hne).1
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_iUnion_le_of_fintype (fun i : coverSet d × coverSet d =>
        PairSet1 L (cx + i.1.1) (cy + i.2.1) (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ)))
  have h3 : ∑ i : coverSet d × coverSet d, ((PairSet1 L (cx + i.1.1) (cy + i.2.1) (latticePoint L nr) ζ0 ζ1 α β
        (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤ ∑ _i : coverSet d × coverSet d, X :=
    Finset.sum_le_sum fun i _ => (hU _ _ α β ζ0 ζ1 hζ0 hζ1 hne).2
  calc _ ≤ ((⋃ i : coverSet d × coverSet d,
        PairSet1 L (cx + i.1.1) (cy + i.2.1) (latticePoint L nr) ζ0 ζ1 α β (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) := by
        exact_mod_cast h1
    _ ≤ ((∑ i : coverSet d × coverSet d, (PairSet1 L (cx + i.1.1) (cy + i.2.1) (latticePoint L nr) ζ0 ζ1 α β
        (δ⁻¹ * L ^ (-2 * γ))).ncard : ℕ) : ℝ) := by exact_mod_cast h2
    _ = ∑ i : coverSet d × coverSet d, ((PairSet1 L (cx + i.1.1) (cy + i.2.1) (latticePoint L nr) ζ0 ζ1 α β
        (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) := by push_cast; rfl
    _ ≤ _ := h3
    _ = (coverNum d : ℝ) ^ 2 * C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) *
          (min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr))⁻¹ := by
        simp [hX, coverNum, sq]
        ring

end WaveTurbulence.VineCount
