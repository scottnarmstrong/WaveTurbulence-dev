/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.TripleSigns
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-! # The six labels of a double pair with a small gap (DH23 L1975)

Labels `q = (p₁, p₂, a, a', b, b')`: `p₁, p₂` the double bond, `a, a'` the other bonds of `v₁`, `b, b'` those of `v₂`.
The conservation law at `v₁` and the energy window at `v₁` constrain the triple `(p₁, p₂, a')` once `a` is fixed;
the conservation law at `v₂` determines `b'`; the small gap constrains `b` to a ball of radius `L λ` around `σ a`:
`#T ≤ (2L+1)^d (2Lλ+1)^d · C δ⁻¹ L^{2(d−γ)}`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.CountLemmas
variable {d : ℕ}

theorem coord_le_norm {L : ℝ} (x y : Fin d → ℤ) (i : Fin d) (σ : ℤ) (hL : 0 < L) :
    |(x i : ℝ) - (σ : ℝ) * (y i : ℝ)| ≤ L * ‖latticePoint L x - (σ : ℝ) • latticePoint L y‖ := by
  have h : |(latticePoint L x - (σ : ℝ) • latticePoint L y) i| ≤ ‖latticePoint L x - (σ : ℝ) • latticePoint L y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L x - (σ : ℝ) • latticePoint L y) i
  have he : (latticePoint L x - (σ : ℝ) • latticePoint L y) i = ((x i : ℝ) - (σ : ℝ) * (y i : ℝ)) / L := by
    simp only [latticePoint, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [he, abs_div, abs_of_pos hL, div_le_iff₀ hL] at h
  linarith

theorem sixTuple_card_le (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ lam : ℝ, 0 ≤ lam →
      ∀ (ε1 ε2 εa εa' εb εb' σ : ℤ), (ε1 = 1 ∨ ε1 = -1) → (ε2 = 1 ∨ ε2 = -1) → (εa' = 1 ∨ εa' = -1) →
      (εb' = 1 ∨ εb' = -1) → ¬ (ε1 = ε2 ∧ ε2 = εa') → (σ = 1 ∨ σ = -1) →
      ∀ (cen : Fin 6 → Mom d) (n1 n2 : Fin d → ℤ) (β1 : ℝ) (T : Finset (Fin 6 → Fin d → ℤ)),
      (∀ q ∈ T, (∀ i, NearLattice L (cen i) (q i)) ∧
        ε1 • q 0 + ε2 • q 1 + εa • q 2 + εa' • q 3 = n1 ∧
        |(ε1 : ℝ) * ‖latticePoint L (q 0)‖ ^ 2 + (ε2 : ℝ) * ‖latticePoint L (q 1)‖ ^ 2 +
          (εa : ℝ) * ‖latticePoint L (q 2)‖ ^ 2 + (εa' : ℝ) * ‖latticePoint L (q 3)‖ ^ 2 - β1| ≤ δ⁻¹ * L ^ (-2 * γ) ∧
        -(ε1 • q 0) - ε2 • q 1 + εb • q 4 + εb' • q 5 = n2 ∧
        ‖latticePoint L (q 2) - (σ : ℝ) • latticePoint L (q 4)‖ ≤ lam) →
      (T.card : ℝ) ≤ (2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) := by
  classical
  obtain ⟨C, L₀, h⟩ := signedTriple_card_le d hd γ hγ
  refine ⟨max C 0, max L₀ 1, le_max_right _ _, fun L hL δ hδ lam hlam ε1 ε2 εa εa' εb εb' σ h1 h2 h3 h4 hne hσ cen n1 n2 β1 T hT => ?_⟩
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hL)
  have hLL : L ≥ L₀ := (le_max_left _ _).trans hL
  set f : (Fin 6 → Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ) := fun q => (q 2, q 4) with hf
  set t := T.image f with ht
  have hmaps : ∀ q ∈ T, f q ∈ t := fun q hq => mem_image_of_mem f hq
  set N : ℝ := max C 0 * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) with hN
  have hN0 : 0 ≤ N := by have := hδ.1; positivity
  -- the fibers
  have hfib : ∀ p ∈ t, ((T.filter fun q => f q = p).card : ℝ) ≤ N := by
    intro p hp
    set Fb := T.filter fun q => f q = p
    set g : (Fin 6 → Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) := fun q => (q 0, q 1, q 3) with hg
    have hginj : Set.InjOn g Fb := by
      intro q hq q' hq' hgq
      obtain ⟨hqT, hqf⟩ := mem_filter.mp hq
      obtain ⟨hq'T, hqf'⟩ := mem_filter.mp hq'
      simp only [hg, Prod.mk.injEq] at hgq
      have e2 : q 2 = q' 2 := congrArg Prod.fst (hqf.trans hqf'.symm)
      have e4 : q 4 = q' 4 := congrArg Prod.snd (hqf.trans hqf'.symm)
      have m := (hT q hqT).2.2.2.1
      have m' := (hT q' hq'T).2.2.2.1
      have hb5 : εb' • q 5 = εb' • q' 5 := by
        have : εb' • q 5 = n2 - (-(ε1 • q 0) - ε2 • q 1 + εb • q 4) := by rw [← m]; abel
        have : εb' • q' 5 = n2 - (-(ε1 • q' 0) - ε2 • q' 1 + εb • q' 4) := by rw [← m']; abel
        simp_all
      have hε0 : εb' ≠ 0 := by rcases h4 with rfl | rfl <;> norm_num
      have e5 := smul_right_injective (Fin d → ℤ) hε0 hb5
      funext i; fin_cases i
      · exact hgq.1
      · exact hgq.2.1
      · exact e2
      · exact hgq.2.2
      · exact e4
      · exact e5
    have hcard : (Fb.image g).card = Fb.card := card_image_of_injOn hginj
    have hbound := h L hLL δ hδ ε1 ε2 εa' h1 h2 h3 hne (cen 0) (cen 1) (cen 3) (n1 - εa • p.1)
      (β1 - (εa : ℝ) * ‖latticePoint L p.1‖ ^ 2) (Fb.image g) (by
        intro u hu
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
        obtain ⟨hqT, hqf⟩ := mem_filter.mp hq
        have e2 : q 2 = p.1 := congrArg Prod.fst hqf
        obtain ⟨hN1, hm, hE, _, _⟩ := hT q hqT
        refine ⟨hN1 0, hN1 1, hN1 3, ?_, ?_⟩
        · show ε1 • q 0 + ε2 • q 1 + εa' • q 3 = n1 - εa • p.1
          rw [← e2, ← hm]; abel
        · show |(ε1 : ℝ) * ‖latticePoint L (q 0)‖ ^ 2 + (ε2 : ℝ) * ‖latticePoint L (q 1)‖ ^ 2 +
              (εa' : ℝ) * ‖latticePoint L (q 3)‖ ^ 2 - (β1 - (εa : ℝ) * ‖latticePoint L p.1‖ ^ 2)| ≤ _
          rw [← e2]
          convert hE using 2; ring)
    rw [hcard] at hbound
    refine hbound.trans ?_
    have : 0 ≤ δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) := by have := hδ.1; positivity
    calc C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) = C * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) := by ring
      _ ≤ max C 0 * (δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = N := by ring
  -- the pairs `(a, b)`
  have hpairs : (t.card : ℝ) ≤ (2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d := by
    set A := Counting.latticeBox (fun i => L * cen 2 i) L with hA
    set P := A.biUnion fun a => (Counting.latticeBox (fun i => (σ : ℝ) * (a i : ℝ)) (L * lam)).image fun b => (a, b)
      with hP
    have hsub : t ⊆ P := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      obtain ⟨hN1, _, _, _, hg⟩ := hT q hq
      refine mem_biUnion.mpr ⟨q 2, nearLattice_mem_box hLp (cen 2) (q 2) (hN1 2), mem_image.mpr ⟨q 4, ?_, rfl⟩⟩
      rw [Counting.mem_latticeBox]
      intro i
      have hgs : ‖latticePoint L (q 4) - (σ : ℝ) • latticePoint L (q 2)‖ ≤ lam := by
        rcases hσ with rfl | rfl
        · simpa [norm_sub_rev] using hg
        · simpa [sub_neg_eq_add, add_comm] using hg
      have := coord_le_norm (L := L) (q 4) (q 2) i σ hLp
      have h2 : |(q 4 i : ℝ) - (σ : ℝ) * (q 2 i : ℝ)| ≤ L * lam :=
        this.trans (mul_le_mul_of_nonneg_left hgs hLp.le)
      simpa [abs_sub_comm] using h2
    have hA' : (A.card : ℝ) ≤ (2 * L + 1) ^ d := Counting.card_latticeBox_le _ hLp.le
    have hc1 : (t.card : ℝ) ≤ ((∑ a ∈ A, ((Counting.latticeBox (fun i => (σ : ℝ) * (a i : ℝ)) (L * lam)).image
        fun b => (a, b)).card : ℕ) : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    refine le_trans hc1 ?_
    have hb : ∀ a ∈ A, (((Counting.latticeBox (fun i => (σ : ℝ) * (a i : ℝ)) (L * lam)).image fun b => (a, b)).card : ℝ) ≤
        (2 * (L * lam) + 1) ^ d := by
      intro a _
      exact le_trans (by exact_mod_cast card_image_le) (Counting.card_latticeBox_le _ (by positivity))
    calc ((∑ a ∈ A, ((Counting.latticeBox (fun i => (σ : ℝ) * (a i : ℝ)) (L * lam)).image fun b => (a, b)).card : ℕ) : ℝ)
        = ∑ a ∈ A, (((Counting.latticeBox (fun i => (σ : ℝ) * (a i : ℝ)) (L * lam)).image fun b => (a, b)).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ _a ∈ A, (2 * (L * lam) + 1) ^ d := sum_le_sum hb
      _ = (A.card : ℝ) * (2 * (L * lam) + 1) ^ d := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hA' (by positivity)
  -- assemble
  have hsum : T.card = ∑ p ∈ t, (T.filter fun q => f q = p).card := card_eq_sum_card_fiberwise hmaps
  have : (T.card : ℝ) = ∑ p ∈ t, ((T.filter fun q => f q = p).card : ℝ) := by exact_mod_cast hsum
  rw [this]
  calc ∑ p ∈ t, ((T.filter fun q => f q = p).card : ℝ) ≤ ∑ _p ∈ t, N := sum_le_sum hfib
    _ = (t.card : ℝ) * N := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      rw [mul_comm ((2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d) N, mul_comm (t.card : ℝ) N]
      exact mul_le_mul_of_nonneg_left hpairs hN0

end WaveTurbulence.FinalCountG8
