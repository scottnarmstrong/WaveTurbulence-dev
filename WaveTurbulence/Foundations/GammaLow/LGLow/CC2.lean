/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.LGLow.CC1

/-! # LG-low (packet L07): the flower couple clause through the waist, part 2

The P7 declarations of `Port/P7/{Total,TotalAssembly,Assembly,Final,FreeBound,FinalFalse,Adapter,AdapterFalse,Export}`
that carry an `LGContext`, copied by source over this area's `CC.LGContext` (no other change). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow.CC
open WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.GammaLow.LGLow

section
-- source: FlowerTop/Port/P7/Total.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

/-- The shared hypotheses of the piece bounds. -/
structure PieceHyp (C₀ : ℕ) (P : WTParams) (p N : ℕ) (Rr : ℕ → Mom P.d → ℝ) (k : Mom P.d)
    (tt : Fin (2 * 3) → ℝ) (Creg : ℕ → ℝ) where
  G : LGContext C₀ P
  hp : p < P.D
  hN : N ≤ P.N (p + 1) ^ 4
  hRr : RemainderBound P Rr p
  hR1 : 1 ≤ P.R (p + 1)
  hmmax : 3 ≤ 10 * P.R (p + 1)
  htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)
  hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|
  hnum6 : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 3 * P.Lambda (p + 1)) *
    gardenT P G.Cφ p 3 N' ^ (8 * 3 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 3) * P.δ ^ (6 * P.ν * N') *
    P.L ^ (-P.η ^ 7) * P.L ^ (-((3 : ℕ) - 1 : ℝ) / 70) ≤ 1
  hnumA : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 2 * P.Lambda (p + 1)) *
    gardenT P G.Cφ p 2 N' ^ (8 * 2 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 2) * P.δ ^ (6 * P.ν * N') *
    P.L ^ (-P.η ^ 7) * P.L ^ (-((2 : ℕ) - 1 : ℝ) / 70) ≤ 1
  hnumC : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
    coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
    P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))
  hreg : RegularFamilyBound P (inputsF P Rr) p Creg

end

section
-- source: FlowerTop/Port/P7/TotalAssembly.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {tt : Fin (2 * 3) → ℝ} {Creg : ℕ → ℝ}
  (H : PieceHyp C₀ P p N Rr k tt Creg) (kind : TreeKind) (n : Fin (2 * 3) → (Fin P.d → ℤ))
include H

theorem bound_shape6 :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 Finset.univ},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Bound6 P p N kind k n := by
  have hset : {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 Finset.univ} = Irr6 P p N kind := by
    ext y
    constructor
    · rintro ⟨hy, hm⟩
      exact ⟨hy, (minimalAt_univ_iff y.garden (Y6Set_plain P p N kind hy)).1 hm⟩
    · rintro ⟨hy, hi⟩
      exact ⟨hy, (minimalAt_univ_iff y.garden (Y6Set_plain P p N kind hy)).2 hi⟩
  rw [hset]
  exact piece0_norm_le C₀ P H.G H.hp H.hN kind Rr H.hRr H.hmmax n k tt H.htt H.hnum6

theorem bound_shape42 (σ : Fin (2 * 2) ⊕ Fin 2 ≃ Fin (2 * 3)) (S : Finset (Fin (2 * 3)))
    (hS : S = Finset.univ.image fun i => σ (.inl i)) (h0 : σ (.inl 0) = 0)
    (hs2 : (fun i => childSig (σ (.inr i))) = ![1, -1]) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 S},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Bound42 P p N kind σ 0 Creg k n := by
  subst hS
  have hset : {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 (Finset.univ.image fun i => σ (.inl i))} =
      {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden (σ (.inl 0)) (Finset.univ.image fun i => σ (.inl i))} := by
    rw [h0]
  rw [hset]
  exact piece42_norm_le C₀ P H.G H.hp H.hN kind Rr H.hRr (by have := H.hmmax; omega) H.hR1 σ 0 hs2 n k tt H.htt H.hF
    H.hnumA H.hnumC Creg H.hreg

theorem bound_shape24 (σ : Fin 2 ⊕ Fin (2 * 2) ≃ Fin (2 * 3)) (S : Finset (Fin (2 * 3)))
    (hS : S = Finset.univ.image fun i => σ (.inl i)) (h0 : σ (.inl 0) = 0)
    (hsA : (fun i => childSig (σ (.inl i))) = ![1, -1])
    (hs4 : (fun i => childSig (σ (.inr i))) = ![1, -1, 1, -1]) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 S},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Bound24 P p N kind σ Creg k n := by
  subst hS
  have hset : {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden 0 (Finset.univ.image fun i => σ (.inl i))} =
      {y | y ∈ Y6Set P p N kind ∧ MinimalAt y.garden (σ (.inl 0)) (Finset.univ.image fun i => σ (.inl i))} := by
    rw [h0]
  rw [hset]
  exact piece24_norm_le C₀ P H.G H.hp H.hN kind Rr H.hRr H.hR1 (by have := H.hmmax; omega) σ hsA hs4 n k tt H.htt
    H.hF H.hnumA H.hnumC Creg H.hreg

/-- **The six-tree sum over the decapitated carrier, at fixed outer root labels `n`, is bounded by the sum of the
sixteen explicit piece bounds.** -/
theorem Y6_sum_norm_le :
    ‖∑ᶠ y ∈ Y6Set P p N kind,
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Bound24 P p N kind σ1 Creg k n + Bound24 P p N kind σ2 Creg k n + Bound24 P p N kind σ3 Creg k n +
      Bound42 P p N kind σ4 0 Creg k n + Bound42 P p N kind σ5 0 Creg k n + Bound42 P p N kind σ6 0 Creg k n +
      Bound42 P p N kind σ7 0 Creg k n + Bound42 P p N kind σ8 0 Creg k n + Bound42 P p N kind σ9 0 Creg k n +
      Bound6 P p N kind k n := by
  rw [finsum_Y6_partition]
  refine (norm_sum_le _ _).trans ?_
  rw [shapeFin_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h1 := bound_shape24 H kind n σ1 {0, 1} (by ext x; fin_cases x <;> simp [σ1, tableEquiv, Fin.exists_fin_two])
    (by simp [σ1, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ1, tableEquiv] <;> decide)
    (by funext i; fin_cases i <;> simp [σ1, tableEquiv] <;> decide)
  have h2 := bound_shape24 H kind n σ2 {0, 3} (by ext x; fin_cases x <;> simp [σ2, tableEquiv, Fin.exists_fin_two])
    (by simp [σ2, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ2, tableEquiv] <;> decide)
    (by funext i; fin_cases i <;> simp [σ2, tableEquiv] <;> decide)
  have h3 := bound_shape24 H kind n σ3 {0, 5} (by ext x; fin_cases x <;> simp [σ3, tableEquiv, Fin.exists_fin_two])
    (by simp [σ3, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ3, tableEquiv] <;> decide)
    (by funext i; fin_cases i <;> simp [σ3, tableEquiv] <;> decide)
  have h4 := bound_shape42 H kind n σ4 {0, 3, 4, 5}
    (by ext x; fin_cases x <;> simp [σ4, tableEquiv, Fin.exists_fin_succ]) (by simp [σ4, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ4, tableEquiv] <;> decide)
  have h5 := bound_shape42 H kind n σ5 {0, 1, 4, 5}
    (by ext x; fin_cases x <;> simp [σ5, tableEquiv, Fin.exists_fin_succ]) (by simp [σ5, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ5, tableEquiv] <;> decide)
  have h6 := bound_shape42 H kind n σ6 {0, 1, 3, 4}
    (by ext x; fin_cases x <;> simp [σ6, tableEquiv, Fin.exists_fin_succ]) (by simp [σ6, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ6, tableEquiv] <;> decide)
  have h7 := bound_shape42 H kind n σ7 {0, 2, 3, 5}
    (by ext x; fin_cases x <;> simp [σ7, tableEquiv, Fin.exists_fin_succ]) (by simp [σ7, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ7, tableEquiv] <;> decide)
  have h8 := bound_shape42 H kind n σ8 {0, 1, 2, 5}
    (by ext x; fin_cases x <;> simp [σ8, tableEquiv, Fin.exists_fin_succ]) (by simp [σ8, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ8, tableEquiv] <;> decide)
  have h9 := bound_shape42 H kind n σ9 {0, 1, 2, 3}
    (by ext x; fin_cases x <;> simp [σ9, tableEquiv, Fin.exists_fin_succ]) (by simp [σ9, tableEquiv])
    (by funext i; fin_cases i <;> simp [σ9, tableEquiv] <;> decide)
  have h10 := bound_shape6 H kind n
  linarith

end

section
-- source: FlowerTop/Port/P7/Assembly.lean
open WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {tt : Fin (2 * 3) → ℝ} {Creg : ℕ → ℝ} {Cr : ℝ}

/-- Pointwise (in the outer labels) bound of the six-tree sum. -/
theorem Y6_sum_norm_le_Wtot (H : PieceHyp C₀ P p N Rr k tt Creg) (hb : BoundNum P Creg Cr) (kind : TreeKind)
    (n : Fin (2 * 3) → (Fin P.d → ℤ)) :
    ‖∑ᶠ y ∈ Y6Set P p N kind,
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      Qn P p N Cr * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) * Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n := by
  refine (Y6_sum_norm_le H kind n).trans ?_
  set a : ℝ := 4 * P.Lambda (p + 1) with ha
  set G : ℝ := P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) with hG
  have hG0 : 0 ≤ G := Real.rpow_nonneg hb.hδ0.le _
  have h6 := Bound6_le' hb p N kind k n
  have h42 := fun σ => Bound42_le hb p N kind σ 0 k n
  have h24 := fun σ => Bound24_le hb p N kind σ k n
  have hC := hb.hCr0
  have hQ := Qn_pos P p N hC
  have hW42 : ∀ σ, 0 ≤ Wt42 P.L k a σ n := fun σ => mul_nonneg (prod_gw_nonneg _ _ _ _ _) (Wcp_nonneg _ _ _ _ _)
  have hWm : ∀ τ σ, 0 ≤ Wt24m P.L k a τ σ n := fun τ σ =>
    mul_nonneg (Wcp_nonneg _ _ _ _ _) (mul_nonneg (Wcp_nonneg _ _ _ _ _) (Wcp_nonneg _ _ _ _ _))
  have hWi : ∀ σ, 0 ≤ Wt24irr P.L k a σ n := fun σ => mul_nonneg (Wcp_nonneg _ _ _ _ _) (prod_gw_nonneg _ _ _ _ _)
  have hW6 : 0 ≤ Wt6 P.L k a n := prod_gw_nonneg _ _ _ _ _
  set M1 : ℕ := P.N (p + 1) + 1 with hM1
  have hc1 : (1 : ℝ) ≤ (((N + 1) * M1 ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hc3 : (1 : ℝ) ≤ (1 + Cr) ^ 3 := one_le_pow₀ (by linarith)
  have hc3' : (1 : ℝ) ≤ (1 + Cr) := by linarith
  have hQ6 : ((M1 : ℕ) : ℝ) ^ 6 ≤ Qn P p N Cr := by
    unfold Qn
    have h1 : ((M1 : ℕ) : ℝ) ^ 6 ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (0 : ℝ) ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) := by positivity
    calc _ ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) := h1
      _ ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) * (((N + 1) * M1 ^ 4 : ℕ) : ℝ) := le_mul_of_one_le_right h2 hc1
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hc3
  have hQ42 : (((N - 2 + 1) * (M1 ^ (2 * 2) * M1 ^ 2) : ℕ) : ℝ) * (1 + Cr) ≤ Qn P p N Cr := by
    unfold Qn
    have h1 : (((N - 2 + 1) * (M1 ^ (2 * 2) * M1 ^ 2) : ℕ) : ℝ) ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) := by
      have : (N - 2 + 1) * (M1 ^ (2 * 2) * M1 ^ 2) ≤ (N + 1) * M1 ^ 6 := by
        have : M1 ^ (2 * 2) * M1 ^ 2 = M1 ^ 6 := by rw [← pow_add]
        rw [this]; exact Nat.mul_le_mul_right _ (by omega)
      exact_mod_cast this
    calc _ ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) * (1 + Cr) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) * (1 + Cr) ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [sq_nonneg Cr]
      _ ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) * (((N + 1) * M1 ^ 4 : ℕ) : ℝ) * (1 + Cr) ^ 3 := by
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hc1) (by positivity)
  have hQ24 : (((N - 2 + 1) * (M1 ^ 2 * M1 ^ (2 * 2)) : ℕ) : ℝ) *
      ((((N + 1) * (M1 ^ 2 * M1 ^ 2) : ℕ) : ℝ) * (1 + Cr) ^ 3) ≤ Qn P p N Cr := by
    unfold Qn
    have h1 : (N - 2 + 1) * (M1 ^ 2 * M1 ^ (2 * 2)) ≤ (N + 1) * M1 ^ 6 := by
      have : M1 ^ 2 * M1 ^ (2 * 2) = M1 ^ 6 := by rw [← pow_add]
      rw [this]; exact Nat.mul_le_mul_right _ (by omega)
    have h2 : (N + 1) * (M1 ^ 2 * M1 ^ 2) ≤ (N + 1) * M1 ^ 4 := by
      have : M1 ^ 2 * M1 ^ 2 = M1 ^ 4 := by rw [← pow_add]
      rw [this]
    have h1' : (((N - 2 + 1) * (M1 ^ 2 * M1 ^ (2 * 2)) : ℕ) : ℝ) ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : (((N + 1) * (M1 ^ 2 * M1 ^ 2) : ℕ) : ℝ) ≤ (((N + 1) * M1 ^ 4 : ℕ) : ℝ) := by exact_mod_cast h2
    calc _ = (((N - 2 + 1) * (M1 ^ 2 * M1 ^ (2 * 2)) : ℕ) : ℝ) * (((N + 1) * (M1 ^ 2 * M1 ^ 2) : ℕ) : ℝ) *
          (1 + Cr) ^ 3 := by ring
      _ ≤ (((N + 1) * M1 ^ 6 : ℕ) : ℝ) * (((N + 1) * M1 ^ 4 : ℕ) : ℝ) * (1 + Cr) ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul h1' h2' (by positivity) (by positivity)
  have b6 : Bound6 P p N kind k n ≤ Qn P p N Cr * G * Wt6 P.L k a n := by
    refine h6.trans ?_
    calc _ = ((M1 : ℕ) : ℝ) ^ 6 * (G * Wt6 P.L k a n) := rfl
      _ ≤ Qn P p N Cr * (G * Wt6 P.L k a n) := mul_le_mul_of_nonneg_right hQ6 (mul_nonneg hG0 hW6)
      _ = _ := by ring
  have b42 : ∀ σ, Bound42 P p N kind σ 0 Creg k n ≤ Qn P p N Cr * G * Wt42 P.L k a σ n := by
    intro σ
    refine (h42 σ).trans ?_
    calc _ = ((((N - 2 + 1) * (M1 ^ (2 * 2) * M1 ^ 2) : ℕ) : ℝ) * (1 + Cr)) * (G * Wt42 P.L k a σ n) := by ring
      _ ≤ Qn P p N Cr * (G * Wt42 P.L k a σ n) := mul_le_mul_of_nonneg_right hQ42 (mul_nonneg hG0 (hW42 σ))
      _ = _ := by ring
  have b24 : ∀ σ, Bound24 P p N kind σ Creg k n ≤ Qn P p N Cr * G *
      (Wt24m P.L k a τ1 σ n + Wt24m P.L k a τ2 σ n + Wt24irr P.L k a σ n) := by
    intro σ
    refine (h24 σ).trans ?_
    have hs : 0 ≤ Wt24m P.L k a τ1 σ n + Wt24m P.L k a τ2 σ n + Wt24irr P.L k a σ n :=
      add_nonneg (add_nonneg (hWm _ _) (hWm _ _)) (hWi _)
    calc _ = ((((N - 2 + 1) * (M1 ^ 2 * M1 ^ (2 * 2)) : ℕ) : ℝ) *
          ((((N + 1) * (M1 ^ 2 * M1 ^ 2) : ℕ) : ℝ) * (1 + Cr) ^ 3)) *
          (G * (Wt24m P.L k a τ1 σ n + Wt24m P.L k a τ2 σ n + Wt24irr P.L k a σ n)) := by ring
      _ ≤ Qn P p N Cr * (G * (Wt24m P.L k a τ1 σ n + Wt24m P.L k a τ2 σ n + Wt24irr P.L k a σ n)) :=
          mul_le_mul_of_nonneg_right hQ24 (mul_nonneg hG0 hs)
      _ = _ := by ring
  have := b42 σ4; have := b42 σ5; have := b42 σ6; have := b42 σ7; have := b42 σ8; have := b42 σ9
  have := b24 σ1; have := b24 σ2; have := b24 σ3
  unfold Wtot
  nlinarith

/-- **The decapitation bound.** `‖coupleSum … true‖` is at most `c² · Qn · δ^{2ν(N-2)}` times the outer-label lattice
sum `16 · 3 · 3^{4Λ} ⟨k⟩^{-4Λ} (max 1 ∑ gw)^6`. -/
theorem coupleSum_true_norm_le {t : ℝ} (H : PieceHyp C₀ P p N Rr k (fun _ => t) Creg) (hb : BoundNum P Creg Cr) (kind : TreeKind)
    (hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1)) :
    ‖coupleSum P (inputsF P Rr) p N kind true t k‖ ≤
      (coupling P.d P.L P.γ P.δ) ^ 2 * (Qn P p N Cr * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) *
        (16 * (3 * (3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * jbr k ^ (-(4 * (P.Lambda (p + 1) : ℝ)))) *
          (max 1 (∑' m, gw P.L k (4 * P.Lambda (p + 1) : ℝ) m)) ^ 6))) := by
  rw [coupleSum_true_Y6 P (inputsF P Rr) p N kind t k H.hF, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  set G : ℝ := P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) with hG
  have hG0 : 0 ≤ G := Real.rpow_nonneg hb.hδ0.le _
  have hQ0 : 0 ≤ Qn P p N Cr := by linarith [Qn_pos P p N hb.hCr0]
  set g : OuterLabels P.d → ℝ := fun n => Qn P p N Cr * G * Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n.1 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg (mul_nonneg hQ0 hG0) (Wtot_nonneg _ _ _ _)
  set B : ℝ := Qn P p N Cr * G * (16 * (3 * (3 ^ (4 * (P.Lambda (p + 1) : ℝ)) *
    jbr k ^ (-(4 * (P.Lambda (p + 1) : ℝ)))) * (max 1 (∑' m, gw P.L k (4 * P.Lambda (p + 1) : ℝ) m)) ^ 6)) with hB
  have hpart : ∀ u : Finset (OuterLabels P.d), ∑ n ∈ u, g n ≤ B := by
    intro u
    simp only [hg]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Wtot_sum_le hb.hL k hΛ u) (mul_nonneg hQ0 hG0)
  have hs : Summable g := summable_of_sum_le hg0 hpart
  refine (tsum_of_norm_bounded hs.hasSum fun n => ?_).trans (Real.tsum_le_of_sum_le hg0 hpart)
  rw [norm_mul]
  calc ‖outerWeight P.L P.γ P.δ k t n.1‖ * ‖∑ᶠ y ∈ Y6Set P p N kind,
          kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0‖
      ≤ 1 * (Qn P p N Cr * G * Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n.1) :=
        mul_le_mul (norm_outerWeight_le_one _ _ _ _ _ _) (Y6_sum_norm_le_Wtot H hb kind n.1)
          (norm_nonneg _) zero_le_one
    _ = g n := one_mul _

end

section
-- source: FlowerTop/Port/P7/Final.lean
open WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {t : ℝ} {Creg : ℕ → ℝ} {Cr : ℝ}

/-- **The `dt = true` couple bound, in the shape of `RegularCouplesDtAt`** (with the loss as a hypothesis on the
data counts): `‖coupleSum … true‖ ≤ ⟨k⟩^{-4Λ} L^{100d} δ^{2νN}`. -/
theorem coupleSum_true_bound (H : PieceHyp C₀ P p N Rr k (fun _ => t) Creg) (hb : BoundNum P Creg Cr) (kind : TreeKind)
    (hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1))
    (hLoss : Qn P p N Cr * 12 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * (Kd P.d * P.L ^ (P.d + 1)) ^ 6 ≤
      P.L ^ (100 * P.d : ℝ)) :
    ‖coupleSum P (inputsF P Rr) p N kind true t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
  refine (coupleSum_true_norm_le H hb kind hΛ).trans ?_
  set a : ℝ := 4 * P.Lambda (p + 1) with ha
  set G : ℝ := P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) with hG
  set J : ℝ := jbr k ^ (-a) with hJ
  set Mg : ℝ := max 1 (∑' m, gw P.L k a m) with hMg
  have hG0 : 0 ≤ G := Real.rpow_nonneg hb.hδ0.le _
  have hJ0 : 0 ≤ J := Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _
  have hQ := Qn_pos P p N hb.hCr0
  have h3 : (0 : ℝ) ≤ 3 ^ a := Real.rpow_nonneg (by norm_num) _
  have hKL : 1 ≤ Kd P.d * P.L ^ (P.d + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_Kd _) (one_le_pow₀ hb.hL)
  have hMg1 : Mg ≤ Kd P.d * P.L ^ (P.d + 1) :=
    max_le hKL (tsum_gw_le_Kd hb.hL k hΛ)
  have hMg0 : 0 ≤ Mg := le_trans zero_le_one (le_max_left _ _)
  have hMg6 : Mg ^ 6 ≤ (Kd P.d * P.L ^ (P.d + 1)) ^ 6 := pow_le_pow_left₀ hMg0 hMg1 6
  have hcsq := coupling_sq_le hb.hδ0 hb.hL hb.hγ
  have hX : 0 ≤ Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6)) := by
    have : 0 ≤ Mg ^ 6 := by positivity
    have : 0 ≤ Qn P p N Cr := by linarith
    positivity
  have hδG := delta_sq_mul_le hb N
  calc (coupling P.d P.L P.γ P.δ) ^ 2 * (Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6)))
      ≤ (P.δ ^ 2 / 4) * (Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6))) :=
        mul_le_mul_of_nonneg_right hcsq hX
    _ = (P.δ ^ 2 * G) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6) := by ring
    _ ≤ P.δ ^ (2 * P.ν * (N : ℝ)) * J * P.L ^ (100 * P.d : ℝ) := by
        have hL1 : Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6 ≤ P.L ^ (100 * P.d : ℝ) := by
          refine le_trans ?_ hLoss
          have : 0 ≤ Qn P p N Cr := by linarith
          have : 0 ≤ Qn P p N Cr * 12 * 3 ^ a := by positivity
          exact mul_le_mul_of_nonneg_left hMg6 this
        have hnn : 0 ≤ Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6 := by
          have : 0 ≤ Qn P p N Cr := by linarith
          positivity
        calc (P.δ ^ 2 * G) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6)
            ≤ (P.δ ^ (2 * P.ν * (N : ℝ))) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              exact mul_le_mul_of_nonneg_right hδG hJ0
          _ ≤ (P.δ ^ (2 * P.ν * (N : ℝ))) * J * P.L ^ (100 * P.d : ℝ) :=
              mul_le_mul_of_nonneg_left hL1 (mul_nonneg (Real.rpow_nonneg hb.hδ0.le _) hJ0)
    _ = _ := by ring

end

section
-- source: FlowerTop/Port/P7/FreeBound.lean
open WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset MeasureTheory
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {Creg : ℕ → ℝ} {Cr : ℝ}

theorem norm_freeIntegrand_sum_le
    (Hs : ∀ tt : Fin (2 * 3) → ℝ, (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) → PieceHyp C₀ P p N Rr k tt Creg)
    (hb : BoundNum P Creg Cr) (t : ℝ) (n : OuterLabels P.d) (s : Fin 2 → ℝ) :
    ‖∑ y ∈ (finite_Y6 P p N .L0).toFinset, freeIntegrand P.L P.γ P.δ (inputsF P Rr) y.1 p t k n s‖ ≤
      (rootDom p t).indicator (fun _ => Qn P p N Cr * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) *
        Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n.1) s := by
  by_cases hs : s ∈ rootDom p t
  · rw [Set.indicator_of_mem hs]
    have h1 : ∑ y ∈ (finite_Y6 P p N .L0).toFinset, freeIntegrand P.L P.γ P.δ (inputsF P Rr) y.1 p t k n s =
        ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ) *
          rootPhaseS P.L P.γ P.δ k s n.1 *
          ∑ᶠ y ∈ Y6Set P p N .L0, kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1)
            (fun b => s (jOf b.1.1)) k n.1 0 := by
      rw [← sum_toFinset_Y6, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold freeIntegrand
      rw [Set.indicator_of_mem hs]
    rw [h1, norm_mul, norm_mul, norm_rootPhaseS, mul_one]
    have he : ‖((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => abs_epsCoef_le_one _ _ _)
    have htt : ∀ j, (fun c : Fin (2 * 3) => s (jOf c)) j ∈ Set.Icc (p : ℝ) (p + 1) := fun j =>
      ⟨(hs (jOf j)).1.le, (hs (jOf j)).2.1.le⟩
    have hY := Y6_sum_norm_le_Wtot (Hs _ htt) hb .L0 n.1
    calc ‖((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ)‖ *
          ‖∑ᶠ y ∈ Y6Set P p N .L0, kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1)
            (fun b => s (jOf b.1.1)) k n.1 0‖
        ≤ 1 * (Qn P p N Cr * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) * Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n.1) :=
          mul_le_mul he hY (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem hs]
    have : ∀ y ∈ (finite_Y6 P p N .L0).toFinset,
        freeIntegrand P.L P.γ P.δ (inputsF P Rr) y.1 p t k n s = 0 := fun y _ => by
      unfold freeIntegrand; rw [Set.indicator_of_notMem hs]
    rw [Finset.sum_eq_zero this, norm_zero]

/-- **The decapitation bound for `kind = L0`, `dt = false`.** -/
theorem coupleSum_false_norm_le
    (Hs : ∀ tt : Fin (2 * 3) → ℝ, (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) → PieceHyp C₀ P p N Rr k tt Creg)
    (hb : BoundNum P Creg Cr) (t : ℝ) (hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1))
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L n)|) :
    ‖coupleSum P (inputsF P Rr) p N .L0 false t k‖ ≤
      (coupling P.d P.L P.γ P.δ) ^ 2 * (Qn P p N Cr * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) *
        (16 * (3 * (3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * jbr k ^ (-(4 * (P.Lambda (p + 1) : ℝ)))) *
          (max 1 (∑' m, gw P.L k (4 * P.Lambda (p + 1) : ℝ) m)) ^ 6))) := by
  rw [coupleSum_false_swap P (inputsF P Rr) p N t k hF, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  set G : ℝ := P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) with hG
  have hG0 : 0 ≤ G := Real.rpow_nonneg hb.hδ0.le _
  have hQ0 : 0 ≤ Qn P p N Cr := by linarith [Qn_pos P p N hb.hCr0]
  set g : OuterLabels P.d → ℝ := fun n => Qn P p N Cr * G * Wtot P.L k (4 * P.Lambda (p + 1) : ℝ) n.1 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg (mul_nonneg hQ0 hG0) (Wtot_nonneg _ _ _ _)
  set B : ℝ := Qn P p N Cr * G * (16 * (3 * (3 ^ (4 * (P.Lambda (p + 1) : ℝ)) *
    jbr k ^ (-(4 * (P.Lambda (p + 1) : ℝ)))) * (max 1 (∑' m, gw P.L k (4 * P.Lambda (p + 1) : ℝ) m)) ^ 6)) with hB
  have hpart : ∀ u : Finset (OuterLabels P.d), ∑ n ∈ u, g n ≤ B := by
    intro u
    simp only [hg]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Wtot_sum_le hb.hL k hΛ u) (mul_nonneg hQ0 hG0)
  have hs : Summable g := summable_of_sum_le hg0 hpart
  refine (tsum_of_norm_bounded hs.hasSum fun n => ?_).trans (Real.tsum_le_of_sum_le hg0 hpart)
  have hmeas := measurableSet_rootDom p t
  have hI : Integrable ((rootDom p t).indicator fun _ => g n) :=
    (integrable_indicator_iff hmeas).2 (integrableOn_const (volume_rootDom_lt_top p t).ne)
  calc ‖∫ s : Fin 2 → ℝ, ∑ y ∈ (finite_Y6 P p N .L0).toFinset,
          freeIntegrand P.L P.γ P.δ (inputsF P Rr) y.1 p t k n s‖
      ≤ ∫ s, (rootDom p t).indicator (fun _ => g n) s :=
        norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall fun s =>
          norm_freeIntegrand_sum_le Hs hb t n s)
    _ = (volume : Measure (Fin 2 → ℝ)).real (rootDom p t) * g n := by
        rw [integral_indicator_const _ hmeas, smul_eq_mul]
    _ ≤ g n := mul_le_of_le_one_left (hg0 n) (volume_rootDom_le p t)

end

section
-- source: FlowerTop/Port/P7/FinalFalse.lean
open WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {Creg : ℕ → ℝ} {Cr : ℝ}

/-- **The `kind = L0`, `dt = false` couple bound by decapitation** (loss as a hypothesis on the data counts):
`‖coupleSum … L0 false‖ ≤ ⟨k⟩^{-4Λ} L^{100d} δ^{2νN}`. -/
theorem coupleSum_false_bound
    (Hs : ∀ tt : Fin (2 * 3) → ℝ, (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) → PieceHyp C₀ P p N Rr k tt Creg)
    (hb : BoundNum P Creg Cr)
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L n)|) (t : ℝ)
    (hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1))
    (hLoss : Qn P p N Cr * 12 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * (Kd P.d * P.L ^ (P.d + 1)) ^ 6 ≤
      P.L ^ (100 * P.d : ℝ)) :
    ‖coupleSum P (inputsF P Rr) p N .L0 false t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
  refine (coupleSum_false_norm_le Hs hb t hΛ hF).trans ?_
  set a : ℝ := 4 * P.Lambda (p + 1) with ha
  set G : ℝ := P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) with hG
  set J : ℝ := jbr k ^ (-a) with hJ
  set Mg : ℝ := max 1 (∑' m, gw P.L k a m) with hMg
  have hG0 : 0 ≤ G := Real.rpow_nonneg hb.hδ0.le _
  have hJ0 : 0 ≤ J := Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _
  have hQ := Qn_pos P p N hb.hCr0
  have h3 : (0 : ℝ) ≤ 3 ^ a := Real.rpow_nonneg (by norm_num) _
  have hKL : 1 ≤ Kd P.d * P.L ^ (P.d + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_Kd _) (one_le_pow₀ hb.hL)
  have hMg1 : Mg ≤ Kd P.d * P.L ^ (P.d + 1) :=
    max_le hKL (tsum_gw_le_Kd hb.hL k hΛ)
  have hMg0 : 0 ≤ Mg := le_trans zero_le_one (le_max_left _ _)
  have hMg6 : Mg ^ 6 ≤ (Kd P.d * P.L ^ (P.d + 1)) ^ 6 := pow_le_pow_left₀ hMg0 hMg1 6
  have hcsq := coupling_sq_le hb.hδ0 hb.hL hb.hγ
  have hX : 0 ≤ Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6)) := by
    have : 0 ≤ Mg ^ 6 := by positivity
    have : 0 ≤ Qn P p N Cr := by linarith
    positivity
  have hδG := delta_sq_mul_le hb N
  calc (coupling P.d P.L P.γ P.δ) ^ 2 * (Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6)))
      ≤ (P.δ ^ 2 / 4) * (Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6))) :=
        mul_le_mul_of_nonneg_right hcsq hX
    _ = (P.δ ^ 2 * G) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6) := by ring
    _ ≤ P.δ ^ (2 * P.ν * (N : ℝ)) * J * P.L ^ (100 * P.d : ℝ) := by
        have hL1 : Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6 ≤ P.L ^ (100 * P.d : ℝ) := by
          refine le_trans ?_ hLoss
          have : 0 ≤ Qn P p N Cr := by linarith
          have : 0 ≤ Qn P p N Cr * 12 * 3 ^ a := by positivity
          exact mul_le_mul_of_nonneg_left hMg6 this
        have hnn : 0 ≤ Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6 := by
          have : 0 ≤ Qn P p N Cr := by linarith
          positivity
        calc (P.δ ^ 2 * G) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6)
            ≤ (P.δ ^ (2 * P.ν * (N : ℝ))) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              exact mul_le_mul_of_nonneg_right hδG hJ0
          _ ≤ (P.δ ^ (2 * P.ν * (N : ℝ))) * J * P.L ^ (100 * P.d : ℝ) :=
              mul_le_mul_of_nonneg_left hL1 (mul_nonneg (Real.rpow_nonneg hb.hδ0.le _) hJ0)
    _ = _ := by ring

end

section
-- source: FlowerTop/Port/P7/Adapter.lean
open WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {t : ℝ} {Creg : ℕ → ℝ}

/-- `PieceHyp` from LG-SPINE's numerics. -/
def PieceHyp.mkOf (G : LGContext C₀ P) (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) (ht : t ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) : PieceHyp C₀ P p N Rr k (fun _ => t) Creg where
  G := G
  hp := hp
  hN := hN
  hRr := hRr
  hR1 := hR1
  hmmax := by omega
  htt := fun _ => ht
  hF := hF
  hnum6 := fun N' hN' => hGN 3 N' (by norm_num) (by omega) hN'
  hnumA := fun N' hN' => hGN 2 N' (by norm_num) (by omega) hN'
  hnumC := hCN
  hreg := hreg

theorem boundNum_of (G : LGContext C₀ P) (hγ : P.γ ≤ P.d) {Cr : ℝ} (hCr : 0 ≤ Cr)
    (hCreg : ∀ e, Creg e ≤ Cr) (hCreg0 : ∀ e, 0 ≤ Creg e) : BoundNum P Creg Cr where
  hδ0 := G.hs.delta_pos
  hδ1 := G.hs.delta_le
  hL := by linarith [G.hs.L_ge]
  hν := G.hs.nu_pos.le
  hν8 := by linarith [G.hs.nu_small, G.hs.nu_pos]
  hCr0 := hCr
  hCreg := hCreg
  hCreg0 := hCreg0
  hγ := hγ

/-- **The `dt = true` total couple bound over LG-SPINE's gates** (the content of `RegularCouplesDtAt` and of
`CoupleStage1At` for `dt = true`): `‖coupleSum … true‖ ≤ ⟨k⟩^{-4Λ(p+1)} L^{100 d} δ^{2νN}`, with `kind` arbitrary. -/
theorem coupleSum_true_total (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) {t : ℝ} (ht : t ∈ Set.Icc (p : ℝ) (p + 1)) (k : Mom P.d) (kind : TreeKind)
    (hγ : P.γ ≤ P.d) (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (H : RegPremises P (inputsF P Rr) p)
    (hE : (12 * 2 ^ 12 * (1 + H.Creg) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log P.L ^ (12 * logExp P) ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1))) :
    ‖coupleSum P (inputsF P Rr) p N kind true t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
  have hL1 : 1 ≤ P.L := by linarith [G.hs.L_ge]
  set H'' : RegPremises P (inputsF P (truncR Rr p)) p := H.of_trunc Rr rfl with hH''
  have hCreg : H''.Creg = H.Creg := rfl
  have hF := summable_inputsF_truncR P Rr G.hd hL1 hp.le hRr k
  have hreg := H''.bound
  have PH := PieceHyp.mkOf (N := N) (k := k) (t := t) G hp hN (remainderBound_truncR P Rr p hL1 hRr) hR1 ht hF hGN hCN hreg
  have hCr0 : 0 ≤ H.Creg := by linarith [H.creg_pos]
  have hb : BoundNum P (fun _ => H''.Creg) H.Creg :=
    boundNum_of G hγ hCr0 (fun _ => hCreg.le) (fun _ => by rw [hCreg]; exact hCr0)
  have hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1) := by
    have := forty_dim_le_Lambda P G.hd (show p + 1 ≤ P.D by omega)
    have h1 : (P.d : ℝ) + 1 ≤ 40 * P.d := by
      have : (1 : ℝ) ≤ P.d := by exact_mod_cast G.hd
      linarith
    have h2 : ((40 * P.d : ℕ) : ℝ) ≤ P.Lambda (p + 1) := by exact_mod_cast this
    push_cast at h2
    linarith
  have hLoss := hLoss_of_numerics P G.hd G.hlog hL1 p N hN hCr0 hE
  rw [coupleSum_congr P (inputsF P Rr) (inputsF P (truncR Rr p)) p N kind true t k
    (fun q hq => (inputsF_truncR P Rr p hq).symm)]
  exact coupleSum_true_bound PH hb kind hΛ hLoss

end

section
-- source: FlowerTop/Port/P7/AdapterFalse.lean
open WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {Creg : ℕ → ℝ}

/-- `PieceHyp` from LG-SPINE's numerics, with arbitrary per-tree caps. -/
def PieceHyp.mkOfTT (G : LGContext C₀ P) (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) (tt : Fin (2 * 3) → ℝ) (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) : PieceHyp C₀ P p N Rr k tt Creg where
  G := G
  hp := hp
  hN := hN
  hRr := hRr
  hR1 := hR1
  hmmax := by omega
  htt := htt
  hF := hF
  hnum6 := fun N' hN' => hGN 3 N' (by norm_num) (by omega) hN'
  hnumA := fun N' hN' => hGN 2 N' (by norm_num) (by omega) hN'
  hnumC := hCN
  hreg := hreg

/-- **The `kind = L0`, `dt = false` total couple bound over LG-SPINE's gates** (the content of `CoupleStage1At` for
`dt = false`; the regular part is the two-time family bound `regular_family_pointwise2`):
`‖coupleSum … L0 false‖ ≤ ⟨k⟩^{-4Λ(p+1)} L^{100 d} δ^{2νN}`. -/
theorem coupleSum_false_total (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) (t : ℝ) (k : Mom P.d)
    (hγ : P.γ ≤ P.d) (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (H : RegPremises P (inputsF P Rr) p)
    (hE : (12 * 2 ^ 12 * (1 + H.Creg) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log P.L ^ (12 * logExp P) ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1))) :
    ‖coupleSum P (inputsF P Rr) p N .L0 false t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
  have hL1 : 1 ≤ P.L := by linarith [G.hs.L_ge]
  set H'' : RegPremises P (inputsF P (truncR Rr p)) p := H.of_trunc Rr rfl with hH''
  have hCreg : H''.Creg = H.Creg := rfl
  have hF := summable_inputsF_truncR P Rr G.hd hL1 hp.le hRr k
  have hreg := H''.bound
  have Hs : ∀ tt : Fin (2 * 3) → ℝ, (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
      PieceHyp C₀ P p N (truncR Rr p) k tt (fun _ => H''.Creg) := fun tt htt =>
    PieceHyp.mkOfTT (N := N) (k := k) G hp hN (remainderBound_truncR P Rr p hL1 hRr) hR1 tt htt hF hGN hCN hreg
  have hCr0 : 0 ≤ H.Creg := by linarith [H.creg_pos]
  have hb : BoundNum P (fun _ => H''.Creg) H.Creg :=
    boundNum_of G hγ hCr0 (fun _ => hCreg.le) (fun _ => by rw [hCreg]; exact hCr0)
  have hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1) := by
    have := forty_dim_le_Lambda P G.hd (show p + 1 ≤ P.D by omega)
    have h1 : (P.d : ℝ) + 1 ≤ 40 * P.d := by
      have : (1 : ℝ) ≤ P.d := by exact_mod_cast G.hd
      linarith
    have h2 : ((40 * P.d : ℕ) : ℝ) ≤ P.Lambda (p + 1) := by exact_mod_cast this
    push_cast at h2
    linarith
  have hLoss := hLoss_of_numerics P G.hd G.hlog hL1 p N hN hCr0 hE
  rw [coupleSum_congr P (inputsF P Rr) (inputsF P (truncR Rr p)) p N .L0 false t k
    (fun q hq => (inputsF_truncR P Rr p hq).symm)]
  exact coupleSum_false_bound Hs hb hF t hΛ hLoss

end

section
-- source: FlowerTop/Port/P7/Export.lean
open WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

/-- **`coupleSum` bound for every admissible `(kind, dt)`** (`kind = tr → dt = true`), by decapitation:
`‖coupleSum P (inputsF P Rr) p N kind dt t k‖ ≤ ⟨k⟩^{-4Λ(p+1)} L^{100 d} δ^{ν N}` (even `δ^{2νN}`).
It replaces both `RegularCouplesAt` and `CoupleStage1At` inside `couple_clause_bound`: the regular/nonregular split
does not factor over the components of the decapitation (a nonregular couple can decapitate into three regular
couples), so the TOTAL sum is bounded, regular components by the family bound of FLOWER-REG
(`regular_family_pointwise2`, two-time port) and the nonregular ones by LG-SPINE's slice estimates. -/
theorem coupleSum_total_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) {t : ℝ} (ht : t ∈ Set.Ioo (p : ℝ) (p + 1)) (k : Mom P.d)
    (kind : TreeKind) (dt : Bool) (hkdt : kind = .tr → dt = true)
    (hγ : P.γ ≤ P.d) (hGN : GardenNum P G.Cφ p) (hCN : CoupleNum P G.Cφ p)
    (H : RegPremises P (inputsF P Rr) p)
    (hE : (12 * 2 ^ 12 * (1 + H.Creg) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log P.L ^ (12 * logExp P) ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1))) :
    ‖coupleSum P (inputsF P Rr) p N kind dt t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * (N : ℝ)) := by
  have hδ0 := G.hs.delta_pos
  have hδ1 := G.hs.delta_le
  have hν := G.hs.nu_pos.le
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpow : P.δ ^ (2 * P.ν * (N : ℝ)) ≤ P.δ ^ (P.ν * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by nlinarith)
  have hj : 0 ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _) (Real.rpow_nonneg (by linarith [G.hs.L_ge]) _)
  have key : ‖coupleSum P (inputsF P Rr) p N kind dt t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
    cases dt with
    | true => exact coupleSum_true_total C₀ P G hp Rr hRr hR1 hN ⟨ht.1.le, ht.2.le⟩ k kind hγ hGN hCN H hE
    | false =>
      have hk : kind = .L0 := by
        cases kind with
        | tr => exact absurd (hkdt rfl) (by simp)
        | L0 => rfl
      subst hk
      exact coupleSum_false_total C₀ P G hp Rr hRr hR1 hN t k hγ hGN hCN H hE
  exact key.trans (mul_le_mul_of_nonneg_left hpow hj)

end

end WaveTurbulence.GammaLow.LGLow.CC
