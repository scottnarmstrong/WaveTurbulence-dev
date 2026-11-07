/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.LatticeTotal
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.TotalAssembly
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.BoundPieces
/-! FLOWER-P7: the norm of `coupleSum … true` is bounded by the summed piece bounds (the outer-label sum). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

theorem abs_epsCoef_le_one {d : ℕ} (x y z : Fin d → ℤ) : |epsCoef x y z| ≤ 1 := by
  unfold epsCoef; split_ifs <;> simp

theorem norm_rootPhase {d : ℕ} (L γ δ : ℝ) (k : Mom d) (t : ℝ) (n : Fin (2 * 3) → (Fin d → ℤ)) :
    ‖rootPhase L γ δ k t n‖ = 1 := by
  unfold rootPhase
  rw [norm_prod]
  exact Finset.prod_eq_one fun j _ => Complex.norm_exp_ofReal_mul_I _

theorem norm_outerWeight_le_one {d : ℕ} (L γ δ : ℝ) (k : Mom d) (t : ℝ) (n : Fin (2 * 3) → (Fin d → ℤ)) :
    ‖outerWeight L γ δ k t n‖ ≤ 1 := by
  unfold outerWeight
  rw [norm_mul, norm_rootPhase, mul_one, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => abs_epsCoef_le_one _ _ _)

/-- The data-count constant. -/
noncomputable def Qn (P : WTParams) (p N : ℕ) (Cr : ℝ) : ℝ :=
  (((N + 1) * (P.N (p + 1) + 1) ^ 6 : ℕ) : ℝ) * (((N + 1) * (P.N (p + 1) + 1) ^ 4 : ℕ) : ℝ) * (1 + Cr) ^ 3

theorem Qn_pos (P : WTParams) (p N : ℕ) {Cr : ℝ} (hC : 0 ≤ Cr) : 1 ≤ Qn P p N Cr := by
  unfold Qn
  have h1 : (1 : ℝ) ≤ (((N + 1) * (P.N (p + 1) + 1) ^ 6 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : (1 : ℝ) ≤ (((N + 1) * (P.N (p + 1) + 1) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have h3 : (1 : ℝ) ≤ (1 + Cr) ^ 3 := one_le_pow₀ (by linarith)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3

section
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

theorem Wtot_nonneg {d : ℕ} (L : ℝ) (k : Mom d) (a : ℝ) (n : Fin (2 * 3) → Fin d → ℤ) : 0 ≤ Wtot L k a n := by
  have h42 : ∀ σ, 0 ≤ Wt42 L k a σ n := fun σ => mul_nonneg (prod_gw_nonneg _ _ _ _ _) (Wcp_nonneg _ _ _ _ _)
  have hm : ∀ τ σ, 0 ≤ Wt24m L k a τ σ n := fun τ σ =>
    mul_nonneg (Wcp_nonneg _ _ _ _ _) (mul_nonneg (Wcp_nonneg _ _ _ _ _) (Wcp_nonneg _ _ _ _ _))
  have hi : ∀ σ, 0 ≤ Wt24irr L k a σ n := fun σ => mul_nonneg (Wcp_nonneg _ _ _ _ _) (prod_gw_nonneg _ _ _ _ _)
  have h6 : 0 ≤ Wt6 L k a n := prod_gw_nonneg _ _ _ _ _
  unfold Wtot
  have := h42 σ4; have := h42 σ5; have := h42 σ6; have := h42 σ7; have := h42 σ8; have := h42 σ9
  have := hm τ1 σ1; have := hm τ2 σ1; have := hi σ1; have := hm τ1 σ2; have := hm τ2 σ2; have := hi σ2
  have := hm τ1 σ3; have := hm τ2 σ3; have := hi σ3
  linarith

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

end WaveTurbulence.FlowerP7
