/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.BoundWeights
/-! FLOWER-P7: the three piece bounds in weight form. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

theorem term_le (A Lp Xd cf R : ℝ) (hA : 0 ≤ A) (hLp1 : Lp ≤ 1) (hLp0 : 0 ≤ Lp) (hXd : 0 ≤ Xd)
    (hcf : cf ≤ R) (hcf0 : 0 ≤ cf) : (A * Lp * Xd) * cf ≤ (A * Xd) * R := by
  have h1 : A * Lp * Xd ≤ A * Xd := by
    have : A * Lp ≤ A := mul_le_of_le_one_right hA hLp1
    exact mul_le_mul_of_nonneg_right this hXd
  exact mul_le_mul h1 hcf hcf0 (mul_nonneg hA hXd)

section
variable {P : WTParams} {Creg : ℕ → ℝ} {Cr : ℝ}

theorem Lpow2_le_one (hb : BoundNum P Creg Cr) : P.L ^ (-(((2 : ℕ) : ℝ) - 1) / 4) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hb.hL (by norm_num)

theorem Lpow3_le_one (hb : BoundNum P Creg Cr) : P.L ^ (-(((3 : ℕ) : ℝ) - 1) / 4) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hb.hL (by norm_num)

theorem delta_sum (hb : BoundNum P Creg Cr) {x y : ℕ} {N : ℕ} (h : x + y + 2 = N) :
    P.δ ^ (2 * P.ν * (x : ℝ)) * P.δ ^ (2 * P.ν * (y : ℝ)) = P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) := by
  rw [delta_pow_mul hb.hδ0, ← mul_add]
  congr 2
  have : N - 2 = x + y := by omega
  rw [this]; push_cast; ring

theorem Bound6_le' (hb : BoundNum P Creg Cr) (p N : ℕ) (kind : TreeKind) (k : Mom P.d)
    (n : Fin (2 * 3) → (Fin P.d → ℤ)) :
    Bound6 P p N kind k n ≤ ((P.N (p + 1) + 1 : ℕ) : ℝ) ^ 6 *
      (P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) * Wt6 P.L k (4 * P.Lambda (p + 1) : ℝ) n) := by
  refine (Bound6_le P p N kind k n hb.hδ0 (by linarith [hb.hL])).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Wt6, ← jbrProdAt_rpow]
  have hX : 0 ≤ P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) := Real.rpow_nonneg hb.hδ0.le _
  have hJ : 0 ≤ jbrProdAt P.L k n ^ (-(4 * (P.Lambda (p + 1) : ℝ))) := Real.rpow_nonneg
    (Finset.prod_nonneg fun j _ => (WaveTurbulence.Induct.jbr_pos _).le) _
  have := Lpow3_le_one hb
  nlinarith [mul_nonneg hJ hX]

open scoped Classical in
theorem Bound42_le (hb : BoundNum P Creg Cr) (p N : ℕ) (kind : TreeKind)
    (σ : Fin (2 * 2) ⊕ Fin 2 ≃ Fin (2 * 3)) (i0 : Fin (2 * 2)) (k : Mom P.d)
    (n : Fin (2 * 3) → (Fin P.d → ℤ)) :
    Bound42 P p N kind σ i0 Creg k n ≤
      (((N - 2 + 1) * ((P.N (p + 1) + 1) ^ (2 * 2) * (P.N (p + 1) + 1) ^ 2) : ℕ) : ℝ) *
        ((1 + Cr) * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) * Wt42 P.L k (4 * P.Lambda (p + 1) : ℝ) σ n) := by
  unfold Bound42
  have hW : 0 ≤ Wt42 P.L k (4 * P.Lambda (p + 1) : ℝ) σ n :=
    mul_nonneg (prod_gw_nonneg _ _ _ _ _) (Wcp_nonneg _ _ _ _ _)
  have hT : 0 ≤ (1 + Cr) * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) * Wt42 P.L k (4 * P.Lambda (p + 1) : ℝ) σ n := by
    have := Real.rpow_nonneg hb.hδ0.le (2 * P.ν * ((N - 2 : ℕ) : ℝ))
    have := hb.hCr0
    positivity
  refine sum_pairs_le _ _ (Joint1 P p N kind σ) (N - 2) (P.N (p + 1)) ?_ _ _ hT ?_
  · intro x y hJ
    obtain ⟨h1, h2⟩ := hJ
    obtain ⟨h3, h4⟩ := entries_of_glueKindOK σ x.2 y.2 h2
    exact ⟨by omega, h3, h4⟩
  · intro x y hJ
    obtain ⟨h1, h2⟩ := hJ
    have hcf := cplFactor_le hb p y.1 (n (σ (.inr 0))) (n (σ (.inr 1))) k
    have hcf0 := cplFactor_nonneg hb p y.1 (n (σ (.inr 0))) (n (σ (.inr 1))) k
    have hA : 0 ≤ jbrProdAt P.L k (fun i => n (σ (.inl i))) ^ (-(4 * (P.Lambda (p + 1) : ℝ))) :=
      Real.rpow_nonneg (Finset.prod_nonneg fun j _ => (WaveTurbulence.Induct.jbr_pos _).le) _
    have hY := Real.rpow_nonneg hb.hδ0.le (2 * P.ν * (y.1 : ℝ))
    have hX := Real.rpow_nonneg hb.hδ0.le (2 * P.ν * (x.1 : ℝ))
    have hWc := Wcp_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) (n (σ (.inr 0))) (n (σ (.inr 1)))
    have hC := hb.hCr0
    have key := term_le _ _ _ _ _ hA (Lpow2_le_one hb) (Real.rpow_nonneg (by linarith [hb.hL]) _) hX hcf hcf0
    refine key.trans (le_of_eq ?_)
    rw [Wt42, ← delta_sum hb h1, ← jbrProdAt_rpow]
    ring

open scoped Classical in
theorem PieceBound2_le (hb : BoundNum P Creg Cr) (p N : ℕ) (τ : Fin 2 ⊕ Fin 2 ≃ Fin (2 * 2))
    (ζ : Fin (2 * 2) → ℤˣ) (e : ℕ × (Fin (2 * 2) → ℕ)) (nB : Fin (2 * 2) → Fin P.d → ℤ) (k : Mom P.d)
    (he : ∀ i, e.2 i ≤ P.N (p + 1)) :
    PieceBound2 P p N τ ζ e Creg nB k ≤
      (((e.1 + 1) * ((P.N (p + 1) + 1) ^ 2 * (P.N (p + 1) + 1) ^ 2) : ℕ) : ℝ) *
        ((1 + Cr) ^ 2 * P.δ ^ (2 * P.ν * (e.1 : ℝ)) *
          (Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ (.inl 0))) (nB (τ (.inl 1))) *
            Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ (.inr 0))) (nB (τ (.inr 1))))) := by
  unfold PieceBound2
  have hW : 0 ≤ Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ (.inl 0))) (nB (τ (.inl 1))) *
            Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ (.inr 0))) (nB (τ (.inr 1))) :=
    mul_nonneg (Wcp_nonneg _ _ _ _ _) (Wcp_nonneg _ _ _ _ _)
  have hT : 0 ≤ (1 + Cr) ^ 2 * P.δ ^ (2 * P.ν * (e.1 : ℝ)) *
          (Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ (.inl 0))) (nB (τ (.inl 1))) *
            Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ (.inr 0))) (nB (τ (.inr 1)))) := by
    have := Real.rpow_nonneg hb.hδ0.le (2 * P.ν * (e.1 : ℝ))
    have := hb.hCr0
    positivity
  refine sum_pairs_le _ _ (Joint2 τ e) e.1 (P.N (p + 1)) ?_ _ _ hT ?_
  · intro x y hJ
    obtain ⟨h1, h2⟩ := hJ
    refine ⟨h1, fun i => ?_, fun i => ?_⟩
    · have := he (τ (.inl i)); rw [← h2, glueVec_inl] at this; exact this
    · have := he (τ (.inr i)); rw [← h2, glueVec_inr] at this; exact this
  · intro x y hJ
    obtain ⟨h1, h2⟩ := hJ
    have h3 := cplFactor_le hb p x.1 (nB (τ (.inl 0))) (nB (τ (.inl 1))) k
    have h4 := cplFactor_le hb p y.1 (nB (τ (.inr 0))) (nB (τ (.inr 1))) k
    have h3' := cplFactor_nonneg hb p x.1 (nB (τ (.inl 0))) (nB (τ (.inl 1))) k
    have h4' := cplFactor_nonneg hb p y.1 (nB (τ (.inr 0))) (nB (τ (.inr 1))) k
    have hm := mul_le_mul h3 h4 h4' (by
      have := Real.rpow_nonneg hb.hδ0.le (2 * P.ν * (x.1 : ℝ))
      have := hb.hCr0
      have := Wcp_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ (.inl 0))) (nB (τ (.inl 1)))
      positivity)
    refine hm.trans (le_of_eq ?_)
    have hd := delta_sum hb (x := x.1) (y := y.1) (N := e.1 + 2) (by omega)
    simp only [Nat.add_sub_cancel] at hd
    have hxy : P.δ ^ (2 * P.ν * (e.1 : ℝ)) = P.δ ^ (2 * P.ν * (x.1 : ℝ)) * P.δ ^ (2 * P.ν * (y.1 : ℝ)) := by
      rw [hd, ← h1]
    rw [hxy]
    ring

theorem alg24 (c Ce Ye W1 W2 Wi P1 P2 I : ℝ) (hc : 1 ≤ c) (hCe : 1 ≤ Ce) (hY : 0 ≤ Ye) (hWi : 0 ≤ Wi)
    (hP1 : P1 ≤ c * (Ce * Ye * W1)) (hP2 : P2 ≤ c * (Ce * Ye * W2)) (hI : I ≤ Ye * Wi) :
    P1 + P2 + I ≤ c * (Ce * Ye * (W1 + W2 + Wi)) := by
  have h1 : 1 ≤ c * Ce := one_le_mul_of_one_le_of_one_le hc hCe
  have h2 : Ye * Wi ≤ c * (Ce * Ye * Wi) := by
    have := mul_nonneg hY hWi
    nlinarith
  nlinarith

open scoped Classical in
theorem Bound24_le (hb : BoundNum P Creg Cr) (p N : ℕ) (kind : TreeKind)
    (σ : Fin 2 ⊕ Fin (2 * 2) ≃ Fin (2 * 3)) (k : Mom P.d) (n : Fin (2 * 3) → (Fin P.d → ℤ)) :
    Bound24 P p N kind σ Creg k n ≤
      (((N - 2 + 1) * ((P.N (p + 1) + 1) ^ 2 * (P.N (p + 1) + 1) ^ (2 * 2)) : ℕ) : ℝ) *
        ((((N + 1) * ((P.N (p + 1) + 1) ^ 2 * (P.N (p + 1) + 1) ^ 2) : ℕ) : ℝ) *
          ((1 + Cr) ^ 3 * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) *
            (Wt24m P.L k (4 * P.Lambda (p + 1) : ℝ) τ1 σ n + Wt24m P.L k (4 * P.Lambda (p + 1) : ℝ) τ2 σ n +
              Wt24irr P.L k (4 * P.Lambda (p + 1) : ℝ) σ n))) := by
  unfold Bound24
  set c2 : ℝ := (((N + 1) * ((P.N (p + 1) + 1) ^ 2 * (P.N (p + 1) + 1) ^ 2) : ℕ) : ℝ) with hc2
  have hc2one : 1 ≤ c2 := by
    rw [hc2]
    have : 1 ≤ (N + 1) * ((P.N (p + 1) + 1) ^ 2 * (P.N (p + 1) + 1) ^ 2) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hW : 0 ≤ Wt24m P.L k (4 * P.Lambda (p + 1) : ℝ) τ1 σ n + Wt24m P.L k (4 * P.Lambda (p + 1) : ℝ) τ2 σ n +
              Wt24irr P.L k (4 * P.Lambda (p + 1) : ℝ) σ n := by
    have h1 : ∀ τ, 0 ≤ Wt24m P.L k (4 * P.Lambda (p + 1) : ℝ) τ σ n := fun τ =>
      mul_nonneg (Wcp_nonneg _ _ _ _ _) (mul_nonneg (Wcp_nonneg _ _ _ _ _) (Wcp_nonneg _ _ _ _ _))
    have h2 : 0 ≤ Wt24irr P.L k (4 * P.Lambda (p + 1) : ℝ) σ n :=
      mul_nonneg (Wcp_nonneg _ _ _ _ _) (prod_gw_nonneg _ _ _ _ _)
    linarith [h1 τ1, h1 τ2]
  have hδN := Real.rpow_nonneg hb.hδ0.le (2 * P.ν * ((N - 2 : ℕ) : ℝ))
  have hC := hb.hCr0
  have hc20 : 0 ≤ c2 := by linarith
  have hT : 0 ≤ c2 * ((1 + Cr) ^ 3 * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) *
            (Wt24m P.L k (4 * P.Lambda (p + 1) : ℝ) τ1 σ n + Wt24m P.L k (4 * P.Lambda (p + 1) : ℝ) τ2 σ n +
              Wt24irr P.L k (4 * P.Lambda (p + 1) : ℝ) σ n)) := by positivity
  refine sum_pairs_le _ _ (Joint1 P p N kind σ) (N - 2) (P.N (p + 1)) ?_ _ _ hT ?_
  · intro x y hJ
    obtain ⟨h1, h2⟩ := hJ
    obtain ⟨h3, h4⟩ := entries_of_glueKindOK σ x.2 y.2 h2
    exact ⟨by omega, h3, h4⟩
  · intro x y hJ
    obtain ⟨h1, h2⟩ := hJ
    obtain ⟨h3, h4⟩ := entries_of_glueKindOK σ x.2 y.2 h2
    set nB : Fin (2 * 2) → Fin P.d → ℤ := fun i => n (σ (.inr i)) with hnB
    have hcA := cplFactor_le hb p x.1 (n (σ (.inl 0))) (n (σ (.inl 1))) k
    have hcA0 := cplFactor_nonneg hb p x.1 (n (σ (.inl 0))) (n (σ (.inl 1))) k
    have hP1 := PieceBound2_le hb p N τ1 (fun i => childSig (σ (.inr i))) y nB k h4
    have hP2 := PieceBound2_le hb p N τ2 (fun i => childSig (σ (.inr i))) y nB k h4
    have hcnt : ((((y.1 + 1) * ((P.N (p + 1) + 1) ^ 2 * (P.N (p + 1) + 1) ^ 2) : ℕ)) : ℝ) ≤ c2 := by
      rw [hc2]; exact_mod_cast Nat.mul_le_mul_right _ (by omega)
    have hY := Real.rpow_nonneg hb.hδ0.le (2 * P.ν * (y.1 : ℝ))
    have hX := Real.rpow_nonneg hb.hδ0.le (2 * P.ν * (x.1 : ℝ))
    have hW1 := mul_nonneg (Wcp_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ1 (.inl 0))) (nB (τ1 (.inl 1))))
      (Wcp_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ1 (.inr 0))) (nB (τ1 (.inr 1))))
    have hW2 := mul_nonneg (Wcp_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ2 (.inl 0))) (nB (τ2 (.inl 1))))
      (Wcp_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ2 (.inr 0))) (nB (τ2 (.inr 1))))
    have hZ1 : 0 ≤ (1 + Cr) ^ 2 * P.δ ^ (2 * P.ν * (y.1 : ℝ)) *
        (Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ1 (.inl 0))) (nB (τ1 (.inl 1))) *
          Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ1 (.inr 0))) (nB (τ1 (.inr 1)))) := by positivity
    have hZ2 : 0 ≤ (1 + Cr) ^ 2 * P.δ ^ (2 * P.ν * (y.1 : ℝ)) *
        (Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ2 (.inl 0))) (nB (τ2 (.inl 1))) *
          Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ2 (.inr 0))) (nB (τ2 (.inr 1)))) := by positivity
    have hP1' := hP1.trans (mul_le_mul_of_nonneg_right hcnt hZ1)
    have hP2' := hP2.trans (mul_le_mul_of_nonneg_right hcnt hZ2)
    have hIrr : jbrProdAt P.L k nB ^ (-(4 * (P.Lambda (p + 1) : ℝ))) * P.L ^ (-(((2 : ℕ) : ℝ) - 1) / 4) *
        P.δ ^ (2 * P.ν * (y.1 : ℝ)) ≤ P.δ ^ (2 * P.ν * (y.1 : ℝ)) * ∏ i, gw P.L k (4 * P.Lambda (p + 1) : ℝ) (nB i) := by
      rw [jbrProdAt_rpow]
      have hg := prod_gw_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) Finset.univ nB
      have hLp := Lpow2_le_one hb
      have := mul_le_mul_of_nonneg_left hLp hg
      nlinarith [mul_nonneg hg hY]
    have hS := alg24 c2 ((1 + Cr) ^ 2) (P.δ ^ (2 * P.ν * (y.1 : ℝ)))
      (Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ1 (.inl 0))) (nB (τ1 (.inl 1))) *
        Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ1 (.inr 0))) (nB (τ1 (.inr 1))))
      (Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ2 (.inl 0))) (nB (τ2 (.inl 1))) *
        Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ2 (.inr 0))) (nB (τ2 (.inr 1))))
      (∏ i, gw P.L k (4 * P.Lambda (p + 1) : ℝ) (nB i)) _ _ _ hc2one
      (by nlinarith [sq_nonneg Cr]) hY (prod_gw_nonneg _ _ _ _ _) (by simpa [mul_assoc] using hP1')
      (by simpa [mul_assoc] using hP2') hIrr
    have hS0 : 0 ≤ c2 * ((1 + Cr) ^ 2 * P.δ ^ (2 * P.ν * (y.1 : ℝ)) *
        (Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ1 (.inl 0))) (nB (τ1 (.inl 1))) *
          Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ1 (.inr 0))) (nB (τ1 (.inr 1))) +
          Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ2 (.inl 0))) (nB (τ2 (.inl 1))) *
            Wcp P.L k (4 * P.Lambda (p + 1) : ℝ) (nB (τ2 (.inr 0))) (nB (τ2 (.inr 1))) +
          ∏ i, gw P.L k (4 * P.Lambda (p + 1) : ℝ) (nB i))) := by
      have := prod_gw_nonneg P.L k (4 * P.Lambda (p + 1) : ℝ) Finset.univ nB
      positivity
    refine (mul_le_mul_of_nonneg_left hS hcA0).trans ((mul_le_mul_of_nonneg_right hcA hS0).trans (le_of_eq ?_))
    have hd := delta_sum hb (x := x.1) (y := y.1) (N := N) (by omega)
    rw [← hd]
    simp only [Wt24m, Wt24irr]
    ring

end

end WaveTurbulence.FlowerP7
