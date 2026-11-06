/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TaylorConstants

/-!
# TARGET Prop 6.2 (proplayer3): the coherent Taylor gate

`coherentTaylorGate`: the spine's `CoherentTaylorGate` follows from the B2.1 obligations
`RegularAsymptoticsGate` (single-layer approximation, the factor bounds (3) and the WKE identity (4)) and
`LeafwiseRegularAsymptoticsGate` (the same estimates with individually modified leaf inputs).

Proof (TARGET L1247). By (4) with `𝓡 = 0`, `∑_𝒬 𝒜_𝒬[φ_p] = 𝒰^{(p)}_n` (the non-dominant leading terms
vanish), so the left side is `‖∑_𝒬 (𝒜_𝒬[F_p] − 𝒜_𝒬[φ_p])(t, t, k)‖`. Each code term is bounded by
`norm_app_add_sub_app_le` (with `‖𝓡_p‖ ≤ L^{-θ_p}`, `‖φ_p‖ ≤ β_φ`), the code count is `≤ (12^9)^n`
(`norm_finsum_codes_le`), and `L^{-(γ₁-√η)}, L^{-θ_p} ≤ L^{-(θ_{p+1}+4θ_p)/5}` for small `η`
(`theta_avg_le`). The constant is `C₁ = 24 · 12^9 · C₁ᴬ C₁ᴮ β_φ²` (`taylor_constant_le`).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg

/-- The body of the coherent Taylor gate (spine `CoherentTaylorGate`). -/
def CTBody (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
    ‖(∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        Q.app P.δ p (inputsF P R p) t t k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ n * jbr k ^ (-(30 * P.d : ℝ)) *
        P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5)

theorem coherentTaylor_gate_eq : CoherentTaylorGate = WTPrefix CTBody := rfl

/-- The constant of Prop 6.2. -/
noncomputable def gT (P₀ : WTParams) (x y : ℝ) : ℝ := 24 * 12 ^ 9 * x * y * βφ P₀ ^ 2

theorem one_le_gT (P₀ : WTParams) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ gT P₀ x y := by
  unfold gT
  have hβ : (1 : ℝ) ≤ βφ P₀ ^ 2 := one_le_pow₀ (one_le_βφ P₀)
  calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
    _ ≤ 24 * 12 ^ 9 * x * y * βφ P₀ ^ 2 := by gcongr; norm_num

/-- `N_q` depends only on `d`, `𝔇` and `L`. -/
theorem N_eq_of (P P' : WTParams) (hd : P'.d = P.d) (hD : P'.D = P.D) (hL : P'.L = P.L) (q : ℕ) :
    P'.N q = P.N q := by
  have hR : ∀ k, P'.Rdown k = P.Rdown k := by
    intro k
    induction k with
    | zero => simp only [WTParams.Rdown, hd, hL]
    | succ k ih => simp only [WTParams.Rdown, ih, hd]
  unfold WTParams.N WTParams.R
  rw [hD, hR, hd]

theorem ηTaylor_le_one (d : ℕ) (γ : ℝ) : ηTaylor d γ ≤ 1 := by
  unfold ηTaylor
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem RegCpl.app_of_not_dominant {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (Q : RegCpl)
    (hQ : Q.dominant = false) (t s : ℝ) (k : Mom d) : Q.app δ r F t s k = 0 := by
  unfold RegCpl.app
  rw [hQ]
  rfl

/-- The B2.1 approximation error in the leafwise form, for a constant profile. -/
theorem const_profile_error_eq (P : WTParams) (r : ℕ) (Q : RegCpl) (LG : LayeredGarden 2)
    (F : Mom P.d → ℝ) :
    (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => coupleLeaves P.L P.γ P.δ LG (fun _ => F) (ts 0) (ts 1) k -
        LeafApp.couple P.δ r (fun _ => F) Q (ts 0) (ts 1) k) =
      (fun ts k => KQstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
        Q.app P.δ r F (ts 0) (ts 1) k) := by
  funext ts k
  rw [LeafApp.couple_const]
  congr 1

/-- **Prop 6.2 at fixed parameters.** -/
theorem ctBody_of (P : WTParams) (C₁' C₂' : ℝ) (hS : Standing P (ηTaylor P.d P.γ))
    (hC₁' : 1 ≤ C₁') (hA : B21Body P) (hB : LRABody { P with C₁ := C₁', C₂ := C₂' }) :
    CTBody { P with C₁ := gT (preC₁ P) P.C₁ C₁' } := by
  intro p hp R hR n hn₀ t ht k
  have hn : n ≤ P.N (p + 1) ^ 4 := by
    rwa [N_eq_of P { P with C₁ := gT (preC₁ P) P.C₁ C₁' } rfl rfl rfl] at hn₀
  have hnB : n ≤ ({ P with C₁ := C₁', C₂ := C₂' } : WTParams).N (p + 1) ^ 4 := by
    rwa [N_eq_of P { P with C₁ := C₁', C₂ := C₂' } rfl rfl rfl]
  show ‖(∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), Q.app P.δ p (inputsF P R p) t t k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)‖ ≤
    gT (preC₁ P) P.C₁ C₁' * (gT (preC₁ P) P.C₁ C₁' * P.δ) ^ n * jbr k ^ (-(30 * P.d : ℝ)) *
      P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5)
  have hd : 1 ≤ P.d := by have := hS.d_ge; omega
  have hL : 1 ≤ P.L := by linarith [hS.L_ge]
  have hη0 : 0 ≤ P.η := hS.η_pos.le
  have hη1 : P.η ≤ 1 := hS.η_le.trans (ηTaylor_le_one _ _)
  have hδ : 0 ≤ P.δ := hS.δ_pos.le
  have hC : 1 ≤ P.C₁ := hS.C₁_ge
  have hj : 0 ≤ jbr k ^ (-(30 * P.d : ℝ)) := Real.rpow_nonneg (jbr_pos k).le _
  -- the WKE solution is bounded at the layer time `δp`
  have hτ : P.δ * p ∈ Icc 0 P.τstar := by
    refine ⟨mul_nonneg hδ (Nat.cast_nonneg p), ?_⟩
    rw [hS.τstar_eq, mul_comm]
    have : (p : ℝ) ≤ P.D := by exact_mod_cast hp.le
    exact mul_le_mul_of_nonneg_right this hδ
  have hφβ : SNormR (40 * P.d) (40 * P.d) (P.φ (P.δ * p)) ≤ ENNReal.ofReal (βφ (preC₁ P)) :=
    SNormR_le_βφ (preC₁ P) hS.wke.1 hτ
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : NNReal, (ρ : ℝ) = P.L ^ (-P.theta p) :=
    ⟨⟨P.L ^ (-P.theta p), Real.rpow_nonneg (by linarith) _⟩, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : NNReal, (β : ℝ) = βφ (preC₁ P) :=
    ⟨⟨βφ (preC₁ P), by linarith [one_le_βφ (preC₁ P)]⟩, rfl⟩
  have hβ1 : (1 : ℝ) ≤ β := by rw [hβdef]; exact one_le_βφ _
  have hρ1 : (ρ : ℝ) ≤ 1 := by
    rw [hρdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr (theta_nonneg P p))
  have hρβ : ρ ≤ β := by
    rw [← NNReal.coe_le_coe]
    linarith
  have hβ : 1 ≤ β := by exact_mod_cast hβ1
  have hF₀ : SNormR (40 * P.d) (40 * P.d) (P.φ (P.δ * p)) ≤ ENNReal.ofReal (β : ℝ) := by
    rw [hβdef]; exact hφβ
  have hRp : SNormR (40 * P.d) (40 * P.d) (R p) ≤ ENNReal.ofReal (ρ : ℝ) := by
    rw [hρdef]; exact hR p le_rfl
  -- the B2.1 obligations at the input `F_p` and at the input `φ_p`
  obtain ⟨hA1F, -, hA3F, -, -⟩ := hA p hp p le_rfl (R p) (hR p le_rfl) n hn
  have h0 : InputRemainder P (fun _ => 0) p := by
    unfold InputRemainder
    rw [SNormR_zero]
    exact zero_le
  obtain ⟨hA1₀, -, -, -, hA4₀⟩ := hA p hp p le_rfl (fun _ => 0) h0 n hn
  have hU := hA4₀ rfl (fun _ => rfl) t ht k
  simp only [add_zero] at hA1₀ hU
  -- one code
  set eA : ℝ := P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ))
    with heAdef
  set eB : ℝ := C₁' * (C₁' * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ))
    with heBdef
  have hΛ0 : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by linarith) _
  have heA : 0 ≤ eA := by positivity
  have heB : 0 ≤ eB := by
    have : 0 ≤ C₁' := by linarith
    positivity
  have hcJ : 0 ≤ P.C₁ * P.C₁ ^ n := by positivity
  have hcM : 0 ≤ C₁' * C₁' ^ n := by
    have : 0 ≤ C₁' := by linarith
    positivity
  set X : ℝ := 2 * eA + 2 ^ (2 * n + 1) * (eB + P.δ ^ n * 2 ^ n * (P.C₁ * P.C₁ ^ n) *
    (C₁' * C₁' ^ n)) * ((ρ : ℝ) * (β : ℝ) ^ (2 * n + 1)) with hXdef
  have hcode : ∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n →
      ‖Q.app P.δ p (inputsF P R p) t t k - Q.app P.δ p (P.φ (P.δ * p)) t t k‖ ≤
        X * jbr k ^ (-(30 * P.d : ℝ)) := by
    intro Q hwf hsize
    obtain ⟨LG, hQ, hlay⟩ := exists_layered_decodes Q hwf p
    have hA₀ : XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox p p) Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG (fun _ => P.φ (P.δ * p)) (ts 0) (ts 1) k -
          LeafApp.couple P.δ p (fun _ => P.φ (P.δ * p)) Q (ts 0) (ts 1) k) ≤
        ENNReal.ofReal eA := by
      rw [const_profile_error_eq]
      exact hA1₀ Q hwf hsize LG hQ hlay
    have hA₁ : XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox p p) Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG (fun _ x => P.φ (P.δ * p) x + R p x) (ts 0) (ts 1) k -
          LeafApp.couple P.δ p (fun _ x => P.φ (P.δ * p) x + R p x) Q (ts 0) (ts 1) k) ≤
        ENNReal.ofReal eA := by
      rw [const_profile_error_eq P p Q LG (fun x => P.φ (P.δ * p) x + R p x)]
      exact hA1F Q hwf hsize LG hQ hlay
    have hBq := fun (H : LeafProfiles 2 P.d) (B : (Fin 2 × Path) → NNReal)
        (hH : LeafwiseControlled LG H B) =>
      (hB p hp p le_rfl n hnB).1 Q hwf hsize LG hQ hlay H B hH
    have hJ : Q.dominant = true → |Q.JB p t t| ≤ P.C₁ * P.C₁ ^ n := fun hdom =>
      abs_JB_le hη1 Q p hcJ (hA3F Q hwf hdom hsize).1 ht ht
    have key := norm_app_add_sub_app_le P hd hL hη0 hδ Q hsize LG hQ (P.φ (P.δ * p)) (R p) hρβ hβ
      hF₀ hRp heA heB hcJ hcM hA₀ hA₁ hBq ht ht hJ k
    rw [LeafApp.couple_const, LeafApp.couple_const] at key
    exact key
  -- the code sum
  have hsum : (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        Q.app P.δ p (inputsF P R p) t t k) - (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ) =
      ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        (Q.app P.δ p (inputsF P R p) t t k - Q.app P.δ p (P.φ (P.δ * p)) t t k) := by
    rw [← hU, finsum_dominant_eq n _ (fun Q hQ => RegCpl.app_of_not_dominant _ _ _ Q hQ _ _ _),
      finsum_codes_sub]
  rw [hsum]
  -- the exponents
  have hθ := theta_avg_le P hS.d_ge hS.γ_mem hS.η_pos hS.η_le p
  have hθs := theta_succ_le P hη0 p
  have hΛℓ : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) ≤
      P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    rw [Nat.cast_one, mul_one]
    linarith
  have hΛ1 : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hL
    rw [Nat.cast_one, mul_one]
    linarith [theta_nonneg P p, theta_nonneg P (p + 1)]
  have hρℓ : (ρ : ℝ) ≤ P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5) := by
    rw [hρdef]
    apply Real.rpow_le_rpow_of_exponent_le hL
    linarith
  have hconst := taylor_constant_le hC hC₁' hβ1 hδ hΛ0 hΛℓ hΛ1 ρ.2 hρℓ n
  calc _ ≤ ((12 ^ 9 : ℕ) ^ n : ℝ) * (X * jbr k ^ (-(30 * P.d : ℝ))) :=
        norm_finsum_codes_le n _ _ (mul_nonneg (by positivity) hj) hcode
    _ = (((12 ^ 9 : ℕ) ^ n : ℝ) * X) * jbr k ^ (-(30 * P.d : ℝ)) := by ring
    _ ≤ ((24 * 12 ^ 9 * P.C₁ * C₁' * (β : ℝ) ^ 2) * ((24 * 12 ^ 9 * P.C₁ * C₁' * (β : ℝ) ^ 2) * P.δ) ^ n *
          P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5)) * jbr k ^ (-(30 * P.d : ℝ)) :=
        mul_le_mul_of_nonneg_right hconst hj
    _ = _ := by
        rw [hβdef]
        unfold gT
        ring

/-- **TARGET Prop 6.2 (proplayer3)** from the B2.1 obligations. -/
theorem coherentTaylorGate (hA : RegularAsymptoticsGate) (hB : LeafwiseRegularAsymptoticsGate) :
    CoherentTaylorGate :=
  wtPrefix_transfer₂' gT (fun P _ _ hx hy => one_le_gT P hx hy) ηTaylor ηTaylor_pos hA hB
    fun P C₁' C₂' hS hC₁' _ hAP hBP => ctBody_of P C₁' C₂' hS hC₁' hAP hBP

end WaveTurbulence.PL234
