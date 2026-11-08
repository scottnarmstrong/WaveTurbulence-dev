/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltNT.Profile
public import WaveTurbulence.Foundations.ApproxNT.CellEstimate
public import WaveTurbulence.Foundations.ApproxNT.AppCell
public import WaveTurbulence.Foundations.RegAsymp.ContinuousCellSize

/-! # FILT-NT: the cell estimates for the filtered profile

* `exists_filt_cell_bound`: main's `ApproxNT.exists_cell_bound` for `filtProf J S Ψ₁` (the core bound
  `ApproxNT.exists_core_bound` is generic in the Fourier representation and the weights);
* `filt_continuous_cell_size`: main's `RegAsymp.exists_continuous_cell_size_bound`, the `J`-factors bounded through
  `‖ĝ_S‖_∞` and the `L¹` bound of `cellInt` (no principal-value estimate is needed).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset WithLp WaveTurbulence.ApproxNT
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.Flower.FiltNT

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Splitting the time integral of the filtered profile into the `J` and `J^c` variables. -/
theorem integral_filtHat_split (J : Finset ι) (S : ι → ℝ)
    (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (g : ι → ℝ → ℂ) :
    ∫ s, filtHat J S Ψ₁ s * ∏ i, g i (s i) =
      (∏ j ∈ J, ∫ t, ghat (S j) t * g j t) *
        ∫ b : {j // j ∉ J} → ℝ, 𝓕 Ψ₁ (toLp 2 b) * ∏ i : {j // j ∉ J}, g i (b i) := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J)
  have hpt : ∀ p : ({j // j ∈ J} → ℝ) × ({j // j ∉ J} → ℝ),
      filtHat J S Ψ₁ (e.symm p) * ∏ i, g i (e.symm p i) =
      (∏ j : {j // j ∈ J}, ghat (S j) (p.1 j) * g j (p.1 j)) *
        (𝓕 Ψ₁ (toLp 2 p.2) * ∏ i : {j // j ∉ J}, g i (p.2 i)) := by
    intro p
    have hsplit : filtHat J S Ψ₁ (e.symm p) =
        (∏ j : {j // j ∈ J}, ghat (S j) ((e (e.symm p)).1 j)) *
          𝓕 Ψ₁ (toLp 2 (e (e.symm p)).2) := by
      rw [filtHat, ← prod_coe_sort J]
      rfl
    rw [hsplit, e.apply_symm_apply, ← prod_mul_prod_compl J (fun i => g i (e.symm p i)),
      ← prod_coe_sort J, prod_subtype Jᶜ (p := (· ∉ J)) (fun x => by simp), prod_mul_distrib]
    have h1 : ∀ i : {j // j ∈ J}, e.symm p i = p.1 i := fun i => by
      rw [piSplit_symm_apply]; simp [i.2]
    have h2 : ∀ i : {j // j ∉ J}, e.symm p i = p.2 i := fun i => by
      rw [piSplit_symm_apply]; simp [i.2]
    simp_rw [h1, h2]
    ring
  rw [integral_split_J J]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun p => hpt p)).trans ?_
  have hpm := integral_prod_mul (μ := (volume : Measure ({j // j ∈ J} → ℝ)))
    (ν := (volume : Measure ({j // j ∉ J} → ℝ)))
    (fun a => ∏ j : {j // j ∈ J}, ghat (S j) (a j) * g j (a j))
    (fun b => 𝓕 Ψ₁ (toLp 2 b) * ∏ i : {j // j ∉ J}, g i (b i))
  refine hpm.trans ?_
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun (j : {j // j ∈ J}) (t : ℝ) => ghat (S j) t * g j t), ← prod_coe_sort J]


variable {d : ℕ}

/-- The profile weights, in closed form. -/
theorem filt_weight_le {d n : ℕ} (J : Finset (Fin n)) (Kp : ℝ) (hKp : 0 ≤ Kp) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (F : Finset (Fin n)) :
    Kp ^ J.card * (2 ^ (d * (F.subtype (· ∉ J)).card) *
      ∑ G ∈ (F.subtype (· ∉ J)).powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ)) ≤
      max 1 (Kp) ^ n * C₀ ^ n *
        (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d)) ^ F.card := by
  set F' := F.subtype (· ∉ J)
  have hF' : F'.card ≤ F.card := by rw [card_subtype]; exact card_filter_le _ _
  have hJ : J.card ≤ n := by simpa using card_le_univ J
  have hFn : F.card ≤ n := by simpa using card_le_univ F
  have hK := hKp
  have hC0 : 0 ≤ C₀ := by linarith
  set B : ℝ := ((8 * d * n + 1 : ℕ) : ℝ)
  have hB : 1 ≤ B := by simp only [B]; exact_mod_cast Nat.le_add_left 1 _
  have hM : Kp ^ J.card ≤ max 1 (Kp) ^ n :=
    (pow_le_pow_left₀ hK (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) hJ)
  have hterm : ∀ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ) ≤
      C₀ ^ n * B ^ (8 * d * F.card) := by
    intro G hG
    have hGc : G.card ≤ F.card := (card_le_card (mem_powerset.1 hG)).trans hF'
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : 4 * (G.card * (2 * d)) = (8 * d) * G.card := by ring
    rw [h1]
    calc (((8 * d) * G.card).factorial : ℝ) ≤ B ^ ((8 * d) * G.card) :=
          factorial_le_pow_of_le (hGc.trans hFn)
      _ ≤ B ^ (8 * d * F.card) := pow_le_pow_right₀ hB (Nat.mul_le_mul_left _ hGc)
  have hsum : ∑ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ) ≤
      2 ^ F.card * (C₀ ^ n * B ^ (8 * d * F.card)) := by
    calc ∑ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ)
        ≤ ∑ _G ∈ F'.powerset, C₀ ^ n * B ^ (8 * d * F.card) := sum_le_sum hterm
      _ = 2 ^ F'.card * (C₀ ^ n * B ^ (8 * d * F.card)) := by
          rw [sum_const, card_powerset, nsmul_eq_mul]; push_cast; ring
      _ ≤ 2 ^ F.card * (C₀ ^ n * B ^ (8 * d * F.card)) := by
          gcongr
          · norm_num
  calc Kp ^ J.card * (2 ^ (d * F'.card) *
        ∑ G ∈ F'.powerset, C₀ ^ n * ((4 * (G.card * (2 * d))).factorial : ℝ))
      ≤ max 1 (Kp) ^ n * (2 ^ (d * F.card) * (2 ^ F.card * (C₀ ^ n * B ^ (8 * d * F.card)))) := by
        refine mul_le_mul hM ?_ (by positivity) (by positivity)
        refine mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hF')) hsum
          (sum_nonneg fun G _ => by positivity) (by positivity)
    _ = max 1 (Kp) ^ n * C₀ ^ n * (2 ^ (d + 1) * B ^ (8 * d)) ^ F.card := by
        rw [mul_pow, ← pow_mul, ← pow_mul, add_mul, one_mul, pow_add]
        ring


/-- The estimate for one cell configuration. -/
theorem exists_filt_cell_bound (hd : 3 ≤ d) (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hb : ∀ S : ℝ, 1 ≤ S → ∀ s : ℝ, ‖ghat S s‖ * (1 + s ^ 2) ^ d ≤ Kp) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 20) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (L δ : ℝ), 2 ≤ L → 2 ≤ L ^ η → δ ∈ Set.Ioc (0 : ℝ) 1 →
      (n : ℝ) * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
        L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)) ≤ 1 / 2 →
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ), ContDiff ℝ ∞ Ψ₁ →
      WordDerivL1 Ψ₁ (fun k => C₀ ^ n * ((4 * k).factorial : ℝ)) →
      ∀ (S : Fin n → ℝ), (∀ j, 1 ≤ S j) → ∀ (c : CellData d (Fin n)),
      ‖multiSum L (δ * L ^ (2 * γ)) (filtProf J S Ψ₁) c.p c.q c.ξ c.ζ -
          ((L ^ (2 * d) : ℝ) : ℂ) ^ n *
            multiInt (δ * L ^ (2 * γ)) (filtProf J S Ψ₁) c.p c.q c.ξ c.ζ‖ ≤
        (K * max 1 (Kp) * C₀ * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n *
          (∑ i, (L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) + L⁻¹) +
            2 * n * (2 ^ (d + 1) * ((8 * d * n + 1 : ℕ) : ℝ) ^ (8 * d) *
              L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η))) := by
  obtain ⟨K, hK0, hcore⟩ := exists_core_bound hd hγ hη0 hη
  refine ⟨K, hK0, ?_⟩
  intro n L δ hL hLη hδ hnq J Ψ₁ hΨ hD S hS c
  have hd1 : 1 ≤ d := by omega
  have hD0 : ∀ k, 0 ≤ C₀ ^ n * ((4 * k).factorial : ℝ) := fun k => by
    have : 0 ≤ C₀ := by linarith
    positivity
  have hL0 : 0 < L := by linarith
  set M := max 1 (Kp)
  set B : ℝ := ((8 * d * n + 1 : ℕ) : ℝ)
  set ε : ℝ := L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)
  have hε : 0 ≤ ε := Real.rpow_nonneg hL0.le _
  set q : ℝ := 2 ^ (d + 1) * B ^ (8 * d) * ε
  have hq : 0 ≤ q := by positivity
  set A : Finset (Fin n) → ℝ := fun F => M ^ n * C₀ ^ n * (2 ^ (d + 1) * B ^ (8 * d)) ^ F.card
  have hA : ∀ F s, ‖filtHat J S Ψ₁ s‖ * ∏ i ∈ F, (1 + s i ^ 2) ^ d ≤ A F := fun F s =>
    (norm_filtHat_mul_le J S Kp hKp (fun j s' => hb (S j) (hS j) s') hΨ hD hD0 F s).trans (filt_weight_le J Kp hKp hC₀ F)
  have hrep := isFourierRep_filtProf hd1 J S hS hΨ hD hD0
  have h := hcore (Fin n) L δ hL hLη hδ _ _ hrep A hA c
  rw [Fintype.card_fin] at h
  refine h.trans ?_
  have hμ : 0 < δ * L ^ (2 * γ) := mul_pos hδ.1 (Real.rpow_pos_of_pos hL0 _)
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hC0 : 0 ≤ C₀ := by linarith
  have hsumF : ∑ F ∈ (univ : Finset (Fin n)).powerset.erase ∅, A F * ε ^ F.card ≤
      M ^ n * C₀ ^ n * (2 * n * q) := by
    have h1 : ∑ F ∈ (univ : Finset (Fin n)).powerset.erase ∅, A F * ε ^ F.card =
        M ^ n * C₀ ^ n * ∑ F ∈ (univ : Finset (Fin n)).powerset.erase ∅, q ^ F.card := by
      rw [mul_sum]
      refine sum_congr rfl fun F _ => ?_
      simp only [A, q, mul_pow]; ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := sum_powerset_erase_pow_le (ι := Fin n) hq (by simpa [q] using hnq)
    simpa using h2
  have hA0 : A ∅ = M ^ n * C₀ ^ n := by simp [A]
  rw [hA0]
  have hx : 0 ≤ (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n := by positivity
  calc (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n *
        (M ^ n * C₀ ^ n * ∑ i, (L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) + L⁻¹) +
          ∑ F ∈ (univ : Finset (Fin n)).powerset.erase ∅, A F * ε ^ F.card)
      ≤ (K * L ^ (2 * d) / (δ * L ^ (2 * γ))) ^ n *
        (M ^ n * C₀ ^ n * ∑ i, (L ^ (-1 + 2 * η) * (1 + ‖c.ξ i‖ + ‖c.ζ i‖) + L⁻¹) +
          M ^ n * C₀ ^ n * (2 * n * q)) := by gcongr
    _ = _ := by
        simp only [q, B, ε, M]
        rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, mul_pow]
        ring


end WaveTurbulence.Flower.FiltNT
