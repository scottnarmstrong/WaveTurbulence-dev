/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Endpoint
public import WaveTurbulence.Foundations.IncohInst.Regref.Inputs
public import WaveTurbulence.Foundations.FC23.ExtractionNumerics
/-! # FL-TYPED: the `S^{40d,40d}` bound of the family pair profile. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Typed
open WaveTurbulence.NormBridgeScratch WaveTurbulence.Induct Finset

variable {d : ℕ}

theorem wordD_weighted_of_SNormR {A B : ℕ} (hA : A ≠ 0) {f : Mom d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : SNormR A B f ≤ ENNReal.ofReal C) (l : List (Fin d)) (hl : l.length ≤ A) (x : Mom d) :
    jbr x ^ B * ‖wordD l (fun y => ((f y : ℝ) : ℂ)) x‖ ≤ C := by
  have hc : ContDiff ℝ (A : WithTop ℕ∞) f :=
    WaveTurbulence.Regref.contDiff_of_SNormR_ne_top hA (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  have hcc : ContDiff ℝ (A : WithTop ℕ∞) (fun y => ((f y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hc
  have e : wordD l (fun y => ((f y : ℝ) : ℂ)) =
      Fourier.momentumDerivative (fun i : Fin l.length => l.get i) (fun y => ((f y : ℝ) : ℂ)) := by
    rw [momentumDerivative_eq_wordD _ (hcc.of_le (by exact_mod_cast hl)), List.ofFn_get]
  rw [e]
  exact SNorm_momentum_pointwise (fun y => ((f y : ℝ) : ℂ)) hcc C hC h hl _ x

/-- **The `S^{40d,40d}` bound of the family pair profile.** The constants `c` and `M₀` depend only on `d`.
The input `F q` is controlled in `S^{40d,40d}` (by `b0`) and in `S^{40d,120d}` (by `b1`); the second weight
is needed for the cross term `z_j z_{j'}`.  `A = M/(4(2N+1))`, and `K = C(2N+1)U ≥ 1`. -/
theorem familyProfile_snorm (hd : 1 ≤ d) :
    ∃ c M₀ : ℝ, 0 ≤ c ∧ 0 < M₀ ∧ ∀ {w : ℕ} (F : ℕ → Mom d → ℝ) (p N : ℕ) (C U M A b0 b1 : ℝ)
      (tail : Fin w → Bool) (z : Fin w → ℝ) (q : ℕ) (j j' : Fin w),
      0 ≤ b0 → 0 ≤ b1 → 0 < C → 0 < U → 1 ≤ C * ((2 * N + 1 : ℕ) : ℝ) * U → M₀ ≤ M →
      A = M / (4 * ((2 * N + 1 : ℕ) : ℝ)) → 1 ≤ A →
      (∀ i, z i ∈ Set.Icc (0 : ℝ) (FC23.extractionRadius (40 * d) N C U M)) →
      SNormR (40 * d) (40 * d) (F q) ≤ ENNReal.ofReal b0 →
      SNormR (40 * d) (120 * d) (F q) ≤ ENNReal.ofReal b1 →
      SNormR (40 * d) (40 * d) (familyProfile F p M A tail z q j j') ≤
        ENNReal.ofReal (2 * b0 + c / (C * ((2 * N + 1 : ℕ) : ℝ)) * b1 / U) := by
  obtain ⟨γ, hγ, hγ0, hj⟩ := radial_jets (d := d) (40 * d)
  have hS0 : 0 ≤ S0Sum γ (40 * d) :=
    sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (mulγ_nonneg hγ hγ i)
  have hT0 : 0 ≤ TSum γ (Γvf γ) (40 * d) :=
    sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (add_nonneg (mulγ_nonneg (Γvf_nonneg hγ) hγ i) (mulγ_nonneg hγ (Γvf_nonneg hγ) i))
        (mulγ_nonneg (Γvf_nonneg hγ) (Γvf_nonneg hγ) i))
  refine ⟨2 ^ (2 * (40 * d)) * TSum γ (Γvf γ) (40 * d), 2 * S0Sum γ (40 * d) + 2,
    by positivity, by linarith, ?_⟩
  intro w F p N C U M A b0 b1 tail z q j j' hb0 hb1 hC hU hK hM hAdef hA1 hz h0 h1
  have hd0 : 40 * d ≠ 0 := by omega
  set N' : ℝ := ((2 * N + 1 : ℕ) : ℝ) with hN'
  have hN1 : 1 ≤ N' := by rw [hN']; exact_mod_cast Nat.le_add_left 1 (2 * N)
  have hA0 : 0 < A := by linarith
  have hMA : M = 4 * N' * A := by rw [hAdef]; field_simp
  have h2A : 2 * A ≤ M := by rw [hMA]; nlinarith
  have hKpos : 0 < C * N' * U := by positivity
  have hzK : ∀ i, |z i| ≤ A ^ (40 * d) / (C * N' * U) := by
    intro i
    obtain ⟨hz0, hz1⟩ := hz i
    rw [abs_of_nonneg hz0]
    refine hz1.trans (le_of_eq ?_)
    unfold FC23.extractionRadius
    rw [← hAdef]
  obtain ⟨u1, v1, hu1c, hv1c, hu1, hv1, hvan1, hu1e⟩ :=
    endpoint_data (40 * d) hγ hγ0 hj p q (tail j) hA1 h2A
  obtain ⟨u2, v2, hu2c, hv2c, hu2, hv2, hvan2, hu2e⟩ :=
    endpoint_data (40 * d) hγ hγ0 hj p q (tail j') hA1 h2A
  have hFc : ContDiff ℝ ((40 * d : ℕ) : WithTop ℕ∞) (fun y => ((F q y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (WaveTurbulence.Regref.contDiff_of_SNormR_ne_top hd0
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h0))
  have hF0 : ∀ l : List (Fin d), l.length ≤ 40 * d → ∀ x,
      jbr x ^ (40 * d) * ‖wordD l (fun y => ((F q y : ℝ) : ℂ)) x‖ ≤ b0 :=
    fun l hl x => wordD_weighted_of_SNormR hd0 hb0 h0 l hl x
  have hF1 : ∀ l : List (Fin d), l.length ≤ 40 * d → ∀ x,
      jbr x ^ (3 * (40 * d)) * ‖wordD l (fun y => ((F q y : ℝ) : ℂ)) x‖ ≤ b1 := by
    intro l hl x
    rw [show 3 * (40 * d) = 120 * d by ring]
    exact wordD_weighted_of_SNormR hd0 hb1 h1 l hl x
  have hcore := profile_core (d := d) (40 * d) (40 * d) hγ (by rw [hγ0]) (Γvf_nonneg hγ)
    (A := A) (M := M) (K := C * N' * U) (b0 := b0) (b1 := b1) (z1 := z j) (z2 := z j')
    hA1 h2A hK hb0 hb1 (by linarith) (hzK j) (hzK j') hFc hF0 hF1 hu1c hu2c hv1c hv2c hu1 hu2 hv1 hv2
    hvan1 hvan2
  have hPeq : (fun y : Mom d => ((familyProfile F p M A tail z q j j' y : ℝ) : ℂ)) =
      fun y => ((F q y : ℝ) : ℂ) *
        ((u1 y + (z j : ℂ) * v1 y) * (u2 y + (z j' : ℂ) * v2 y)) := by
    funext y
    have e1 := hu1e (z j) y
    have e2 := hu2e (z j') y
    unfold familyProfile
    push_cast
    rw [e1, e2]
    ring
  have hPc : ContDiff ℝ ((40 * d : ℕ) : WithTop ℕ∞)
      (fun y : Mom d => ((familyProfile F p M A tail z q j j' y : ℝ) : ℂ)) := by
    rw [hPeq]
    exact hFc.mul ((hu1c.add (contDiff_const.mul hv1c)).mul (hu2c.add (contDiff_const.mul hv2c)))
  have hfin : SNorm (40 * d) (40 * d)
      (fun y : Mom d => ((familyProfile F p M A tail z q j j' y : ℝ) : ℂ)) ≤
      ENNReal.ofReal (2 * b0 + 2 ^ (2 * (40 * d)) * TSum γ (Γvf γ) (40 * d) * b1 / (C * N' * U)) := by
    apply SNorm_le_of_momentum_bounds _ hPc
    intro n hn ρ x
    rw [momentumDerivative_eq_wordD ρ (hPc.of_le (by exact_mod_cast hn)), hPeq]
    have := hcore (List.ofFn ρ) (by simpa using hn) x
    exact this
  have hrhs : (2 * b0 + 2 ^ (2 * (40 * d)) * TSum γ (Γvf γ) (40 * d) * b1 / (C * N' * U)) =
      2 * b0 + 2 ^ (2 * (40 * d)) * TSum γ (Γvf γ) (40 * d) / (C * N') * b1 / U := by
    field_simp
  rw [hrhs] at hfin
  exact hfin

end WaveTurbulence.Flower.Typed
