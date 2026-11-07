/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Fam.Defs
public import WaveTurbulence.Foundations.Flower.Fam.Profile
public import WaveTurbulence.Foundations.Flower.Typed.Support
/-! # FL-FAM: input bounds, the profile constants, and the support of the family profile. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Set WaveTurbulence.Flower.Typed

/-- The `S^{A,B}` bound of `inputsF` for `A, B ≤ Λ_p`, with constant `unifBound at (Λ₀, Λ₀)` plus one. -/
theorem inputs_bound (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ)
    (htime : P.τstar = (P.D : ℝ) * P.δ) (hsol : ContinuousOn P.φ (Icc 0 P.τstar))
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) {A B : ℕ}
    (hA : A ≤ P.Lambda p) (hB : B ≤ P.Lambda p) :
    ∀ r ≤ p, SNormR A B (inputsF P R r) ≤ ENNReal.ofReal (Ufam P p) := by
  have hsp := unifBound_spec P hsol (P.Lambda 0) (P.Lambda 0)
  have hΛ := LGSpine.Lambda_antitone P hd (Nat.zero_le p)
  have htr : ∀ r ≤ p, P.δ * r ∈ Icc (0 : ℝ) P.τstar := by
    intro r hr
    refine ⟨mul_nonneg hδ (Nat.cast_nonneg r), ?_⟩
    rw [htime]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (show (r : ℝ) ≤ P.D by exact_mod_cast hr.trans hp.le) hδ
  exact LGSpine.inputsF_SNormR_bound P hd hL hp hA hB R hR _ (by linarith [hsp.1]) (fun r hr =>
    LGSpine.SNormR_mono_bound (hA.trans hΛ) (hB.trans hΛ) _ ((P.φ (P.δ * r)).smooth _) _
      (by linarith [hsp.1]) (hsp.2 _ (htr r hr)))

/-- The `S^{40d,40d}` bound of `inputsF`, independent of `δ`. -/
theorem inputs_bound_low (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ)
    (htime : P.τstar = (P.D : ℝ) * P.δ) (hsol : ContinuousOn P.φ (Icc 0 P.τstar))
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) :
    ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (inputsF P R r) ≤ ENNReal.ofReal (Ulow P) := by
  have hsp := unifBound_spec P hsol (40 * P.d) (40 * P.d)
  have htr : ∀ r ≤ p, P.δ * r ∈ Icc (0 : ℝ) P.τstar := by
    intro r hr
    refine ⟨mul_nonneg hδ (Nat.cast_nonneg r), ?_⟩
    rw [htime]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (show (r : ℝ) ≤ P.D by exact_mod_cast hr.trans hp.le) hδ
  have h40 := LGSpine.forty_dim_le_Lambda P hd hp.le
  exact LGSpine.inputsF_SNormR_bound P hd hL hp h40 h40 R hR _ (by linarith [hsp.1])
    (fun r hr => hsp.2 _ (htr r hr))

/-- The `S`-weight profile constant. -/
def cgen (d S : ℕ) : ℝ :=
  if h : 1 ≤ d ∧ 40 * d ≤ S then (familyProfile_snorm_gen h.1 S h.2).choose else 0

/-- The threshold on the scale `M`. -/
def Mgen (d S : ℕ) : ℝ :=
  if h : 1 ≤ d ∧ 40 * d ≤ S then (familyProfile_snorm_gen h.1 S h.2).choose_spec.choose else 0

theorem genSpec {d : ℕ} (hd : 1 ≤ d) (S : ℕ) (hS : 40 * d ≤ S) :
    0 ≤ cgen d S ∧ 0 < Mgen d S ∧ ∀ {w : ℕ} (F : ℕ → Mom d → ℝ) (p N : ℕ) (C U M A b0 b1 : ℝ)
      (tail : Fin w → Bool) (z : Fin w → ℝ) (q : ℕ) (j j' : Fin w),
      0 ≤ b0 → 0 ≤ b1 → 0 < C → 0 < U → 1 ≤ C * ((2 * N + 1 : ℕ) : ℝ) * U → Mgen d S ≤ M →
      A = M / (4 * ((2 * N + 1 : ℕ) : ℝ)) → 1 ≤ A →
      (∀ i, z i ∈ Set.Icc (0 : ℝ) (FC23.extractionRadius (40 * d) N C U M)) →
      SNormR (40 * d) S (F q) ≤ ENNReal.ofReal b0 →
      SNormR (40 * d) (3 * S) (F q) ≤ ENNReal.ofReal b1 →
      SNormR (40 * d) S (familyProfile F p M A tail z q j j') ≤
        ENNReal.ofReal (2 * b0 + cgen d S / (C * ((2 * N + 1 : ℕ) : ℝ)) * b1 / U) := by
  have hh : 1 ≤ d ∧ 40 * d ≤ S := ⟨hd, hS⟩
  unfold cgen Mgen
  rw [dif_pos hh, dif_pos hh]
  exact (familyProfile_snorm_gen hd S hS).choose_spec.choose_spec

/-- The family profile bound with `C = 1`: `‖·‖ ≤ 2 b0 + c`, when `b1 ≤ U`, `1 ≤ U`. -/
theorem profile_bound {d : ℕ} (hd : 1 ≤ d) (S : ℕ) (hS : 40 * d ≤ S) {w : ℕ} (F : ℕ → Mom d → ℝ)
    (p N : ℕ) (U M A b0 b1 : ℝ) (tail : Fin w → Bool) (z : Fin w → ℝ) (q : ℕ) (j j' : Fin w)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hU1 : 1 ≤ U) (hb1U : b1 ≤ U) (hM : Mgen d S ≤ M)
    (hA : A = M / (4 * ((2 * N + 1 : ℕ) : ℝ))) (hA1 : 1 ≤ A)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) (FC23.extractionRadius (40 * d) N (Cfam d) U M))
    (h0 : SNormR (40 * d) S (F q) ≤ ENNReal.ofReal b0)
    (h1 : SNormR (40 * d) (3 * S) (F q) ≤ ENNReal.ofReal b1) :
    SNormR (40 * d) S (familyProfile F p M A tail z q j j') ≤ ENNReal.ofReal (2 * b0 + cgen d S) := by
  obtain ⟨hc, -, hsp⟩ := genSpec hd S hS
  have hN1 : (1 : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 (2 * N)
  have hK : 1 ≤ Cfam d * ((2 * N + 1 : ℕ) : ℝ) * U := by
    unfold Cfam; rw [one_mul]; nlinarith
  refine (hsp F p N (Cfam d) U M A b0 b1 tail z q j j' hb0 hb1 (Cfam_pos d) (by linarith) hK hM hA hA1
    hz h0 h1).trans (ENNReal.ofReal_le_ofReal ?_)
  have : cgen d S / (Cfam d * ((2 * N + 1 : ℕ) : ℝ)) * b1 / U ≤ cgen d S := by
    unfold Cfam
    rw [one_mul, div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
    have h2 : cgen d S * b1 ≤ cgen d S * U := mul_le_mul_of_nonneg_left hb1U hc
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hN1), mul_nonneg hc hb1]
  linarith

/-- The low profile constant. -/
def loB (P : WTParams) : ℝ := 2 * Ulow P + cgen P.d (40 * P.d)

/-- The weight of the high profile norm. -/
def Wt (P : WTParams) (p : ℕ) : ℕ := 40 * P.d + 4 * P.Lambda (p + 1)

/-- The high profile constant (at least `loB`). -/
def hiB (P : WTParams) (p : ℕ) : ℝ := max (2 * Ufam P p + cgen P.d (Wt P p)) (loB P)

theorem cgen_nonneg {d : ℕ} (hd : 1 ≤ d) (S : ℕ) (hS : 40 * d ≤ S) : 0 ≤ cgen d S :=
  (genSpec hd S hS).1

theorem one_le_loB (P : WTParams) (hd : 1 ≤ P.d) : 1 ≤ loB P := by
  have := one_le_Ulow P
  have := cgen_nonneg hd (40 * P.d) le_rfl
  unfold loB; linarith

theorem loB_le_hiB (P : WTParams) (p : ℕ) : loB P ≤ hiB P p := le_max_right _ _

theorem Lambda_succ (P : WTParams) {p : ℕ} (hp : p < P.D) :
    P.Lambda p = 40 * P.d * P.Lambda (p + 1) := by
  unfold WTParams.Lambda
  rw [show P.D + 1 - p = (P.D + 1 - (p + 1)) + 1 by omega, pow_succ]
  ring

theorem weights_le (P : WTParams) (hd : 3 ≤ P.d) {p : ℕ} (hp : p < P.D) :
    3 * Wt P p ≤ P.Lambda p ∧ 120 * P.d ≤ P.Lambda p := by
  have h1 := Lambda_succ P hp
  have h2 : 40 * P.d ≤ P.Lambda (p + 1) := LGSpine.forty_dim_le_Lambda P (by omega) (by omega)
  have h3 : 120 ≤ 40 * P.d := by omega
  unfold Wt
  constructor
  · rw [h1]; nlinarith [Nat.zero_le (P.Lambda (p + 1))]
  · rw [h1]; nlinarith [Nat.zero_le (P.Lambda (p + 1))]

/-- The family profile of the inputs, low weight. -/
theorem profile_low {Pm : ℕ} (P : WTParams) (hd : 3 ≤ P.d) (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ)
    (htime : P.τstar = (P.D : ℝ) * P.δ) (hsol : ContinuousOn P.φ (Icc 0 P.τstar))
    {p : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (N : ℕ) (M A : ℝ) (tail : Fin (2 * Pm) → Bool) (z : Fin (2 * Pm) → ℝ)
    (hM : Mgen P.d (40 * P.d) ≤ M) (hA : A = M / (4 * ((2 * N + 1 : ℕ) : ℝ))) (hA1 : 1 ≤ A)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) (FC23.extractionRadius (40 * P.d) N (Cfam P.d) (Ufam P p) M)) :
    ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d)
      (familyProfile (inputsF P R) p M A tail z q j j') ≤ ENNReal.ofReal (loB P) := by
  intro q hq j j'
  have hd1 : 1 ≤ P.d := by omega
  have h0 := inputs_bound_low P hd1 hL hδ htime hsol hp R hR q hq
  have hlam := weights_le P hd hp
  have h1 := inputs_bound P hd1 hL hδ htime hsol hp R hR (A := 40 * P.d) (B := 3 * (40 * P.d))
    (by have := LGSpine.forty_dim_le_Lambda P hd1 hp.le; exact this) (by omega) q hq
  have := profile_bound hd1 (40 * P.d) le_rfl (inputsF P R) p N (Ufam P p) M A (Ulow P) (Ufam P p) tail z q j j'
    (by linarith [one_le_Ulow P]) (by linarith [Ufam_one P p]) (Ufam_one P p) le_rfl hM hA hA1 hz h0 h1
  exact this.trans (ENNReal.ofReal_le_ofReal (by unfold loB; linarith))

end WaveTurbulence.Flower.Fam
