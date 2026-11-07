/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Core2
/-! # FL-TYPED: the abstract profile estimate. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Typed
open WaveTurbulence.NormBridgeScratch Finset

variable {d : ℕ}

theorem term_step {p : Prop} [Decidable p] {C a g1 g2 g3 y1 y2 y3 zc wf b0 gain : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hg3 : 0 ≤ g3) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2)
    (hy3 : 0 ≤ y3) (hwf : 0 ≤ wf) (hwf0 : wf ≤ b0) (hzc : 0 ≤ zc) (hgain : 0 ≤ gain)
    (hout : ¬p → wf ≤ gain) (hZ : ¬p → y1 * g1 + y2 * g2 + y3 * g3 ≤ zc) :
    C * ((((a + y1 * (if p then 0 else g1)) + y2 * (if p then 0 else g2)) +
        y3 * (if p then 0 else g3)) * wf) ≤ C * a * b0 + C * zc * gain := by
  have e : (((a + y1 * (if p then 0 else g1)) + y2 * (if p then 0 else g2)) +
      y3 * (if p then 0 else g3)) =
      a + (y1 * (if p then 0 else g1) + y2 * (if p then 0 else g2) + y3 * (if p then 0 else g3)) := by
    ring
  rw [e]
  refine term_bound hC ha ?_ hwf hwf0 hzc hgain ?_
  · split_ifs <;> positivity
  · by_cases hp : p
    · left; simp [hp]
    · right
      refine ⟨?_, hout hp⟩
      simpa [hp] using hZ hp

theorem aux_le {y q G t : ℝ} (hy : 0 ≤ y) (hyq : y ≤ q) (hG : 0 ≤ G) (ht : t ≤ 1) (ht0 : 0 ≤ t) :
    y * (G * t) ≤ q * G := by
  calc y * (G * t) ≤ y * G := mul_le_mul_of_nonneg_left (by nlinarith) hy
    _ ≤ q * G := mul_le_mul_of_nonneg_right hyq hG

/-- The jet envelope of the endpoint-pair factor. -/
def eEjet (Γ0 Γv : ℕ → ℝ) (A M z1 z2 : ℝ) (k : ℕ) (x : Mom d) : ℝ :=
  ((mulγ Γ0 Γ0 k * (2 / M) ^ k +
    ‖(z1 : ℂ)‖ * (if ‖x‖ < A / 2 then 0 else mulγ Γv Γ0 k * (1 / A) ^ k)) +
    ‖(z2 : ℂ)‖ * (if ‖x‖ < A / 2 then 0 else mulγ Γ0 Γv k * (1 / A) ^ k)) +
    ‖(z1 : ℂ) * (z2 : ℂ)‖ * (if ‖x‖ < A / 2 then 0 else mulγ Γv Γv k * (1 / A) ^ k)

/-- The decomposed endpoint-pair factor. -/
def Edec (z1 z2 : ℝ) (u1 u2 v1 v2 : Mom d → ℂ) (y : Mom d) : ℂ :=
  ((u1 y * u2 y + (z1 : ℂ) * (v1 y * u2 y)) + (z2 : ℂ) * (u1 y * v2 y)) +
    ((z1 : ℂ) * (z2 : ℂ)) * (v1 y * v2 y)

theorem Edec_jet (m : ℕ) {Γ0 Γv : ℕ → ℝ} (hΓ0 : ∀ k, 0 ≤ Γ0 k)
    {A M z1 z2 : ℝ} (hA : 1 ≤ A) (h2A : 2 * A ≤ M)
    {u1 u2 v1 v2 : Mom d → ℂ}
    (hu1c : ContDiff ℝ (m : WithTop ℕ∞) u1) (hu2c : ContDiff ℝ (m : WithTop ℕ∞) u2)
    (hv1c : ContDiff ℝ (m : WithTop ℕ∞) v1) (hv2c : ContDiff ℝ (m : WithTop ℕ∞) v2)
    (hu1 : JetW m (fun k _ => Γ0 k * (2 / M) ^ k) u1)
    (hu2 : JetW m (fun k _ => Γ0 k * (2 / M) ^ k) u2)
    (hv1 : JetW m (fun k _ => Γv k * (1 / A) ^ k) v1)
    (hv2 : JetW m (fun k _ => Γv k * (1 / A) ^ k) v2)
    (hvan1 : ∀ y, ‖y‖ < A / 2 → v1 y = 0) (hvan2 : ∀ y, ‖y‖ < A / 2 → v2 y = 0) :
    ContDiff ℝ (m : WithTop ℕ∞) (Edec z1 z2 u1 u2 v1 v2) ∧
      JetW m (eEjet Γ0 Γv A M z1 z2) (Edec z1 z2 u1 u2 v1 v2) := by
  have hA0 : 0 < A := by linarith
  have hMpos : 0 < M := by linarith
  have hτ0 : 0 ≤ 2 / M := by positivity
  have hτ01 : 2 / M ≤ 1 / A := by rw [div_le_div_iff₀ hMpos hA0]; linarith
  have hu1' := hu1.tau_mono hΓ0 hτ0 hτ01
  have hu2' := hu2.tau_mono hΓ0 hτ0 hτ01
  have c1 := hu1c.mul hu2c
  have c2 := hv1c.mul hu2c
  have c3 := hu1c.mul hv2c
  have c4 := hv1c.mul hv2c
  have hU0 := jetMulγ hu1c hu2c hu1 hu2
  have hW1 := (jetMulγ hv1c hu2c hv1 hu2').vanish (r := A / 2)
    (fun y hy => by show v1 y * u2 y = 0; rw [hvan1 y hy, zero_mul])
  have hW2 := (jetMulγ hu1c hv2c hu1' hv2).vanish (r := A / 2)
    (fun y hy => by show u1 y * v2 y = 0; rw [hvan2 y hy, mul_zero])
  have hW3 := (jetMulγ hv1c hv2c hv1 hv2).vanish (r := A / 2)
    (fun y hy => by show v1 y * v2 y = 0; rw [hvan1 y hy, zero_mul])
  have d2 : ContDiff ℝ (m : WithTop ℕ∞) (fun y => (z1 : ℂ) * (v1 y * u2 y)) := contDiff_const.mul c2
  have d3 : ContDiff ℝ (m : WithTop ℕ∞) (fun y => (z2 : ℂ) * (u1 y * v2 y)) := contDiff_const.mul c3
  have d4 : ContDiff ℝ (m : WithTop ℕ∞) (fun y => ((z1 : ℂ) * (z2 : ℂ)) * (v1 y * v2 y)) :=
    contDiff_const.mul c4
  have c12 := c1.add d2
  have c123 := c12.add d3
  have c1234 := c123.add d4
  have hA1 := JetW.add c1 d2 hU0 (JetW.const_mul (z1 : ℂ) c2 hW1)
  have hA2 := JetW.add c12 d3 hA1 (JetW.const_mul (z2 : ℂ) c3 hW2)
  have hA3 := JetW.add c123 d4 hA2 (JetW.const_mul ((z1 : ℂ) * (z2 : ℂ)) c4 hW3)
  exact ⟨c1234, hA3⟩

theorem sum_numeric (S m : ℕ) {Γ0 Γv : ℕ → ℝ} (hΓ0 : ∀ k, 0 ≤ Γ0 k) (hΓ00 : Γ0 0 ≤ 1)
    (hΓv : ∀ k, 0 ≤ Γv k) {A M K b0 b1 z1 z2 : ℝ} (hA : 1 ≤ A) (h2A : 2 * A ≤ M) (hK : 1 ≤ K)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hM : 2 * S0Sum Γ0 m + 2 ≤ M)
    (hz1 : |z1| ≤ A ^ S / K) (hz2 : |z2| ≤ A ^ S / K) {n : ℕ} (hnm : n ≤ m)
    (x : Mom d) {wf : ℝ} (hwf : 0 ≤ wf) (hwf0 : wf ≤ b0)
    (hgain : ‖x‖ ≥ A / 2 → wf ≤ b1 * 2 ^ (2 * S) / A ^ (2 * S)) :
    ∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℝ) * (eEjet Γ0 Γv A M z1 z2 ij.1 x * wf) ≤
      2 * b0 + 2 ^ (2 * S) * TSum Γ0 Γv m * b1 / K := by
  have hA0 : 0 < A := by linarith
  have hMpos : 0 < M := by linarith
  have hS0 : 0 ≤ S0Sum Γ0 m :=
    sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (mulγ_nonneg hΓ0 hΓ0 i)
  have hτ0 : 0 ≤ 2 / M := by positivity
  have hτ1 : 1 / A ≤ 1 := (div_le_one hA0).mpr hA
  have hτ1' : 0 ≤ 1 / A := by positivity
  have hKpos : 0 < K := by linarith
  have hAS : A ^ S ≤ A ^ (2 * S) := pow_le_pow_right₀ hA (by omega)
  have hq0 : 0 ≤ A ^ (2 * S) / K := by positivity
  have hz1q : |z1| ≤ A ^ (2 * S) / K := hz1.trans (div_le_div_of_nonneg_right hAS hKpos.le)
  have hz2q : |z2| ≤ A ^ (2 * S) / K := hz2.trans (div_le_div_of_nonneg_right hAS hKpos.le)
  have hz12q : |z1| * |z2| ≤ A ^ (2 * S) / K := by
    calc |z1| * |z2| ≤ (A ^ S / K) * (A ^ S / K) :=
          mul_le_mul hz1 hz2 (abs_nonneg _) (by positivity)
      _ = A ^ (2 * S) / (K * K) := by rw [two_mul, pow_add]; field_simp
      _ ≤ A ^ (2 * S) / K :=
          div_le_div_of_nonneg_left (by positivity) hKpos (by nlinarith)
  have hgainnn : 0 ≤ b1 * 2 ^ (2 * S) / A ^ (2 * S) := by positivity
  have hterm : ∀ i : ℕ,
      (n.choose i : ℝ) * (eEjet Γ0 Γv A M z1 z2 i x * wf) ≤
        (n.choose i : ℝ) * (mulγ Γ0 Γ0 i * (2 / M) ^ i) * b0 +
          (n.choose i : ℝ) * ((mulγ Γv Γ0 i + mulγ Γ0 Γv i + mulγ Γv Γv i) * (A ^ (2 * S) / K)) *
            (b1 * 2 ^ (2 * S) / A ^ (2 * S)) := by
    intro i
    have hpt : 0 ≤ (1 / A) ^ i := pow_nonneg hτ1' _
    have hpt1 : (1 / A) ^ i ≤ 1 := pow_le_one₀ hτ1' hτ1
    have hG1 := mulγ_nonneg hΓv hΓ0 i
    have hG2 := mulγ_nonneg hΓ0 hΓv i
    have hG3 := mulγ_nonneg hΓv hΓv i
    have hG0 := mulγ_nonneg hΓ0 hΓ0 i
    have hn1 : ‖(z1 : ℂ)‖ = |z1| := by simp
    have hn2 : ‖(z2 : ℂ)‖ = |z2| := by simp
    have hn12 : ‖(z1 : ℂ) * (z2 : ℂ)‖ = |z1| * |z2| := by simp
    have := term_step (p := ‖x‖ < A / 2) (C := (n.choose i : ℝ)) (a := mulγ Γ0 Γ0 i * (2 / M) ^ i)
      (g1 := mulγ Γv Γ0 i * (1 / A) ^ i) (g2 := mulγ Γ0 Γv i * (1 / A) ^ i)
      (g3 := mulγ Γv Γv i * (1 / A) ^ i) (y1 := ‖(z1 : ℂ)‖) (y2 := ‖(z2 : ℂ)‖)
      (y3 := ‖(z1 : ℂ) * (z2 : ℂ)‖)
      (zc := (mulγ Γv Γ0 i + mulγ Γ0 Γv i + mulγ Γv Γv i) * (A ^ (2 * S) / K))
      (wf := wf) (b0 := b0) (gain := b1 * 2 ^ (2 * S) / A ^ (2 * S))
      (Nat.cast_nonneg _) (mul_nonneg hG0 (pow_nonneg hτ0 _)) (mul_nonneg hG1 hpt)
      (mul_nonneg hG2 hpt) (mul_nonneg hG3 hpt) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hwf hwf0 (mul_nonneg (by linarith) hq0) hgainnn
      (fun hp => hgain (not_lt.mp hp))
      (fun _ => by
        rw [hn1, hn2, hn12]
        have a1 := aux_le (abs_nonneg z1) hz1q hG1 hpt1 hpt
        have a2 := aux_le (abs_nonneg z2) hz2q hG2 hpt1 hpt
        have a3 := aux_le (mul_nonneg (abs_nonneg z1) (abs_nonneg z2)) hz12q hG3 hpt1 hpt
        nlinarith)
    exact this
  rw [sum_antidiag_fst n (fun i => (n.choose i : ℝ) * (eEjet Γ0 Γv A M z1 z2 i x * wf))]
  refine (sum_le_sum fun i _ => hterm i).trans ?_
  have hS : 2 / M * S0Sum Γ0 m ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hMpos]; linarith
  have hM2 : 2 / M ≤ 1 := by rw [div_le_one hMpos]; linarith
  have hlead := lead_sum_le hnm (G := mulγ Γ0 Γ0) (fun i => mulγ_nonneg hΓ0 hΓ0 i)
    (by rw [mulγ_zero]; exact mul_le_one₀ hΓ00 (hΓ0 0) hΓ00) hτ0 hM2 hS
  have hgsum := gain_sum_le hnm (g := fun i => mulγ Γv Γ0 i + mulγ Γ0 Γv i + mulγ Γv Γv i)
    (fun i => add_nonneg (add_nonneg (mulγ_nonneg hΓv hΓ0 i) (mulγ_nonneg hΓ0 hΓv i))
      (mulγ_nonneg hΓv hΓv i))
  have hAne : A ^ (2 * S) ≠ 0 := (pow_pos hA0 _).ne'
  have hsplit : ∑ i ∈ range (n + 1),
      ((n.choose i : ℝ) * (mulγ Γ0 Γ0 i * (2 / M) ^ i) * b0 +
        (n.choose i : ℝ) * ((mulγ Γv Γ0 i + mulγ Γ0 Γv i + mulγ Γv Γv i) * (A ^ (2 * S) / K)) *
          (b1 * 2 ^ (2 * S) / A ^ (2 * S))) =
      (∑ i ∈ range (n + 1), (n.choose i : ℝ) * (mulγ Γ0 Γ0 i * (2 / M) ^ i)) * b0 +
        (2 ^ (2 * S) * b1 / K) * ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
          (mulγ Γv Γ0 i + mulγ Γ0 Γv i + mulγ Γv Γv i) := by
    rw [mul_sum, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    field_simp
  rw [hsplit]
  have hc0 : 0 ≤ 2 ^ (2 * S) * b1 / K := by positivity
  have h1 := mul_le_mul_of_nonneg_right hlead hb0
  have h2 := mul_le_mul_of_nonneg_left hgsum hc0
  have : 2 ^ (2 * S) * TSum Γ0 Γv m * b1 / K = (2 ^ (2 * S) * b1 / K) * TSum Γ0 Γv m := by ring
  rw [this]
  unfold TSum
  linarith

theorem profile_core (S m : ℕ) {Γ0 Γv : ℕ → ℝ} (hΓ0 : ∀ k, 0 ≤ Γ0 k) (hΓ00 : Γ0 0 ≤ 1)
    (hΓv : ∀ k, 0 ≤ Γv k) {A M K b0 b1 z1 z2 : ℝ} (hA : 1 ≤ A) (h2A : 2 * A ≤ M) (hK : 1 ≤ K)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hM : 2 * S0Sum Γ0 m + 2 ≤ M)
    (hz1 : |z1| ≤ A ^ S / K) (hz2 : |z2| ≤ A ^ S / K)
    {F u1 u2 v1 v2 : Mom d → ℂ}
    (hFc : ContDiff ℝ (m : WithTop ℕ∞) F)
    (hF0 : ∀ l : List (Fin d), l.length ≤ m → ∀ x, jbr x ^ S * ‖wordD l F x‖ ≤ b0)
    (hF1 : ∀ l : List (Fin d), l.length ≤ m → ∀ x, jbr x ^ (3 * S) * ‖wordD l F x‖ ≤ b1)
    (hu1c : ContDiff ℝ (m : WithTop ℕ∞) u1) (hu2c : ContDiff ℝ (m : WithTop ℕ∞) u2)
    (hv1c : ContDiff ℝ (m : WithTop ℕ∞) v1) (hv2c : ContDiff ℝ (m : WithTop ℕ∞) v2)
    (hu1 : JetW m (fun k _ => Γ0 k * (2 / M) ^ k) u1)
    (hu2 : JetW m (fun k _ => Γ0 k * (2 / M) ^ k) u2)
    (hv1 : JetW m (fun k _ => Γv k * (1 / A) ^ k) v1)
    (hv2 : JetW m (fun k _ => Γv k * (1 / A) ^ k) v2)
    (hvan1 : ∀ y, ‖y‖ < A / 2 → v1 y = 0) (hvan2 : ∀ y, ‖y‖ < A / 2 → v2 y = 0) :
    ∀ l : List (Fin d), l.length ≤ m → ∀ x,
      jbr x ^ S * ‖wordD l (fun y => F y *
          ((u1 y + (z1 : ℂ) * v1 y) * (u2 y + (z2 : ℂ) * v2 y))) x‖ ≤
        2 * b0 + 2 ^ (2 * S) * TSum Γ0 Γv m * b1 / K := by
  intro l hl x
  obtain ⟨hEc, hEj⟩ := Edec_jet m hΓ0 hA h2A hu1c hu2c hv1c hv2c hu1 hu2 hv1 hv2 hvan1 hvan2
  have hfun : (fun y => F y * ((u1 y + (z1 : ℂ) * v1 y) * (u2 y + (z2 : ℂ) * v2 y))) =
      fun y => Edec z1 z2 u1 u2 v1 v2 y * F y := by
    funext y; unfold Edec; ring
  rw [hfun]
  have hFj : JetW m (fun _ (y : Mom d) => min (b0 / jbr y ^ S) (b1 / jbr y ^ (3 * S))) F := by
    intro l' hl' y
    refine le_min ?_ ?_
    · rw [le_div_iff₀ (pow_pos (jbr_pos' y) _), mul_comm]; exact hF0 l' hl' y
    · rw [le_div_iff₀ (pow_pos (jbr_pos' y) _), mul_comm]; exact hF1 l' hl' y
  have hLeib := (JetW.mul hEc hFc hEj hFj) l hl x
  have hJpos : 0 < jbr x := jbr_pos' x
  have hw : 0 < jbr x ^ S := pow_pos hJpos _
  have hA0 : 0 < A := by linarith
  have hfx0 : 0 ≤ min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S)) :=
    le_min (div_nonneg hb0 hw.le) (div_nonneg hb1 (pow_pos hJpos _).le)
  have hwf : 0 ≤ jbr x ^ S * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S)) := mul_nonneg hw.le hfx0
  have hwf0 : jbr x ^ S * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S)) ≤ b0 := by
    calc jbr x ^ S * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S)) ≤ jbr x ^ S * (b0 / jbr x ^ S) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hw.le
      _ = b0 := mul_div_cancel₀ _ hw.ne'
  have hgain : ‖x‖ ≥ A / 2 → jbr x ^ S * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S)) ≤
      b1 * 2 ^ (2 * S) / A ^ (2 * S) := by
    intro hx
    have h1 : jbr x ^ S * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S)) ≤ b1 / jbr x ^ (2 * S) := by
      calc jbr x ^ S * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S)) ≤
            jbr x ^ S * (b1 / jbr x ^ (3 * S)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hw.le
        _ = b1 / jbr x ^ (2 * S) := by
            have : jbr x ^ (3 * S) = jbr x ^ S * jbr x ^ (2 * S) := by
              rw [← pow_add]; congr 1; ring
            rw [this]; field_simp
    refine h1.trans ?_
    have hJ2 : A / 2 ≤ jbr x := hx.trans (norm_le_jbr' x)
    have h2 : (A / 2) ^ (2 * S) ≤ jbr x ^ (2 * S) := pow_le_pow_left₀ (by positivity) hJ2 _
    calc b1 / jbr x ^ (2 * S) ≤ b1 / (A / 2) ^ (2 * S) :=
          div_le_div_of_nonneg_left hb1 (by positivity) h2
      _ = b1 * 2 ^ (2 * S) / A ^ (2 * S) := by
          rw [div_pow]; field_simp
  have hsum := sum_numeric S m hΓ0 hΓ00 hΓv hA h2A hK hb0 hb1 hM hz1 hz2 (n := l.length) hl x hwf hwf0 hgain
  have e2 : jbr x ^ S * ∑ ij ∈ antidiagonal l.length, (l.length.choose ij.1 : ℝ) *
      (eEjet Γ0 Γv A M z1 z2 ij.1 x * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S))) =
      ∑ ij ∈ antidiagonal l.length, (l.length.choose ij.1 : ℝ) *
      (eEjet Γ0 Γv A M z1 z2 ij.1 x * (jbr x ^ S * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S)))) := by
    rw [mul_sum]
    refine sum_congr rfl fun ij _ => ?_
    ring
  calc jbr x ^ S * ‖wordD l (fun y => Edec z1 z2 u1 u2 v1 v2 y * F y) x‖ ≤
      jbr x ^ S * ∑ ij ∈ antidiagonal l.length, (l.length.choose ij.1 : ℝ) *
        (eEjet Γ0 Γv A M z1 z2 ij.1 x * min (b0 / jbr x ^ S) (b1 / jbr x ^ (3 * S))) :=
        mul_le_mul_of_nonneg_left hLeib hw.le
    _ = _ := e2
    _ ≤ _ := hsum

end WaveTurbulence.Flower.Typed
