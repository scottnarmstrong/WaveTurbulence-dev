/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Part2Prob

/-!
# X3 Part2Num: the parameters of Part 2 and the size of `probSum`

**The parameters** `par2 P Pm p kind`:
* `q = 2 Pm`, `A = Λ + d + 1` with `Λ = (5/4) Λ_{p+1}`;
* `B = β / (4 · 2^{Λ/2} S_L)`, with `β = e^{2N}` for `𝒳` and `β = 1` for `𝒴`, `𝒲`;
* regime A: `J = 1`, `h = 1`;
* regime B: `J = ⌈M₂^{1/50}⌉`, `h = M₂^{−1/50}`, and weights `v(j₂) = (1 − ρ) ρ^{j₂}` with `ρ = 2^{−1/100}`.

**Statement** (`probSum_le`). For `Pm ≥ 100 (d+1)²`, `probSum ≤ ofReal T`, where
`T = kindGain · B^{−q} · S_L · Q(L, ℓ')`, `ℓ' = ℓ_max + 1`, and `Q` is an explicit polynomial (`totPoly`).

**Proof.**
- Each test term is `ofReal` of `2^{q−1}(J^q C + h^{q−1} C')/λ^q` (`term_eq_ofReal`).
- The `X2Body` factor `⟨k−ζk'⟩^{−4Λ_{p+1}P}` over `λ^q ∋ ⟨k−ζk'⟩^{−Aq}` leaves `⟨k−ζk'⟩^{−(d+1)}`, summed by `S_L`.
- The `M₁`, `M₂` powers decay like `M₁^{−1} M₂^{−1}` after the test-set counts, since `Pm` is large.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree
open scoped ENNReal

variable {d : ℕ}

/-! ## The parameters -/

/-- `ρ = 2^{−1/100}`. -/
noncomputable def rho : ℝ := (2 : ℝ) ^ (-(1 / 100 : ℝ))

theorem rho_pos : 0 < rho := Real.rpow_pos_of_pos two_pos _

theorem rho_lt_one : rho < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)

/-- The threshold gain: `e^{2N}` for `𝒳`, `1` for `𝒴`, `𝒲`. -/
noncomputable def kindBeta (Ntr : ℕ) : FlowerKind → ℝ
  | .X => Real.exp (2 * (Ntr : ℝ))
  | .Y => 1
  | .W => 1

theorem kindBeta_pos (Ntr : ℕ) (kind : FlowerKind) : 0 < kindBeta Ntr kind := by
  cases kind <;> simp [kindBeta, Real.exp_pos]

theorem latSum_pos {L : ℝ} (hL : 1 ≤ L) : 0 < latSum d L :=
  (summable_jbr_rpow_neg hL).tsum_pos (fun _ => Real.rpow_nonneg (jbr_pos'' _).le _) 0
    (Real.rpow_pos_of_pos (jbr_pos'' _) _)

/-- **The parameters of Part 2.** -/
noncomputable def par2 (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) : P2Par where
  q := ((2 * Pm : ℕ) : ℝ)
  A := 5 / 4 * (P.Lambda (p + 1) : ℝ) + P.d + 1
  B := kindBeta (P.N (p + 1)) kind / (4 * 2 ^ (5 / 4 * (P.Lambda (p + 1) : ℝ) / 2) * latSum P.d P.L)
  JA := 1
  hA := 1
  JB := fun j => ⌈((2 : ℝ) ^ j * P.L) ^ (1 / 50 : ℝ)⌉₊
  hB := fun j => ((2 : ℝ) ^ j * P.L) ^ (-(1 / 50 : ℝ))
  v := fun j => (1 - rho) * rho ^ j

theorem par2_B_pos (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (hL : 1 ≤ P.L) : 0 < (par2 P Pm p kind).B := by
  have := latSum_pos (d := P.d) hL
  have := kindBeta_pos (P.N (p + 1)) kind
  show 0 < kindBeta (P.N (p + 1)) kind / (4 * 2 ^ (5 / 4 * (P.Lambda (p + 1) : ℝ) / 2) * latSum P.d P.L)
  positivity

theorem par2_v_pos (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (j : ℕ) : 0 < (par2 P Pm p kind).v j := by
  show 0 < (1 - rho) * rho ^ j
  have := rho_lt_one
  have := rho_pos
  exact mul_pos (by linarith) (pow_pos rho_pos j)

theorem par2_valid (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (hPm : 1 ≤ Pm) (hL : 1 ≤ P.L) :
    (par2 P Pm p kind).Valid := by
  have hρ0 := rho_pos
  have hρ1 := rho_lt_one
  have hM : ∀ j : ℕ, 0 < (2 : ℝ) ^ j * P.L := fun j => by positivity
  refine ⟨?_, (par2_B_pos P Pm p kind hL).le, le_rfl, by norm_num [par2], fun j => ?_, fun j => ?_,
    fun j => (par2_v_pos P Pm p kind j).le, ?_, ?_⟩
  · show (1 : ℝ) < ((2 * Pm : ℕ) : ℝ)
    have : (2 : ℕ) ≤ 2 * Pm := by omega
    exact_mod_cast lt_of_lt_of_le one_lt_two this
  · exact Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos (hM j) _)
  · show 1 ≤ ((⌈((2 : ℝ) ^ j * P.L) ^ (1 / 50 : ℝ)⌉₊ : ℕ) + 1 : ℝ) * ((2 : ℝ) ^ j * P.L) ^ (-(1 / 50 : ℝ))
    set x := ((2 : ℝ) ^ j * P.L) ^ (1 / 50 : ℝ)
    have hx : 0 < x := Real.rpow_pos_of_pos (hM j) _
    have hneg : ((2 : ℝ) ^ j * P.L) ^ (-(1 / 50 : ℝ)) = x⁻¹ := Real.rpow_neg (hM j).le _
    rw [hneg]
    have hc : x ≤ ⌈x⌉₊ := Nat.le_ceil x
    rw [← div_eq_mul_inv, le_div_iff₀ hx]
    linarith
  · exact (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
  · show ∑' j, (1 - rho) * rho ^ j ≤ 1
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1, mul_inv_cancel₀ (by linarith)]

/-! ## The `X2Body` bounds -/

section X2

variable (P : WTParams) (Pm p : ℕ) (ζ : ℤˣ) (n n' : Fin P.d → ℤ)

theorem x2Bound_plain (j₁ : ℕ) (cut2 : Option ℕ) :
    x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => FixPat.plain) (some j₁) cut2 =
      jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
        P.L ^ ((100 * P.d : ℝ) ^ 3 * Pm) * ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ)) *
          (cut2.elim 1 fun j₂ => ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ))) := by
  simp [x2Bound]

theorem x2Bound_dRoot (hPm : 1 ≤ Pm) (j₁ : ℕ) (cut2 : Option ℕ) :
    x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => FixPat.dRoot) (some j₁) cut2 =
      jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
        P.L ^ (2 * (100 * P.d : ℝ) ^ 3 * Pm) * ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ)) := by
  have h : ¬ ∀ _j : Fin (2 * Pm), False := fun h => h ⟨0, by omega⟩
  cases cut2 <;> simp [x2Bound, h]

end X2

/-! ## Terms as `ofReal` -/

theorem term_eq_ofReal {q h C C' lam : ℝ} (J : ℕ) (hq : 1 ≤ q) (hh : 0 ≤ h) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hlam : 0 < lam) :
    2 ^ (q - 1) * ((J : ℝ≥0∞) ^ q * ENNReal.ofReal C + ENNReal.ofReal h ^ (q - 1) * ENNReal.ofReal C') /
        ENNReal.ofReal lam ^ q =
      ENNReal.ofReal (2 ^ (q - 1) * ((J : ℝ) ^ q * C + h ^ (q - 1) * C') / lam ^ q) := by
  have hq0 : 0 ≤ q := by linarith
  have hq1 : 0 ≤ q - 1 := by linarith
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg hJ hq0, ENNReal.ofReal_rpow_of_nonneg hh hq1,
    ENNReal.ofReal_rpow_of_pos hlam, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show (2 : ℝ≥0∞) ^ (q - 1) = ENNReal.ofReal (2 ^ (q - 1)) by
      rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos (by positivity)]

/-! ## Real helpers -/

theorem jbr_one_le (x : Mom d) : 1 ≤ jbr x := by
  unfold jbr
  exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖x‖])

theorem kindGain_pos (Ntr : ℕ) (kind : FlowerKind) : 0 < kindGain Ntr kind := by
  cases kind <;> simp [kindGain, Real.exp_pos]

theorem rpow_div_rpow_rpow_le {x : ℝ} (hx : 1 ≤ x) (a b q c : ℝ) (h : -a - -b * q ≤ -c) :
    x ^ (-a) / (x ^ (-b)) ^ q ≤ x ^ (-c) := by
  have hx0 : 0 < x := by linarith
  rw [← Real.rpow_mul hx0.le, ← Real.rpow_sub hx0]
  exact Real.rpow_le_rpow_of_exponent_le hx h

theorem two_pow_succ_rpow_le {L : ℝ} (hL : 1 ≤ L) (j : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    ((2 : ℝ) ^ (j + 1)) ^ q ≤ 2 ^ q * ((2 : ℝ) ^ j * L) ^ q := by
  rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num), mul_comm]
  gcongr
  exact le_mul_of_one_le_right (by positivity) hL

theorem rpow_mul_rpow_le {M : ℝ} (hM : 1 ≤ M) (a b c : ℝ) (h : a + b ≤ c) : M ^ a * M ^ b ≤ M ^ c := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hM h

theorem rpow_neg_one_le_half_pow {L : ℝ} (hL : 1 ≤ L) (j : ℕ) {u : ℝ} (hu : u ≤ -1) :
    ((2 : ℝ) ^ j * L) ^ u ≤ (1 / 2) ^ j := by
  have hM : 1 ≤ (2 : ℝ) ^ j * L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  refine (Real.rpow_le_rpow_of_exponent_le hM hu).trans ?_
  rw [Real.rpow_neg_one, one_div, inv_pow]
  exact inv_anti₀ (by positivity) (le_mul_of_one_le_right (by positivity) hL)

theorem tsum_ofReal_half_pow {C : ℝ} (hC : 0 ≤ C) :
    ∑' j : ℕ, ENNReal.ofReal (C * (1 / 2) ^ j) = ENNReal.ofReal (2 * C) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (summable_geometric_two.mul_left C),
    tsum_mul_left, tsum_geometric_two, mul_comm]

theorem tsum_ofReal_jbr {L : ℝ} (hL : 1 ≤ L) {C : ℝ} (hC : 0 ≤ C) (k : Fin d → ℤ) (ζ : ℤˣ) :
    ∑' k' : Fin d → ℤ, ENNReal.ofReal (C * jbr (latticePoint L k - (ζ : ℤ) • latticePoint L k') ^
      (-((d : ℝ) + 1))) = ENNReal.ofReal (C * latSum d L) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k' => mul_nonneg hC (Real.rpow_nonneg (jbr_pos'' _).le _))
    ((summable_shift hL k ζ).mul_left C), tsum_mul_left, tsum_shift]

theorem card_ballZ_le_real {L R : ℝ} (hLR : 1 ≤ L * R) :
    ((ballZ (d := d) L R).card : ℝ) ≤ (3 * (L * R)) ^ d := by
  have h := card_ballZ_le (d := d) L R
  have h1 : ((2 * ⌊L * R⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * (L * R) := by
    push_cast
    have := Nat.floor_le (show 0 ≤ L * R by linarith)
    linarith
  calc ((ballZ (d := d) L R).card : ℝ) ≤ (((2 * ⌊L * R⌋₊ + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h
    _ = ((2 * ⌊L * R⌋₊ + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
    _ ≤ (3 * (L * R)) ^ d := by gcongr

theorem expo_ratio {Λ₀ d Pm : ℝ} (hd : 1 ≤ d) (hPm : 1 ≤ Pm) (hΛ : 40 * d ≤ Λ₀) :
    -(4 * Λ₀ * Pm) - -(5 / 4 * Λ₀ + d + 1) * (2 * Pm) ≤ -(d + 1) := by
  nlinarith [mul_le_mul_of_nonneg_left hΛ (show (0 : ℝ) ≤ Pm by linarith),
    mul_nonneg (show (0 : ℝ) ≤ Pm - 1 by linarith) (show (0 : ℝ) ≤ 58 * d - 2 by linarith)]

/-! ## Regime A -/

/-- `c_A = 2^{q−1} · 6 · L^{2(100d)³P} · kindGain · 2^q / B^q`. -/
noncomputable def cA (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) : ℝ :=
  2 ^ (((2 * Pm : ℕ) : ℝ) - 1) * 6 * P.L ^ (2 * (100 * P.d : ℝ) ^ 3 * Pm) * kindGain (P.N (p + 1)) kind *
    2 ^ ((2 * Pm : ℕ) : ℝ) / (par2 P Pm p kind).B ^ ((2 * Pm : ℕ) : ℝ)

theorem cA_nonneg (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (hL : 1 ≤ P.L) : 0 ≤ cA P Pm p kind := by
  have := par2_B_pos P Pm p kind hL
  have := kindGain_pos (P.N (p + 1)) kind
  unfold cA
  positivity

/-- **One regime-A term.** -/
theorem termA_le (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (ζ : ℤˣ) (hPm : 1 ≤ Pm) (hd : 1 ≤ P.d)
    (hΛ : 40 * P.d ≤ P.Lambda (p + 1)) (hL : 1 ≤ P.L) (j : ℕ) (k k' : Fin P.d → ℤ) :
    termA P Pm p kind ζ (par2 P Pm p kind) j k k' ≤
      ENNReal.ofReal (cA P Pm p kind * ((2 : ℝ) ^ j * P.L) ^ (-(10 * (P.d : ℝ) + 1)) *
        jbr (latticePoint P.L k - (ζ : ℤ) • latticePoint P.L k') ^ (-((P.d : ℝ) + 1))) := by
  have hB := par2_B_pos P Pm p kind hL
  have hkG := kindGain_pos (P.N (p + 1)) kind
  set q : ℝ := ((2 * Pm : ℕ) : ℝ) with hqdef
  have hPm' : (1 : ℝ) ≤ Pm := by exact_mod_cast hPm
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hΛ' : 40 * (P.d : ℝ) ≤ (P.Lambda (p + 1) : ℝ) := by exact_mod_cast hΛ
  have hq : q = 2 * Pm := by rw [hqdef]; push_cast; ring
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  set M := (2 : ℝ) ^ j * P.L with hMdef
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  set x := jbr (latticePoint P.L k - (ζ : ℤ) • latticePoint P.L k') with hxdef
  have hx1 : 1 ≤ x := jbr_one_le _
  set kG := kindGain (P.N (p + 1)) kind
  set G := x ^ (-(4 * (P.Lambda (p + 1) : ℝ) * Pm))
  set Le := P.L ^ ((100 * P.d : ℝ) ^ 3 * Pm)
  set E := P.L ^ (2 * (100 * P.d : ℝ) ^ 3 * Pm)
  set Mr := M ^ (-(80 * P.d * Pm : ℝ))
  set B := (par2 P Pm p kind).B
  set A := 5 / 4 * (P.Lambda (p + 1) : ℝ) + P.d + 1 with hAdef
  set W := x ^ (-A)
  have hG : 0 < G := Real.rpow_pos_of_pos (by linarith) _
  have hW : 0 < W := Real.rpow_pos_of_pos (by linarith) _
  have hMr : 0 < Mr := Real.rpow_pos_of_pos (by linarith) _
  have hE : 0 < E := Real.rpow_pos_of_pos (by linarith) _
  have hLe : Le ≤ E := Real.rpow_le_rpow_of_exponent_le hL (by
    have : (0 : ℝ) ≤ (100 * P.d : ℝ) ^ 3 * Pm := by positivity
    linarith)
  have hT : 0 < ((2 : ℝ) ^ (j + 1)) ^ q := by positivity
  unfold termA lamA
  rw [x2Bound_plain, x2Bound_dRoot P Pm p ζ k k' hPm]
  simp only [Option.elim_none, mul_one]
  have hlam : 0 < B * (2 ^ (j + 1))⁻¹ * wtm P.L ζ (par2 P Pm p kind).A k k' :=
    mul_pos (mul_pos hB (by positivity)) (Real.rpow_pos_of_pos (jbr_pos'' _) _)
  rw [show (par2 P Pm p kind).JA = 1 from rfl, show (par2 P Pm p kind).hA = 1 from rfl,
    show (par2 P Pm p kind).q = q from rfl,
    term_eq_ofReal 1 hq1 zero_le_one (by positivity) (by positivity) hlam]
  refine ENNReal.ofReal_le_ofReal ?_
  have hwtm : wtm P.L ζ (par2 P Pm p kind).A k k' = W := rfl
  rw [hwtm, Nat.cast_one, Real.one_rpow, Real.one_rpow, one_mul, one_mul,
    Real.mul_rpow (by positivity) hW.le, Real.mul_rpow hB.le (by positivity), Real.inv_rpow (by positivity)]
  have hBq : 0 < B ^ q := Real.rpow_pos_of_pos hB _
  have hWq : 0 < W ^ q := Real.rpow_pos_of_pos hW _
  have hratio : G / W ^ q ≤ x ^ (-((P.d : ℝ) + 1)) := by
    refine rpow_div_rpow_rpow_le hx1 _ _ _ _ ?_
    rw [hq, hAdef]
    nlinarith
  have hTle := two_pow_succ_rpow_le hL j (q := q) (by linarith)
  have hMle : M ^ q * Mr ≤ M ^ (-(10 * (P.d : ℝ) + 1)) := by
    refine rpow_mul_rpow_le hM1 _ _ _ ?_
    rw [hq]
    nlinarith
  calc 2 ^ (q - 1) * (3 * (G * Le * Mr) * kG + 3 * (G * E * Mr) * kG) /
        (B ^ q * (((2 : ℝ) ^ (j + 1)) ^ q)⁻¹ * W ^ q)
      ≤ 2 ^ (q - 1) * (6 * G * E * Mr * kG) / (B ^ q * (((2 : ℝ) ^ (j + 1)) ^ q)⁻¹ * W ^ q) := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_left hLe (mul_nonneg hG.le (mul_nonneg hMr.le hkG.le))]
    _ = (2 ^ (q - 1) * 6 * E * kG / B ^ q) * ((2 : ℝ) ^ (j + 1)) ^ q * Mr * (G / W ^ q) := by
        field_simp
    _ ≤ (2 ^ (q - 1) * 6 * E * kG / B ^ q) * (2 ^ q * M ^ q) * Mr * x ^ (-((P.d : ℝ) + 1)) := by
        gcongr
    _ = cA P Pm p kind * (M ^ q * Mr) * x ^ (-((P.d : ℝ) + 1)) := by
        unfold cA
        rw [← hqdef]
        ring
    _ ≤ cA P Pm p kind * M ^ (-(10 * (P.d : ℝ) + 1)) * x ^ (-((P.d : ℝ) + 1)) := by
        have := cA_nonneg P Pm p kind hL
        gcongr

/-- **The regime-A sum.** -/
theorem sumA_le (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (ζ : ℤˣ) (hPm : 1 ≤ Pm) (hd : 1 ≤ P.d)
    (hΛ : 40 * P.d ≤ P.Lambda (p + 1)) (hL : 1 ≤ P.L) :
    (∑' j, ∑ k ∈ testA P.L j, ∑' k', termA P Pm p kind ζ (par2 P Pm p kind) j k k') ≤
      ENNReal.ofReal (2 * (cA P Pm p kind * (3 * P.L) ^ P.d * latSum P.d P.L)) := by
  have hcA := cA_nonneg P Pm p kind hL
  have hS := (latSum_pos (d := P.d) hL).le
  rw [← tsum_ofReal_half_pow (by positivity)]
  refine ENNReal.tsum_le_tsum fun j => ?_
  set M := (2 : ℝ) ^ j * P.L with hMdef
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  have hk : ∀ k, ∑' k', termA P Pm p kind ζ (par2 P Pm p kind) j k k' ≤
      ENNReal.ofReal (cA P Pm p kind * M ^ (-(10 * (P.d : ℝ) + 1)) * latSum P.d P.L) := fun k => by
    refine (ENNReal.tsum_le_tsum fun k' => termA_le P Pm p kind ζ hPm hd hΛ hL j k k').trans (le_of_eq ?_)
    exact tsum_ofReal_jbr hL (by positivity) k ζ
  refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard : ((testA (d := P.d) P.L j).card : ℝ) ≤ (3 * (P.L * M ^ 10)) ^ P.d :=
    card_ballZ_le_real (one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ hM1))
  have hMp : M ^ ((10 * P.d : ℕ) : ℝ) * M ^ (-(10 * (P.d : ℝ) + 1)) ≤ (1 / 2) ^ j := by
    rw [← Real.rpow_add (by linarith)]
    exact rpow_neg_one_le_half_pow hL j (by push_cast; linarith)
  calc ((testA (d := P.d) P.L j).card : ℝ) * (cA P Pm p kind * M ^ (-(10 * (P.d : ℝ) + 1)) * latSum P.d P.L)
      ≤ (3 * (P.L * M ^ 10)) ^ P.d * (cA P Pm p kind * M ^ (-(10 * (P.d : ℝ) + 1)) * latSum P.d P.L) := by
        gcongr
    _ = cA P Pm p kind * (3 * P.L) ^ P.d * latSum P.d P.L *
          (M ^ ((10 * P.d : ℕ) : ℝ) * M ^ (-(10 * (P.d : ℝ) + 1))) := by
        rw [Real.rpow_natCast, pow_mul]
        ring
    _ ≤ cA P Pm p kind * (3 * P.L) ^ P.d * latSum P.d P.L * (1 / 2) ^ j := by gcongr

/-! ## Regime B -/

/-- `c_B = 2^{q−1} · 3 (2^q + 1) · L^{2(100d)³P} · kindGain · 2^q (1 − ρ)^{−q} / B^q`. -/
noncomputable def cB (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) : ℝ :=
  2 ^ (((2 * Pm : ℕ) : ℝ) - 1) * 3 * (2 ^ ((2 * Pm : ℕ) : ℝ) + 1) * P.L ^ (2 * (100 * P.d : ℝ) ^ 3 * Pm) *
    kindGain (P.N (p + 1)) kind * 2 ^ ((2 * Pm : ℕ) : ℝ) * (1 - rho) ^ (-((2 * Pm : ℕ) : ℝ)) /
      (par2 P Pm p kind).B ^ ((2 * Pm : ℕ) : ℝ)

theorem cB_nonneg (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (hL : 1 ≤ P.L) : 0 ≤ cB P Pm p kind := by
  have := par2_B_pos P Pm p kind hL
  have := kindGain_pos (P.N (p + 1)) kind
  have : 0 < 1 - rho := by have := rho_lt_one; linarith
  unfold cB
  positivity

/-- `ρ^{j q} M₂^{q/100} ≥ 1`. -/
theorem rho_pow_rpow_mul_ge {L : ℝ} (hL : 1 ≤ L) (j : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    1 ≤ (rho ^ j) ^ q * ((2 : ℝ) ^ j * L) ^ (q / 100) := by
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have e : (rho ^ j) ^ q = ((2 : ℝ) ^ j) ^ (-(q / 100)) := by
    have h1 : rho ^ j = ((2 : ℝ) ^ j) ^ (-(1 / 100 : ℝ)) := by
      unfold rho
      rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast_mul (by norm_num), mul_comm]
    rw [h1, ← Real.rpow_mul h2j.le]
    congr 1
    ring
  rw [e]
  calc (1 : ℝ) = ((2 : ℝ) ^ j) ^ (-(q / 100)) * ((2 : ℝ) ^ j) ^ (q / 100) := by
        rw [← Real.rpow_add h2j]; simp
    _ ≤ ((2 : ℝ) ^ j) ^ (-(q / 100)) * ((2 : ℝ) ^ j * L) ^ (q / 100) := by
        gcongr
        exact le_mul_of_one_le_right h2j.le hL

/-- **One regime-B term.** -/
theorem termB_le (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (ζ : ℤˣ) (hPm : 1 ≤ Pm) (hd : 1 ≤ P.d)
    (hΛ : 40 * P.d ≤ P.Lambda (p + 1)) (hL : 1 ≤ P.L) (j₁ j₂ : ℕ)
    (hcard : 0 < (dagBoxK (d := P.d) P.L (P.N (p + 1)) kind j₁).card) (k k' : Fin P.d → ℤ) :
    termB P Pm p kind ζ (par2 P Pm p kind) j₁ j₂ k k' ≤
      ENNReal.ofReal (cB P Pm p kind * ((dagBoxK (d := P.d) P.L (P.N (p + 1)) kind j₁).card : ℝ) ^
        ((2 * Pm : ℕ) : ℝ) * ((2 : ℝ) ^ j₁ * P.L) ^ (((2 * Pm : ℕ) : ℝ) - 80 * P.d * Pm) *
          ((2 : ℝ) ^ j₂ * P.L) ^ ((2 - ((2 * Pm : ℕ) : ℝ)) / 100) *
            jbr (latticePoint P.L k - (ζ : ℤ) • latticePoint P.L k') ^ (-((P.d : ℝ) + 1))) := by
  have hB := par2_B_pos P Pm p kind hL
  have hkG := kindGain_pos (P.N (p + 1)) kind
  unfold termB lamB
  rw [x2Bound_plain, x2Bound_dRoot P Pm p ζ k k' hPm]
  simp only [Option.elim_some]
  rw [show (par2 P Pm p kind).JB j₂ = ⌈((2 : ℝ) ^ j₂ * P.L) ^ (1 / 50 : ℝ)⌉₊ from rfl,
    show (par2 P Pm p kind).hB j₂ = ((2 : ℝ) ^ j₂ * P.L) ^ (-(1 / 50 : ℝ)) from rfl,
    show (par2 P Pm p kind).v j₂ = (1 - rho) * rho ^ j₂ from rfl,
    show (par2 P Pm p kind).q = ((2 * Pm : ℕ) : ℝ) from rfl,
    show wtm P.L ζ (par2 P Pm p kind).A k k' =
      jbr (latticePoint P.L k - (ζ : ℤ) • latticePoint P.L k') ^ (-(5 / 4 * (P.Lambda (p + 1) : ℝ) + P.d + 1))
      from rfl]
  unfold cB
  set q : ℝ := ((2 * Pm : ℕ) : ℝ) with hqdef
  have hPm' : (1 : ℝ) ≤ Pm := by exact_mod_cast hPm
  have hd' : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hΛ' : 40 * (P.d : ℝ) ≤ (P.Lambda (p + 1) : ℝ) := by exact_mod_cast hΛ
  have hq : q = 2 * Pm := by rw [hqdef]; push_cast; ring
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  set c : ℝ := ((dagBoxK (d := P.d) P.L (P.N (p + 1)) kind j₁).card : ℝ) with hcdef
  have hc : 0 < c := Nat.cast_pos.2 hcard
  clear_value c
  set M₂ := (2 : ℝ) ^ j₂ * P.L with hM₂def
  have hM₂ : 1 ≤ M₂ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  have hM₂0 : 0 < M₂ := by linarith
  set y := M₂ ^ (1 / 50 : ℝ) with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow hM₂ (by norm_num)
  set Jr : ℝ := ((⌈y⌉₊ : ℕ) : ℝ) with hJrdef
  have hJr : Jr ≤ 2 * y := by
    have := Nat.ceil_lt_add_one (show 0 ≤ y by linarith)
    linarith
  have hJr0 : 0 ≤ Jr := Nat.cast_nonneg _
  clear_value Jr
  set M₁ := (2 : ℝ) ^ j₁ * P.L with hM₁def
  have hM₁ : 1 ≤ M₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  set x := jbr (latticePoint P.L k - (ζ : ℤ) • latticePoint P.L k') with hxdef
  have hx1 : 1 ≤ x := jbr_one_le _
  set kG := kindGain (P.N (p + 1)) kind
  set G := x ^ (-(4 * (P.Lambda (p + 1) : ℝ) * Pm))
  set Le := P.L ^ ((100 * P.d : ℝ) ^ 3 * Pm)
  set E := P.L ^ (2 * (100 * P.d : ℝ) ^ 3 * Pm)
  set Mr := M₁ ^ (-(80 * P.d * Pm : ℝ))
  set B := (par2 P Pm p kind).B
  set A := 5 / 4 * (P.Lambda (p + 1) : ℝ) + P.d + 1 with hAdef
  set W := x ^ (-A)
  set h := M₂ ^ (-(1 / 50 : ℝ)) with hhdef
  set v := (1 - rho) * rho ^ j₂ with hvdef
  have hρ0 := rho_pos
  have hρ1 := rho_lt_one
  have hv : 0 < v := mul_pos (by linarith) (pow_pos hρ0 _)
  have hG : 0 < G := Real.rpow_pos_of_pos (by linarith) _
  have hW : 0 < W := Real.rpow_pos_of_pos (by linarith) _
  have hMr : 0 < Mr := Real.rpow_pos_of_pos (by linarith) _
  have hE : 0 < E := Real.rpow_pos_of_pos (by linarith) _
  have hLe0 : 0 < Le := Real.rpow_pos_of_pos (by linarith) _
  have hLe : Le ≤ E := Real.rpow_le_rpow_of_exponent_le hL (by
    have : (0 : ℝ) ≤ (100 * P.d : ℝ) ^ 3 * Pm := by positivity
    linarith)
  have hh0 : 0 ≤ h := Real.rpow_nonneg hM₂0.le _
  have hM2P : 0 ≤ M₂ ^ (-(Pm / 9 : ℝ)) := Real.rpow_nonneg hM₂0.le _
  have hT : 0 < ((2 : ℝ) ^ (j₁ + 1)) ^ q := by positivity
  have hT' : 0 < ((2 : ℝ) ^ (j₁ + 1))⁻¹ := by positivity
  have hlam : 0 < B * ((2 : ℝ) ^ (j₁ + 1))⁻¹ * (v / c) * W :=
    mul_pos (mul_pos (mul_pos hB hT') (div_pos hv hc)) hW
  have hC1 : 0 ≤ 3 * (G * Le * Mr * M₂ ^ (-(Pm / 9 : ℝ))) * kG :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg hG.le hLe0.le) hMr.le) hM2P))
      hkG.le
  have hC2 : 0 ≤ 3 * (G * E * Mr) * kG :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hG.le hE.le) hMr.le)) hkG.le
  rw [term_eq_ofReal _ hq1 hh0 hC1 hC2 hlam]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hJrdef, Real.mul_rpow (mul_nonneg (mul_nonneg hB.le hT'.le) (div_pos hv hc).le) hW.le,
    Real.mul_rpow (mul_nonneg hB.le hT'.le) (div_pos hv hc).le, Real.mul_rpow hB.le hT'.le,
    Real.inv_rpow (by positivity), Real.div_rpow hv.le hc.le]
  -- the time-sup factors
  have hJq : Jr ^ q * M₂ ^ (-(Pm / 9 : ℝ)) ≤ 2 ^ q * M₂ ^ (-((q - 1) / 50)) := by
    have h1 : Jr ^ q ≤ 2 ^ q * M₂ ^ (q / 50) := by
      calc Jr ^ q ≤ (2 * y) ^ q := Real.rpow_le_rpow hJr0 hJr (by linarith)
        _ = 2 ^ q * M₂ ^ (q / 50) := by
          rw [Real.mul_rpow (by norm_num) (by linarith), hydef, ← Real.rpow_mul hM₂0.le]
          congr 2
          ring
    calc Jr ^ q * M₂ ^ (-(Pm / 9 : ℝ)) ≤ 2 ^ q * M₂ ^ (q / 50) * M₂ ^ (-(Pm / 9 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 hM2P
      _ ≤ 2 ^ q * M₂ ^ (-((q - 1) / 50)) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg zero_le_two _)
        refine rpow_mul_rpow_le hM₂ _ _ _ ?_
        rw [hq]
        linarith
  have hhq : h ^ (q - 1) = M₂ ^ (-((q - 1) / 50)) := by
    rw [hhdef, ← Real.rpow_mul hM₂0.le]
    congr 1
    ring
  have hρq : 0 < (rho ^ j₂) ^ q := Real.rpow_pos_of_pos (pow_pos hρ0 _) _
  have hvq : (v ^ q)⁻¹ ≤ (1 - rho) ^ (-q) * M₂ ^ (q / 100) := by
    have h1 := rho_pow_rpow_mul_ge hL j₂ (q := q) (by linarith)
    rw [hvdef, Real.mul_rpow (by linarith) (pow_pos hρ0 _).le, mul_inv, Real.rpow_neg (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.rpow_nonneg (by linarith) _))
    rw [inv_le_iff_one_le_mul₀ hρq, mul_comm]
    exact h1
  have hBq : 0 < B ^ q := Real.rpow_pos_of_pos hB _
  have hWq : 0 < W ^ q := Real.rpow_pos_of_pos hW _
  have hvq0 : 0 < v ^ q := Real.rpow_pos_of_pos hv _
  have hcq : 0 < c ^ q := Real.rpow_pos_of_pos hc _
  have hratio : G / W ^ q ≤ x ^ (-((P.d : ℝ) + 1)) := by
    refine rpow_div_rpow_rpow_le hx1 _ _ _ _ ?_
    rw [hq, hAdef]
    exact expo_ratio hd' hPm' hΛ'
  have hTle := two_pow_succ_rpow_le hL j₁ (q := q) (by linarith)
  have hnum : Jr ^ q * (3 * (G * Le * Mr * M₂ ^ (-(Pm / 9 : ℝ))) * kG) + h ^ (q - 1) * (3 * (G * E * Mr) * kG) ≤
      3 * G * E * Mr * kG * ((2 ^ q + 1) * M₂ ^ (-((q - 1) / 50))) := by
    rw [hhq]
    have e1 : Jr ^ q * (3 * (G * Le * Mr * M₂ ^ (-(Pm / 9 : ℝ))) * kG) =
        (3 * G * Mr * kG) * Le * (Jr ^ q * M₂ ^ (-(Pm / 9 : ℝ))) := by ring
    rw [e1]
    have h3 : 0 ≤ 3 * G * Mr * kG := by
      have := hG.le; have := hMr.le; have := hkG.le; positivity
    have h4 : (3 * G * Mr * kG) * Le * (Jr ^ q * M₂ ^ (-(Pm / 9 : ℝ))) ≤
        (3 * G * Mr * kG) * E * (2 ^ q * M₂ ^ (-((q - 1) / 50))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hLe h3) hJq
        (mul_nonneg (Real.rpow_nonneg hJr0 _) hM2P) (mul_nonneg h3 hE.le)
    refine (add_le_add_left h4 _).trans (le_of_eq ?_)
    ring
  have hM2e : M₂ ^ (q / 100) * M₂ ^ (-((q - 1) / 50)) = M₂ ^ ((2 - q) / 100) := by
    rw [← Real.rpow_add hM₂0]
    congr 1
    ring
  have hM1e : M₁ ^ q * Mr = M₁ ^ (q - 80 * P.d * Pm) := by
    rw [← Real.rpow_add (by linarith), sub_eq_add_neg]
  have hK : 0 ≤ 2 ^ (q - 1) * 3 * (2 ^ q + 1) * E * kG / B ^ q :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg zero_le_two _) (by norm_num))
      (add_nonneg (Real.rpow_nonneg zero_le_two _) zero_le_one)) hE.le) hkG.le) hBq.le
  have h1ρ : 0 < (1 - rho) ^ (-q) := Real.rpow_pos_of_pos (by linarith) _
  have hM2a : 0 ≤ M₂ ^ (-((q - 1) / 50)) := Real.rpow_nonneg hM₂0.le _
  have hM2q : 0 ≤ M₂ ^ (q / 100) := Real.rpow_nonneg hM₂0.le _
  have hM1q : 0 ≤ M₁ ^ q := Real.rpow_nonneg (by linarith) _
  have h2q : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg zero_le_two _
  have hb1 : 0 ≤ (2 ^ (q - 1) * 3 * (2 ^ q + 1) * E * kG / B ^ q) * (2 ^ q * M₁ ^ q) * c ^ q :=
    mul_nonneg (mul_nonneg hK (mul_nonneg h2q hM1q)) hcq.le
  calc 2 ^ (q - 1) * (Jr ^ q * (3 * (G * Le * Mr * M₂ ^ (-(Pm / 9 : ℝ))) * kG) +
          h ^ (q - 1) * (3 * (G * E * Mr) * kG)) /
        (B ^ q * (((2 : ℝ) ^ (j₁ + 1)) ^ q)⁻¹ * (v ^ q / c ^ q) * W ^ q)
      ≤ 2 ^ (q - 1) * (3 * G * E * Mr * kG * ((2 ^ q + 1) * M₂ ^ (-((q - 1) / 50)))) /
          (B ^ q * (((2 : ℝ) ^ (j₁ + 1)) ^ q)⁻¹ * (v ^ q / c ^ q) * W ^ q) := by
        refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum
          (Real.rpow_nonneg zero_le_two _)) ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg hBq.le (inv_nonneg.2 hT.le)) (div_nonneg hvq0.le hcq.le))
          hWq.le
    _ = (2 ^ (q - 1) * 3 * (2 ^ q + 1) * E * kG / B ^ q) * ((2 : ℝ) ^ (j₁ + 1)) ^ q * c ^ q *
          (v ^ q)⁻¹ * Mr * M₂ ^ (-((q - 1) / 50)) * (G / W ^ q) := by
        have hden : B ^ q * (((2 : ℝ) ^ (j₁ + 1)) ^ q)⁻¹ * (v ^ q / c ^ q) * W ^ q =
            (B ^ q * v ^ q * W ^ q) / (((2 : ℝ) ^ (j₁ + 1)) ^ q * c ^ q) := by
          field_simp
        rw [hden, div_div_eq_mul_div]
        field_simp
    _ ≤ (2 ^ (q - 1) * 3 * (2 ^ q + 1) * E * kG / B ^ q) * (2 ^ q * M₁ ^ q) * c ^ q *
          ((1 - rho) ^ (-q) * M₂ ^ (q / 100)) * Mr * M₂ ^ (-((q - 1) / 50)) * x ^ (-((P.d : ℝ) + 1)) := by
        refine mul_le_mul ?_ hratio (div_nonneg hG.le hWq.le)
          (mul_nonneg (mul_nonneg (mul_nonneg hb1 (mul_nonneg h1ρ.le hM2q)) hMr.le) hM2a)
        refine mul_le_mul_of_nonneg_right ?_ hM2a
        refine mul_le_mul_of_nonneg_right ?_ hMr.le
        refine mul_le_mul ?_ hvq (inv_nonneg.2 hvq0.le) hb1
        refine mul_le_mul_of_nonneg_right ?_ hcq.le
        exact mul_le_mul_of_nonneg_left hTle hK
    _ = 2 ^ (q - 1) * 3 * (2 ^ q + 1) * E * kG * 2 ^ q * (1 - rho) ^ (-q) / B ^ q * c ^ q *
          (M₁ ^ q * Mr) * (M₂ ^ (q / 100) * M₂ ^ (-((q - 1) / 50))) * x ^ (-((P.d : ℝ) + 1)) := by
        ring
    _ = 2 ^ (q - 1) * 3 * (2 ^ q + 1) * E * kG * 2 ^ q * (1 - rho) ^ (-q) / B ^ q * c ^ q *
          M₁ ^ (q - 80 * P.d * Pm) * M₂ ^ ((2 - q) / 100) * x ^ (-((P.d : ℝ) + 1)) := by
        rw [hM1e, hM2e]

/-! ## Test-set counts -/

theorem card_dagBox_le_nat (L R : ℝ) : (dagBox (d := d) L R).card ≤ 3 * (2 * ⌊L * R⌋₊ + 1) ^ (3 * d) := by
  classical
  unfold dagBox
  rw [Finset.card_sigma]
  calc ∑ i : Fin 3, ((Fintype.piFinset fun m : Fin 3 =>
          if m = i then ({0} : Finset (Fin d → ℤ)) else ballZ L R).subtype (fun w => w i = 0)).card
      ≤ ∑ _i : Fin 3, (2 * ⌊L * R⌋₊ + 1) ^ (3 * d) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.card_subtype]
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Fintype.card_piFinset]
        calc ∏ m : Fin 3, (if m = i then ({0} : Finset (Fin d → ℤ)) else ballZ L R).card
            ≤ ∏ _m : Fin 3, (2 * ⌊L * R⌋₊ + 1) ^ d := by
              refine Finset.prod_le_prod fun m _ => ?_
              split_ifs
              · rw [Finset.card_singleton]
                exact Nat.one_le_pow _ _ (by omega)
              · exact card_ballZ_le L R
          _ = (2 * ⌊L * R⌋₊ + 1) ^ (3 * d) := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm d 3]
    _ = 3 * (2 * ⌊L * R⌋₊ + 1) ^ (3 * d) := by simp

theorem card_dagBox_le_real {L R Y : ℝ} (hY : 1 ≤ Y) (hLR0 : 0 ≤ L * R) (hLR : L * R ≤ Y) :
    ((dagBox (d := d) L R).card : ℝ) ≤ (9 * Y) ^ (3 * d + 1) := by
  have h := card_dagBox_le_nat (d := d) L R
  have h1 : ((2 * ⌊L * R⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Y := by
    push_cast
    have := Nat.floor_le hLR0
    linarith
  calc ((dagBox (d := d) L R).card : ℝ) ≤ ((3 * (2 * ⌊L * R⌋₊ + 1) ^ (3 * d) : ℕ) : ℝ) := by exact_mod_cast h
    _ = 3 * ((2 * ⌊L * R⌋₊ + 1 : ℕ) : ℝ) ^ (3 * d) := by push_cast; ring
    _ ≤ 3 * (3 * Y) ^ (3 * d) := by gcongr
    _ ≤ (9 * Y) * (9 * Y) ^ (3 * d) := by
        gcongr
        · linarith
        · linarith
    _ = (9 * Y) ^ (3 * d + 1) := by ring

theorem floor_bound {a Θ : ℝ} (ha : 0 ≤ a) (h : 3 * a ≤ Θ) (hΘ : 1 ≤ Θ) :
    ((2 * ⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ Θ := by
  push_cast
  have := Nat.floor_le ha
  by_cases ha1 : 1 ≤ a
  · linarith
  · push Not at ha1
    have : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.2 ha1
    rw [this]
    push_cast
    linarith

theorem card_testB_le_real (P : WTParams) (Ntr : ℕ) (kind : FlowerKind) (hL : 1 ≤ P.L) (j₁ j₂ : ℕ) :
    ((testB (d := P.d) P.L Ntr kind j₁ j₂).card : ℝ) ≤
      (P.d + 2) * (400 * P.L ^ 2 * ((leafMax Ntr kind + 1 : ℝ) * ((2 : ℝ) ^ j₁ * P.L)) ^ 2 *
        ((2 : ℝ) ^ j₂ * P.L)) ^ (P.d * (P.d + 1)) := by
  have hL0 : 0 < P.L := by linarith
  set ℓ : ℝ := (leafMax Ntr kind : ℝ)
  have hℓ : 0 ≤ ℓ := Nat.cast_nonneg _
  set M₁ := (2 : ℝ) ^ j₁ * P.L
  set M₂ := (2 : ℝ) ^ j₂ * P.L
  have hM₁ : 1 ≤ M₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  have hM₂ : 1 ≤ M₂ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  set Z := (ℓ + 1) * M₁
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le (by linarith) hM₁
  set Θ := 400 * P.L ^ 2 * Z ^ 2 * M₂
  have hΘ : 1 ≤ Θ := by
    have h1 : 1 ≤ P.L ^ 2 := one_le_pow₀ hL
    have h2 : 1 ≤ Z ^ 2 := one_le_pow₀ hZ
    have : 1 ≤ P.L ^ 2 * Z ^ 2 * M₂ :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hM₂
    linarith
  have hB₀ : kerB0K P.L Ntr kind j₁ ≤ 2 * Z := by
    unfold kerB0K
    have : ℓ * M₁ ≤ Z := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hB₀0 := kerB0K_nonneg P.L Ntr kind hL0 j₁
  have hZ2 : 1 ≤ Z ^ 2 := one_le_pow₀ hZ
  have hM2le : M₂ ≤ Z ^ 2 * M₂ := le_mul_of_one_le_left (by linarith) hZ2
  have hZM1 : 1 ≤ Z ^ 2 * M₂ := one_le_mul_of_one_le_of_one_le hZ2 hM₂
  have hZZ : Z ≤ Z ^ 2 := by nlinarith
  have hZ2M' : Z ^ 2 ≤ Z ^ 2 * M₂ := le_mul_of_one_le_right (by positivity) hM₂
  have hZ2M : Z ≤ Z ^ 2 * M₂ := hZZ.trans hZ2M'
  have hB2 : kerB0K P.L Ntr kind j₁ ^ 2 ≤ 4 * Z ^ 2 := by nlinarith
  have hR : kerRK P.L Ntr kind j₁ j₂ ≤ 34 * Z ^ 2 * M₂ := by
    unfold kerRK
    linarith
  have hMr : Mrep P.L Ntr kind j₁ j₂ ≤ 21 * Z ^ 2 * M₂ := by
    unfold Mrep
    linarith
  have hR0 := kerRK_nonneg P.L Ntr kind hL0 j₁ j₂
  have hMr0 := Mrep_nonneg P.L Ntr kind hL0 j₁ j₂
  have hLZ : P.L * (Z ^ 2 * M₂) ≤ P.L ^ 2 * Z ^ 2 * M₂ := by
    have : 0 ≤ Z ^ 2 * M₂ := by positivity
    nlinarith
  -- the two parts
  have h1 : ((ballZ (d := P.d) P.L (kerRK P.L Ntr kind j₁ j₂)).card : ℝ) ≤ Θ ^ P.d := by
    refine (Nat.cast_le.2 (card_ballZ_le _ _)).trans ?_
    push_cast
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have := floor_bound (a := P.L * kerRK P.L Ntr kind j₁ j₂) (Θ := Θ) (by positivity) (by nlinarith) hΘ
    push_cast at this
    exact this
  obtain ⟨-, hrc, -⟩ := repSet_spec (d := P.d) hL hMr0 (repDom (d := P.d) P.L Ntr kind j₁ j₂)
  have h2 : ((repSet (d := P.d) P.L (Mrep P.L Ntr kind j₁ j₂) (repDom (d := P.d) P.L Ntr kind j₁ j₂)).card : ℝ) ≤
      (P.d + 1) * Θ ^ (P.d * (P.d + 1)) := by
    refine (Nat.cast_le.2 hrc).trans ?_
    push_cast
    have hA := floor_bound (a := P.L * Mrep P.L Ntr kind j₁ j₂) (Θ := Θ) (by positivity) (by nlinarith) hΘ
    have hB := floor_bound (a := P.L ^ 2 * Mrep P.L Ntr kind j₁ j₂) (Θ := Θ) (by positivity) (by nlinarith) hΘ
    push_cast at hA hB
    have hΘe : Θ ^ (P.d * (P.d + 1)) = (Θ ^ P.d * Θ) ^ P.d := by
      rw [← pow_succ, ← pow_mul, Nat.mul_comm]
    rw [hΘe]
    gcongr
  have hΘd : Θ ^ P.d ≤ Θ ^ (P.d * (P.d + 1)) := pow_le_pow_right₀ hΘ (Nat.le_mul_of_pos_right _ (by omega))
  have key : (testB (d := P.d) P.L Ntr kind j₁ j₂).card ≤ (ballZ (d := P.d) P.L (kerRK P.L Ntr kind j₁ j₂)).card +
      (repSet (d := P.d) P.L (Mrep P.L Ntr kind j₁ j₂) (repDom (d := P.d) P.L Ntr kind j₁ j₂)).card := by
    unfold testB
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_filter_le _ _) _)
  calc ((testB (d := P.d) P.L Ntr kind j₁ j₂).card : ℝ)
      ≤ ((ballZ (d := P.d) P.L (kerRK P.L Ntr kind j₁ j₂)).card : ℝ) +
        ((repSet (d := P.d) P.L (Mrep P.L Ntr kind j₁ j₂) (repDom (d := P.d) P.L Ntr kind j₁ j₂)).card : ℝ) := by
        exact_mod_cast key
    _ ≤ Θ ^ (P.d * (P.d + 1)) + (P.d + 1) * Θ ^ (P.d * (P.d + 1)) := by linarith
    _ = (P.d + 2) * Θ ^ (P.d * (P.d + 1)) := by ring

/-! ## The regime-B sum -/

theorem expo_M1 {d Pm : ℝ} (hd : 1 ≤ d) (hPm : 100 * (d + 1) ^ 2 ≤ Pm) :
    (3 * d + 1) * (2 * Pm + 1) + 2 * (d * (d + 1)) + (2 * Pm - 80 * d * Pm) ≤ -1 := by
  have h74 : (70 : ℝ) ≤ 74 * d - 4 := by linarith
  have h1 := mul_le_mul_of_nonneg_right hPm (show (0 : ℝ) ≤ 74 * d - 4 by linarith)
  have h2 := mul_le_mul_of_nonneg_left h74 (show (0 : ℝ) ≤ 100 * (d + 1) ^ 2 by positivity)
  nlinarith

theorem expo_M2 {d Pm : ℝ} (hd : 1 ≤ d) (hPm : 100 * (d + 1) ^ 2 ≤ Pm) :
    d * (d + 1) + (2 - 2 * Pm) / 100 ≤ -1 := by
  nlinarith

/-- `K_B = (9 L ℓ')^{(3d+1)(q+1)} (d + 2) (400 L² ℓ'²)^{d(d+1)}`. -/
noncomputable def KB (P : WTParams) (Pm Ntr : ℕ) (kind : FlowerKind) : ℝ :=
  (9 * P.L * (leafMax Ntr kind + 1 : ℝ)) ^ ((3 * P.d + 1 : ℝ) * (((2 * Pm : ℕ) : ℝ) + 1)) * (P.d + 2) *
    (400 * P.L ^ 2 * (leafMax Ntr kind + 1 : ℝ) ^ 2) ^ (P.d * (P.d + 1))

theorem powB_le {L ℓ' c tB : ℝ} {d Pm : ℕ} (j₁ j₂ : ℕ) (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ') (hd : 1 ≤ d)
    (hPm : 100 * ((d : ℝ) + 1) ^ 2 ≤ Pm) (hc : 0 < c)
    (hcb : c ≤ (9 * (L * ℓ' * ((2 : ℝ) ^ j₁ * L))) ^ (3 * d + 1)) (htB0 : 0 ≤ tB)
    (htB : tB ≤ (d + 2) * (400 * L ^ 2 * (ℓ' * ((2 : ℝ) ^ j₁ * L)) ^ 2 * ((2 : ℝ) ^ j₂ * L)) ^ (d * (d + 1))) :
    c * c ^ ((2 * Pm : ℕ) : ℝ) * tB * ((2 : ℝ) ^ j₁ * L) ^ (((2 * Pm : ℕ) : ℝ) - 80 * d * Pm) *
        ((2 : ℝ) ^ j₂ * L) ^ ((2 - ((2 * Pm : ℕ) : ℝ)) / 100) ≤
      (9 * L * ℓ') ^ ((3 * d + 1 : ℝ) * (((2 * Pm : ℕ) : ℝ) + 1)) * (d + 2) *
        (400 * L ^ 2 * ℓ' ^ 2) ^ (d * (d + 1)) * ((1 / 2) ^ j₁ * (1 / 2) ^ j₂) := by
  set q : ℝ := ((2 * Pm : ℕ) : ℝ) with hqdef
  have hq : q = 2 * Pm := by rw [hqdef]; push_cast; ring
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set M₁ := (2 : ℝ) ^ j₁ * L with hM₁def
  set M₂ := (2 : ℝ) ^ j₂ * L with hM₂def
  have hM₁ : 1 ≤ M₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  have hM₂ : 1 ≤ M₂ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hq0 : 0 ≤ q + 1 := by rw [hq]; positivity
  set r : ℝ := (3 * d + 1 : ℝ) * (q + 1) with hrdef
  set n : ℕ := d * (d + 1) with hndef
  have e1 : c * c ^ q = c ^ (q + 1) := by rw [Real.rpow_add_one hc.ne']; ring
  have h1 : c ^ (q + 1) ≤ (9 * L * ℓ') ^ r * M₁ ^ r := by
    calc c ^ (q + 1) ≤ ((9 * (L * ℓ' * M₁)) ^ (3 * d + 1)) ^ (q + 1) := Real.rpow_le_rpow hc.le hcb hq0
      _ = (9 * (L * ℓ' * M₁)) ^ r := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hrdef]
          push_cast
          ring_nf
      _ = (9 * L * ℓ') ^ r * M₁ ^ r := by
          rw [show 9 * (L * ℓ' * M₁) = (9 * L * ℓ') * M₁ by ring, Real.mul_rpow (by positivity) hM₁0.le]
  have h2 : tB ≤ (d + 2) * (400 * L ^ 2 * ℓ' ^ 2) ^ n * (M₁ ^ (2 * n) * M₂ ^ n) := by
    refine htB.trans (le_of_eq ?_)
    rw [pow_mul, mul_pow, mul_pow, mul_pow]
    ring
  have h3 : M₁ ^ r * M₁ ^ (2 * n) * M₁ ^ (q - 80 * d * Pm) ≤ (1 / 2) ^ j₁ := by
    rw [← Real.rpow_natCast M₁ (2 * n), ← Real.rpow_add hM₁0, ← Real.rpow_add hM₁0]
    refine rpow_neg_one_le_half_pow hL j₁ ?_
    rw [hrdef, hq, hndef]
    push_cast
    have := expo_M1 hd' hPm
    linarith
  have h4 : M₂ ^ n * M₂ ^ ((2 - q) / 100) ≤ (1 / 2) ^ j₂ := by
    rw [← Real.rpow_natCast M₂ n, ← Real.rpow_add hM₂0]
    refine rpow_neg_one_le_half_pow hL j₂ ?_
    rw [hq, hndef]
    push_cast
    have := expo_M2 hd' hPm
    linarith
  have hA : 0 ≤ (9 * L * ℓ') ^ r := Real.rpow_nonneg (by positivity) _
  have hB : 0 ≤ (400 * L ^ 2 * ℓ' ^ 2) ^ n := by positivity
  have hM1r : 0 ≤ M₁ ^ r := Real.rpow_nonneg hM₁0.le _
  have hM1e : 0 ≤ M₁ ^ (q - 80 * d * Pm) := Real.rpow_nonneg hM₁0.le _
  have hM2e : 0 ≤ M₂ ^ ((2 - q) / 100) := Real.rpow_nonneg hM₂0.le _
  calc c * c ^ q * tB * M₁ ^ (q - 80 * d * Pm) * M₂ ^ ((2 - q) / 100)
      = c ^ (q + 1) * tB * M₁ ^ (q - 80 * d * Pm) * M₂ ^ ((2 - q) / 100) := by rw [e1]
    _ ≤ ((9 * L * ℓ') ^ r * M₁ ^ r) * ((d + 2) * (400 * L ^ 2 * ℓ' ^ 2) ^ n * (M₁ ^ (2 * n) * M₂ ^ n)) *
          M₁ ^ (q - 80 * d * Pm) * M₂ ^ ((2 - q) / 100) := by
        gcongr
    _ = (9 * L * ℓ') ^ r * (d + 2) * (400 * L ^ 2 * ℓ' ^ 2) ^ n *
          ((M₁ ^ r * M₁ ^ (2 * n) * M₁ ^ (q - 80 * d * Pm)) * (M₂ ^ n * M₂ ^ ((2 - q) / 100))) := by ring
    _ ≤ (9 * L * ℓ') ^ r * (d + 2) * (400 * L ^ 2 * ℓ' ^ 2) ^ n * ((1 / 2) ^ j₁ * (1 / 2) ^ j₂) := by
        gcongr

/-- **The regime-B sum.** -/
theorem sumB_le (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (ζ : ℤˣ)
    (hPm : 100 * ((P.d : ℝ) + 1) ^ 2 ≤ Pm) (hPm1 : 1 ≤ Pm) (hd : 1 ≤ P.d)
    (hΛ : 40 * P.d ≤ P.Lambda (p + 1)) (hL : 1 ≤ P.L) :
    (∑' j₁, ∑' j₂, ∑ _x ∈ dagBoxK (d := P.d) P.L (P.N (p + 1)) kind j₁,
      ∑ k ∈ testB P.L (P.N (p + 1)) kind j₁ j₂, ∑' k', termB P Pm p kind ζ (par2 P Pm p kind) j₁ j₂ k k') ≤
      ENNReal.ofReal (4 * (cB P Pm p kind * latSum P.d P.L * KB P Pm (P.N (p + 1)) kind)) := by
  set N := P.N (p + 1)
  have hcB := cB_nonneg P Pm p kind hL
  have hS := (latSum_pos (d := P.d) hL).le
  set ℓ' : ℝ := (leafMax N kind : ℝ) + 1 with hℓ'def
  have hℓ' : 1 ≤ ℓ' := by have : (0 : ℝ) ≤ leafMax N kind := Nat.cast_nonneg _; linarith
  have hKB : 0 ≤ KB P Pm N kind := by
    unfold KB
    have : (0 : ℝ) ≤ leafMax N kind := Nat.cast_nonneg _
    positivity
  set C := cB P Pm p kind * latSum P.d P.L * KB P Pm N kind with hCdef
  have hC : 0 ≤ C := by positivity
  rw [show 4 * C = 2 * (2 * C) by ring, ← tsum_ofReal_half_pow (by positivity)]
  refine ENNReal.tsum_le_tsum fun j₁ => ?_
  rw [show 2 * C * (1 / 2) ^ j₁ = 2 * (C * (1 / 2) ^ j₁) by ring, ← tsum_ofReal_half_pow (by positivity)]
  refine ENNReal.tsum_le_tsum fun j₂ => ?_
  set box := dagBoxK (d := P.d) P.L N kind j₁
  rcases Nat.eq_zero_or_pos box.card with h0 | hpos
  · rw [Finset.card_eq_zero.1 h0, Finset.sum_empty]
    exact zero_le
  set c : ℝ := (box.card : ℝ) with hcdef
  have hc : 0 < c := Nat.cast_pos.2 hpos
  set tB : ℝ := ((testB (d := P.d) P.L N kind j₁ j₂).card : ℝ)
  set T := cB P Pm p kind * c ^ ((2 * Pm : ℕ) : ℝ) * ((2 : ℝ) ^ j₁ * P.L) ^ (((2 * Pm : ℕ) : ℝ) - 80 * P.d * Pm) *
    ((2 : ℝ) ^ j₂ * P.L) ^ ((2 - ((2 * Pm : ℕ) : ℝ)) / 100) with hTdef
  have hT : 0 ≤ T := by
    have := Real.rpow_nonneg hc.le ((2 * Pm : ℕ) : ℝ)
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 ^ j₁ * P.L by positivity) (((2 * Pm : ℕ) : ℝ) - 80 * P.d * Pm)
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 ^ j₂ * P.L by positivity) ((2 - ((2 * Pm : ℕ) : ℝ)) / 100)
    positivity
  have hk : ∀ k, ∑' k', termB P Pm p kind ζ (par2 P Pm p kind) j₁ j₂ k k' ≤ ENNReal.ofReal (T * latSum P.d P.L) :=
    fun k => (ENNReal.tsum_le_tsum fun k' => termB_le P Pm p kind ζ hPm1 hd hΛ hL j₁ j₂ hpos k k').trans
      (le_of_eq (tsum_ofReal_jbr hL hT k ζ))
  calc ∑ _x ∈ box, ∑ k ∈ testB P.L N kind j₁ j₂, ∑' k', termB P Pm p kind ζ (par2 P Pm p kind) j₁ j₂ k k'
      ≤ ∑ _x ∈ box, ∑ _k ∈ testB (d := P.d) P.L N kind j₁ j₂, ENNReal.ofReal (T * latSum P.d P.L) :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun k _ => hk k
    _ = ENNReal.ofReal (c * (tB * (T * latSum P.d P.L))) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C * (1 / 2) ^ j₁ * (1 / 2) ^ j₂) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hcb : c ≤ (9 * (P.L * ℓ' * ((2 : ℝ) ^ j₁ * P.L))) ^ (3 * P.d + 1) := by
          have hR0 : 0 ≤ P.L * ((leafMax N kind : ℝ) * (2 ^ j₁ * P.L)) := by positivity
          refine card_dagBox_le_real ?_ hR0 ?_
          · have : 1 ≤ P.L * ℓ' := one_le_mul_of_one_le_of_one_le hL hℓ'
            exact one_le_mul_of_one_le_of_one_le this (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hL)
          · have : (leafMax N kind : ℝ) ≤ ℓ' := by linarith
            have h2 : (0 : ℝ) ≤ 2 ^ j₁ * P.L := by positivity
            nlinarith
        have htB := card_testB_le_real P N kind hL j₁ j₂
        have hp := powB_le (d := P.d) (Pm := Pm) j₁ j₂ hL hℓ' hd hPm hc hcb (Nat.cast_nonneg _) htB
        have e : c * (tB * (T * latSum P.d P.L)) = cB P Pm p kind * latSum P.d P.L *
            (c * c ^ ((2 * Pm : ℕ) : ℝ) * tB * ((2 : ℝ) ^ j₁ * P.L) ^ (((2 * Pm : ℕ) : ℝ) - 80 * P.d * Pm) *
              ((2 : ℝ) ^ j₂ * P.L) ^ ((2 - ((2 * Pm : ℕ) : ℝ)) / 100)) := by
          rw [hTdef]; ring
        rw [e, hCdef]
        have hcs : 0 ≤ cB P Pm p kind * latSum P.d P.L := by positivity
        calc cB P Pm p kind * latSum P.d P.L *
              (c * c ^ ((2 * Pm : ℕ) : ℝ) * tB * ((2 : ℝ) ^ j₁ * P.L) ^ (((2 * Pm : ℕ) : ℝ) - 80 * P.d * Pm) *
                ((2 : ℝ) ^ j₂ * P.L) ^ ((2 - ((2 * Pm : ℕ) : ℝ)) / 100))
            ≤ cB P Pm p kind * latSum P.d P.L * ((9 * P.L * ℓ') ^ ((3 * P.d + 1 : ℝ) * (((2 * Pm : ℕ) : ℝ) + 1)) *
                (P.d + 2) * (400 * P.L ^ 2 * ℓ' ^ 2) ^ (P.d * (P.d + 1)) * ((1 / 2) ^ j₁ * (1 / 2) ^ j₂)) :=
              mul_le_mul_of_nonneg_left hp hcs
          _ = cB P Pm p kind * latSum P.d P.L * KB P Pm N kind * (1 / 2) ^ j₁ * (1 / 2) ^ j₂ := by
              unfold KB
              rw [← hℓ'def]
              ring
    _ = ENNReal.ofReal (C * (1 / 2) ^ j₁ * (1 / 2) ^ j₂) := rfl

/-! ## The total -/

theorem KB_nonneg (P : WTParams) (Pm Ntr : ℕ) (kind : FlowerKind) (hL : 1 ≤ P.L) : 0 ≤ KB P Pm Ntr kind := by
  unfold KB
  have : (0 : ℝ) ≤ leafMax Ntr kind := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ (9 * P.L * (leafMax Ntr kind + 1 : ℝ)) ^ ((3 * P.d + 1 : ℝ) * (((2 * Pm : ℕ) : ℝ) + 1)) :=
    Real.rpow_nonneg (by positivity) _
  positivity

theorem probSum_le_tot (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (ζ : ℤˣ)
    (hPm : 100 * ((P.d : ℝ) + 1) ^ 2 ≤ Pm) (hPm1 : 1 ≤ Pm) (hd : 1 ≤ P.d)
    (hΛ : 40 * P.d ≤ P.Lambda (p + 1)) (hL : 1 ≤ P.L) :
    probSum P Pm p kind ζ (par2 P Pm p kind) ≤
      ENNReal.ofReal (2 * (cA P Pm p kind * (3 * P.L) ^ P.d * latSum P.d P.L) +
        4 * (cB P Pm p kind * latSum P.d P.L * KB P Pm (P.N (p + 1)) kind)) := by
  have hcA := cA_nonneg P Pm p kind hL
  have hcB := cB_nonneg P Pm p kind hL
  have hS := (latSum_pos (d := P.d) hL).le
  have hKB := KB_nonneg P Pm (P.N (p + 1)) kind hL
  have hL0 : 0 ≤ P.L := by linarith
  unfold probSum
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (sumA_le P Pm p kind ζ hPm1 hd hΛ hL) (sumB_le P Pm p kind ζ hPm hPm1 hd hΛ hL)

theorem kindGain_div_le (Ntr Pm : ℕ) (kind : FlowerKind) (hPm : 2 ≤ Pm) :
    kindGain Ntr kind / kindBeta Ntr kind ^ ((2 * Pm : ℕ) : ℝ) ≤ Real.exp (-(8 * (Ntr : ℝ))) := by
  have hN : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg _
  have hPm' : (2 : ℝ) ≤ Pm := by exact_mod_cast hPm
  cases kind with
  | X =>
    simp only [kindGain, kindBeta]
    rw [← Real.exp_mul, one_div, ← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    push_cast
    nlinarith
  | Y =>
    simp only [kindGain, kindBeta, Real.one_rpow, div_one]
    exact Real.exp_le_exp.2 (by linarith)
  | W =>
    simp only [kindGain, kindBeta, Real.one_rpow, div_one]
    exact Real.exp_le_exp.2 (by linarith)

/-- The polynomial part of the total. -/
noncomputable def polyTot (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) : ℝ :=
  latSum P.d P.L * (4 * 2 ^ (5 / 4 * (P.Lambda (p + 1) : ℝ) / 2) * latSum P.d P.L) ^ ((2 * Pm : ℕ) : ℝ) *
    P.L ^ (2 * (100 * P.d : ℝ) ^ 3 * Pm) *
    (2 * (2 ^ (((2 * Pm : ℕ) : ℝ) - 1) * 6 * 2 ^ ((2 * Pm : ℕ) : ℝ)) * (3 * P.L) ^ P.d +
      4 * (2 ^ (((2 * Pm : ℕ) : ℝ) - 1) * 3 * (2 ^ ((2 * Pm : ℕ) : ℝ) + 1) * 2 ^ ((2 * Pm : ℕ) : ℝ) *
        (1 - rho) ^ (-((2 * Pm : ℕ) : ℝ))) * KB P Pm (P.N (p + 1)) kind)

theorem tot_eq (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (hL : 1 ≤ P.L) :
    2 * (cA P Pm p kind * (3 * P.L) ^ P.d * latSum P.d P.L) +
        4 * (cB P Pm p kind * latSum P.d P.L * KB P Pm (P.N (p + 1)) kind) =
      kindGain (P.N (p + 1)) kind / kindBeta (P.N (p + 1)) kind ^ ((2 * Pm : ℕ) : ℝ) * polyTot P Pm p kind := by
  have hS := latSum_pos (d := P.d) hL
  have hβ := kindBeta_pos (P.N (p + 1)) kind
  set D := 4 * 2 ^ (5 / 4 * (P.Lambda (p + 1) : ℝ) / 2) * latSum P.d P.L with hDdef
  have hD : 0 < D := by positivity
  have hB : (par2 P Pm p kind).B ^ ((2 * Pm : ℕ) : ℝ) =
      kindBeta (P.N (p + 1)) kind ^ ((2 * Pm : ℕ) : ℝ) / D ^ ((2 * Pm : ℕ) : ℝ) :=
    Real.div_rpow hβ.le hD.le _
  have hβq : 0 < kindBeta (P.N (p + 1)) kind ^ ((2 * Pm : ℕ) : ℝ) := Real.rpow_pos_of_pos hβ _
  have hDq : 0 < D ^ ((2 * Pm : ℕ) : ℝ) := Real.rpow_pos_of_pos hD _
  unfold cA cB polyTot
  rw [hB, ← hDdef]
  field_simp

/-! ## Polynomial bounds -/

/-- `0 ≤ f ≤ c Y^a` with `c ≥ 0`. -/
def PB (Y f c a : ℝ) : Prop := 0 ≤ f ∧ 0 ≤ c ∧ f ≤ c * Y ^ a

theorem PB.mul {Y f₁ f₂ c₁ c₂ a₁ a₂ : ℝ} (hY : 1 ≤ Y) (h₁ : PB Y f₁ c₁ a₁) (h₂ : PB Y f₂ c₂ a₂) :
    PB Y (f₁ * f₂) (c₁ * c₂) (a₁ + a₂) := by
  refine ⟨mul_nonneg h₁.1 h₂.1, mul_nonneg h₁.2.1 h₂.2.1, ?_⟩
  rw [Real.rpow_add (by linarith)]
  calc f₁ * f₂ ≤ (c₁ * Y ^ a₁) * (c₂ * Y ^ a₂) :=
        mul_le_mul h₁.2.2 h₂.2.2 h₂.1 (mul_nonneg h₁.2.1 (Real.rpow_nonneg (by linarith) _))
    _ = c₁ * c₂ * (Y ^ a₁ * Y ^ a₂) := by ring

theorem PB.mono {Y f c a a' : ℝ} (hY : 1 ≤ Y) (h : PB Y f c a) (ha : a ≤ a') : PB Y f c a' :=
  ⟨h.1, h.2.1, h.2.2.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY ha) h.2.1)⟩

theorem PB.add {Y f₁ f₂ c₁ c₂ a : ℝ} (h₁ : PB Y f₁ c₁ a) (h₂ : PB Y f₂ c₂ a) : PB Y (f₁ + f₂) (c₁ + c₂) a :=
  ⟨add_nonneg h₁.1 h₂.1, add_nonneg h₁.2.1 h₂.2.1, by rw [add_mul]; exact add_le_add h₁.2.2 h₂.2.2⟩

theorem PB.rpow {Y f c a q : ℝ} (hY : 1 ≤ Y) (h : PB Y f c a) (hq : 0 ≤ q) : PB Y (f ^ q) (c ^ q) (a * q) := by
  refine ⟨Real.rpow_nonneg h.1 _, Real.rpow_nonneg h.2.1 _, ?_⟩
  calc f ^ q ≤ (c * Y ^ a) ^ q := Real.rpow_le_rpow h.1 h.2.2 hq
    _ = c ^ q * Y ^ (a * q) := by
        rw [Real.mul_rpow h.2.1 (Real.rpow_nonneg (by linarith) _), ← Real.rpow_mul (by linarith)]

theorem PB.le {Y f g c a : ℝ} (h : PB Y g c a) (hf : 0 ≤ f) (hfg : f ≤ g) : PB Y f c a :=
  ⟨hf, h.2.1, hfg.trans h.2.2⟩

theorem PB.smul {Y f c a k : ℝ} (hk : 0 ≤ k) (h : PB Y f c a) : PB Y (k * f) (k * c) a :=
  ⟨mul_nonneg hk h.1, mul_nonneg hk h.2.1, by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h.2.2 hk⟩

theorem PB.base {Y x a : ℝ} (hx : 0 ≤ x) (hxY : x ≤ Y) (ha : 0 ≤ a) : PB Y (x ^ a) 1 a :=
  ⟨Real.rpow_nonneg hx _, zero_le_one, by rw [one_mul]; exact Real.rpow_le_rpow hx hxY ha⟩

theorem PB.npow {Y x c a : ℝ} (hY : 1 ≤ Y) (h : PB Y x c a) (n : ℕ) : PB Y (x ^ n) (c ^ n) (a * n) := by
  have := h.rpow hY (Nat.cast_nonneg n)
  simp only [Real.rpow_natCast] at this
  exact this

/-! ## `polynomial ≤ e^{4N}` -/

theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

/-- **A polynomial in `L` and `N` is at most `e^{4N}`** once `N ≥ (log L)² − 1` and `L` is large. -/
theorem poly_le_exp (K a : ℝ) (hK : 0 < K) (ha : 0 ≤ a) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ N : ℝ, Real.log L ^ 2 - 1 ≤ N →
      ∀ Y : ℝ, 1 ≤ Y → Y ≤ L * (6 * N + 4) → K * Y ^ a ≤ Real.exp (4 * N) := by
  set y₀ := 6 * a + 3 * |Real.log K| + 6 with hy₀
  have hy₀1 : 6 ≤ y₀ := by have := abs_nonneg (Real.log K); linarith
  refine ⟨Real.exp (y₀ + 1), Real.one_le_exp (by linarith), fun L hL N hN Y hY hYL => ?_⟩
  have hL0 : 0 < L := (Real.exp_pos _).trans_le hL
  have hlog : y₀ + 1 ≤ Real.log L := by rw [← Real.exp_le_exp, Real.exp_log hL0]; exact hL
  have hN0 : y₀ ^ 2 ≤ N := by nlinarith
  have hN1 : 0 ≤ N := by nlinarith
  set y := Real.sqrt (6 * N + 4) with hydef
  have hy2 : y ^ 2 = 6 * N + 4 := Real.sq_sqrt (by linarith)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyy₀ : y₀ ≤ y := by
    rw [hydef]
    refine Real.le_sqrt_of_sq_le ?_
    linarith
  have hlogL : Real.log L ≤ y := by
    rw [hydef]
    refine Real.le_sqrt_of_sq_le ?_
    linarith
  have hlog6 : Real.log (6 * N + 4) ≤ 2 * y := log_le_two_sqrt (by linarith)
  have hY0 : 0 < Y := by linarith
  have hlogY : Real.log Y ≤ 3 * y := by
    calc Real.log Y ≤ Real.log (L * (6 * N + 4)) := Real.log_le_log hY0 hYL
      _ = Real.log L + Real.log (6 * N + 4) := Real.log_mul hL0.ne' (by linarith)
      _ ≤ 3 * y := by linarith
  have hKY : K * Y ^ a = Real.exp (Real.log K + a * Real.log Y) := by
    rw [Real.exp_add, Real.exp_log hK, Real.rpow_def_of_pos hY0, mul_comm a]
  rw [hKY]
  refine Real.exp_le_exp.2 ?_
  have h1 : Real.log K ≤ |Real.log K| := le_abs_self _
  have h2 : a * Real.log Y ≤ a * (3 * y) := mul_le_mul_of_nonneg_left hlogY ha
  have h3 : y₀ * y ≤ y * y := mul_le_mul_of_nonneg_right hyy₀ hy0
  have h4 : (1 : ℝ) ≤ y := by linarith
  nlinarith [abs_nonneg (Real.log K)]

/-! ## The final numerics -/

/-- The constant of the polynomial bound. -/
noncomputable def numK (d D Pm : ℕ) : ℝ :=
  2 ^ (d + 1) * latConst d *
    (4 * 2 ^ (5 / 4 * (((40 * d) ^ D : ℕ) : ℝ) / 2) * (2 ^ (d + 1) * latConst d)) ^ ((2 * Pm : ℕ) : ℝ) * 1 *
    (2 * (2 ^ (((2 * Pm : ℕ) : ℝ) - 1) * 6 * 2 ^ ((2 * Pm : ℕ) : ℝ)) * 3 ^ d +
      4 * (2 ^ (((2 * Pm : ℕ) : ℝ) - 1) * 3 * (2 ^ ((2 * Pm : ℕ) : ℝ) + 1) * 2 ^ ((2 * Pm : ℕ) : ℝ) *
        (1 - rho) ^ (-((2 * Pm : ℕ) : ℝ))) *
        (9 ^ ((3 * d + 1 : ℝ) * (((2 * Pm : ℕ) : ℝ) + 1)) * (d + 2) * 400 ^ (d * (d + 1))))

/-- The exponent of the polynomial bound. -/
noncomputable def numA (d Pm : ℕ) : ℝ :=
  ((d : ℝ) + 1) + ((d : ℝ) + 1) * ((2 * Pm : ℕ) : ℝ) + 2 * (100 * d : ℝ) ^ 3 * Pm +
    (1 * (d : ℝ) + ((3 * d + 1 : ℝ) * (((2 * Pm : ℕ) : ℝ) + 1) + 2 * ((d * (d + 1) : ℕ) : ℝ)))

theorem numA_nonneg (d Pm : ℕ) : 0 ≤ numA d Pm := by
  unfold numA
  positivity

theorem numK_pos (d D Pm : ℕ) : 0 ≤ numK d D Pm := by
  have := latConst_nonneg d
  have : 0 < 1 - rho := by have := rho_lt_one; linarith
  unfold numK
  positivity

theorem polyTot_PB (P : WTParams) (Pm p : ℕ) (kind : FlowerKind) (hL : 1 ≤ P.L) (hd : 1 ≤ P.d) (hp : p < P.D) :
    PB (P.L * ((leafMax (P.N (p + 1)) kind : ℝ) + 1)) (polyTot P Pm p kind) (numK P.d P.D Pm) (numA P.d Pm) := by
  set ℓ' : ℝ := (leafMax (P.N (p + 1)) kind : ℝ) + 1 with hℓ'def
  have hℓ' : 1 ≤ ℓ' := by have : (0 : ℝ) ≤ leafMax (P.N (p + 1)) kind := Nat.cast_nonneg _; linarith
  set Y := P.L * ℓ' with hYdef
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le hL hℓ'
  have hL0 : 0 ≤ P.L := by linarith
  have hLY : P.L ≤ Y := le_mul_of_one_le_right hL0 hℓ'
  set q : ℝ := ((2 * Pm : ℕ) : ℝ) with hqdef
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hc := latConst_nonneg P.d
  -- the lattice sum
  have hS : PB Y (latSum P.d P.L) (2 ^ (P.d + 1) * latConst P.d) ((P.d : ℝ) + 1) := by
    refine ⟨(latSum_pos hL).le, by positivity, ?_⟩
    have h1 := latSum_le' (d := P.d) hL
    have h2 : P.L ^ (P.d + 1) ≤ Y ^ ((P.d : ℝ) + 1) := by
      rw [show ((P.d : ℝ) + 1) = ((P.d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      exact pow_le_pow_left₀ hL0 hLY _
    calc latSum P.d P.L ≤ 2 ^ (P.d + 1) * P.L ^ (P.d + 1) * latConst P.d := h1
      _ = 2 ^ (P.d + 1) * latConst P.d * P.L ^ (P.d + 1) := by ring
      _ ≤ 2 ^ (P.d + 1) * latConst P.d * Y ^ ((P.d : ℝ) + 1) := by gcongr
  -- the denominator `4 · 2^{Λ/2} · S`
  have hΛm : (P.Lambda (p + 1) : ℝ) ≤ (((40 * P.d) ^ P.D : ℕ) : ℝ) := by
    exact_mod_cast (Lambda_ge P hp hd).2
  have hDen : PB Y (4 * 2 ^ (5 / 4 * (P.Lambda (p + 1) : ℝ) / 2) * latSum P.d P.L)
      (4 * 2 ^ (5 / 4 * (((40 * P.d) ^ P.D : ℕ) : ℝ) / 2) * (2 ^ (P.d + 1) * latConst P.d)) ((P.d : ℝ) + 1) := by
    have h := hS.smul (k := 4 * 2 ^ (5 / 4 * (((40 * P.d) ^ P.D : ℕ) : ℝ) / 2)) (by positivity)
    refine h.le (mul_nonneg (by positivity) (latSum_pos hL).le) ?_
    have : (2 : ℝ) ^ (5 / 4 * (P.Lambda (p + 1) : ℝ) / 2) ≤ 2 ^ (5 / 4 * (((40 * P.d) ^ P.D : ℕ) : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    have hS0 := (latSum_pos (d := P.d) hL).le
    nlinarith
  have hDq := hDen.rpow hY hq0
  -- `L^{2(100d)³P}`
  have hE : PB Y (P.L ^ (2 * (100 * P.d : ℝ) ^ 3 * Pm)) 1 (2 * (100 * P.d : ℝ) ^ 3 * Pm) :=
    PB.base hL0 hLY (by positivity)
  -- `(3L)^d`
  have h3 : PB Y (3 * P.L) 3 1 := ⟨by positivity, by norm_num, by rw [Real.rpow_one]; linarith⟩
  have h3L := h3.npow hY P.d
  -- `K_B`
  set r : ℝ := (3 * P.d + 1 : ℝ) * (q + 1) with hrdef
  set n : ℕ := P.d * (P.d + 1) with hndef
  have hKB : PB Y (KB P Pm (P.N (p + 1)) kind) (9 ^ r * (P.d + 2) * 400 ^ n) (r + 2 * (n : ℝ)) := by
    refine ⟨KB_nonneg P Pm _ kind hL, by positivity, le_of_eq ?_⟩
    unfold KB
    rw [← hℓ'def, ← hqdef, ← hrdef, show 9 * P.L * ℓ' = 9 * Y by rw [hYdef]; ring,
      show 400 * P.L ^ 2 * ℓ' ^ 2 = 400 * Y ^ 2 by rw [hYdef]; ring,
      Real.mul_rpow (by norm_num) (by linarith), mul_pow, ← pow_mul,
      Real.rpow_add (by linarith), ← Real.rpow_natCast Y (2 * n)]
    push_cast
    ring
  -- the bracket
  set c₁ : ℝ := 2 * (2 ^ (q - 1) * 6 * 2 ^ q)
  set c₂ : ℝ := 4 * (2 ^ (q - 1) * 3 * (2 ^ q + 1) * 2 ^ q * (1 - rho) ^ (-q))
  have hρ : 0 < 1 - rho := by have := rho_lt_one; linarith
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hIn : PB Y (c₁ * (3 * P.L) ^ P.d + c₂ * KB P Pm (P.N (p + 1)) kind)
      (c₁ * 3 ^ P.d + c₂ * (9 ^ r * (P.d + 2) * 400 ^ n)) (1 * (P.d : ℝ) + (r + 2 * (n : ℝ))) := by
    refine PB.add ((h3L.smul hc₁).mono hY ?_) ((hKB.smul hc₂).mono hY ?_)
    · have : 0 ≤ r + 2 * (n : ℝ) := by positivity
      linarith
    · have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
      linarith
  have hall := ((hS.mul hY hDq).mul hY hE).mul hY hIn
  unfold polyTot numK numA
  rw [← hqdef]
  convert hall using 2

/-- `N_q ≥ (log L)² − 1` once `log L ≥ 1`. -/
theorem N_ge_log_sq (P : WTParams) (hd : 1 ≤ P.d) (hx : 1 ≤ Real.log P.L) (q : ℕ) :
    Real.log P.L ^ 2 - 1 ≤ P.N q := by
  have h1 : 1 ≤ P.Rdown 0 := WTParams.one_le_Rdown_zero P hx
  have hN : (P.Rdown 0 : ℝ) ≤ P.N q := by exact_mod_cast WTParams.Rdown_zero_le_N P hd h1 q
  have hfloor : Real.log P.L ^ (40 * P.d) - 1 ≤ (P.Rdown 0 : ℝ) := by
    show Real.log P.L ^ (40 * P.d) - 1 ≤ ((⌊Real.log P.L ^ (40 * P.d)⌋₊ : ℕ) : ℝ)
    have := Nat.lt_floor_add_one (Real.log P.L ^ (40 * P.d))
    linarith
  have hpow : Real.log P.L ^ 2 ≤ Real.log P.L ^ (40 * P.d) := pow_le_pow_right₀ hx (by omega)
  linarith

/-- **The final numerics**: for `L ≥ L₀(d, 𝔇, Pm)`, the total is at most `e^{−4N}/12`. -/
theorem exists_L0_part2 (d D Pm : ℕ) (hd : 1 ≤ d) (hPm : 100 * ((d : ℝ) + 1) ^ 2 ≤ Pm) :
    ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ P : WTParams, P.d = d → P.D = D → L₀ ≤ P.L → ∀ p, p < P.D →
      ∀ kind : FlowerKind,
        2 * (cA P Pm p kind * (3 * P.L) ^ P.d * latSum P.d P.L) +
            4 * (cB P Pm p kind * latSum P.d P.L * KB P Pm (P.N (p + 1)) kind) ≤
          Real.exp (-(4 * P.N (p + 1) : ℝ)) / 12 := by
  obtain ⟨L₁, hL₁, H⟩ := poly_le_exp (12 * numK d D Pm + 1) (numA d Pm)
    (by have := numK_pos d D Pm; linarith) (numA_nonneg d Pm)
  refine ⟨max L₁ (Real.exp 1), le_max_right _ _, fun P hPd hPD hL p hp kind => ?_⟩
  have hL1 : 1 ≤ P.L := le_trans (Real.one_le_exp zero_le_one) ((le_max_right _ _).trans hL)
  have hx : 1 ≤ Real.log P.L := by
    rw [← Real.exp_le_exp, Real.exp_log (by linarith)]
    exact (le_max_right _ _).trans hL
  have hdP : 1 ≤ P.d := hPd ▸ hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hPm1 : 2 ≤ Pm := by
    have h4 : (4 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith
    have : (2 : ℝ) ≤ Pm := by linarith
    exact_mod_cast this
  set N := P.N (p + 1)
  have hN := N_ge_log_sq P hdP hx (p + 1)
  have hPB := polyTot_PB P Pm p kind hL1 hdP hp
  rw [hPd, hPD] at hPB
  set ℓ' : ℝ := (leafMax N kind : ℝ) + 1 with hℓ'def
  have hℓ' : 1 ≤ ℓ' := by have : (0 : ℝ) ≤ leafMax N kind := Nat.cast_nonneg _; linarith
  have hℓN : ℓ' ≤ 6 * (N : ℝ) + 4 := by
    have := leafMax_le N kind
    have : (leafMax N kind : ℝ) ≤ 6 * (N : ℝ) + 3 := by exact_mod_cast this
    linarith
  have hY1 : 1 ≤ P.L * ℓ' := one_le_mul_of_one_le_of_one_le hL1 hℓ'
  have hYL : P.L * ℓ' ≤ P.L * (6 * (N : ℝ) + 4) := mul_le_mul_of_nonneg_left hℓN (by linarith)
  have hexp := H P.L ((le_max_left _ _).trans hL) N hN (P.L * ℓ') hY1 hYL
  have hpoly : polyTot P Pm p kind ≤ Real.exp (4 * (N : ℝ)) / 12 := by
    have h1 := hPB.2.2
    have h2 : numK d D Pm * (P.L * ℓ') ^ numA d Pm ≤ Real.exp (4 * (N : ℝ)) / 12 := by
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ P.L * ℓ' by linarith) (numA d Pm)
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    exact h1.trans h2
  have hkd := kindGain_div_le N Pm kind hPm1
  have hk0 : 0 ≤ kindGain N kind / kindBeta N kind ^ ((2 * Pm : ℕ) : ℝ) :=
    div_nonneg (kindGain_pos N kind).le (Real.rpow_nonneg (kindBeta_pos N kind).le _)
  rw [tot_eq P Pm p kind hL1]
  calc kindGain N kind / kindBeta N kind ^ ((2 * Pm : ℕ) : ℝ) * polyTot P Pm p kind
      ≤ Real.exp (-(8 * (N : ℝ))) * (Real.exp (4 * (N : ℝ)) / 12) :=
        mul_le_mul hkd hpoly hPB.1 (Real.exp_pos _).le
    _ = Real.exp (-(4 * (N : ℝ))) / 12 := by
        rw [mul_div_assoc', ← Real.exp_add]
        ring_nf

end WaveTurbulence.Fixedpt
