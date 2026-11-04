/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.CountLemmas.A23HalfBig
public import WaveTurbulence.Foundations.CountLemmas.PolynomialGrowth
public import WaveTurbulence.Foundations.CountLemmas.PowerAbsorption

/-!
# DH23 Lemma A.2(3), `γ > 1/2`: the anti-parallel selector `ζ = x − v`

With `τ = δ⁻¹L^{-2γ}`, `ρ = δ⁻¹L^{2−2γ}`, `k₀ = ⌈L^{d−1−κ}⌉`, `κ = kappaHalf γ = min((2γ−1)/3, 1−γ)`, every term of
`sum_star_le` except the sparse one is `O(L^{T − gap/2})`, `T = 3(d−γ) − (1−γ) − κ`
(`gap = min(1−γ, (2γ−1)/3)`), and the sparse term is `≤ 4C δ⁻¹ L^T`.
**`coupledTriple_star_bound_half`**: `#S ≤ C δ^{-2} (1 + log L)² L^T`, `C` independent of `δ`.
-/

public section

open Filter Set Asymptotics

namespace WaveTurbulence.CountLemmas

/-- **The saving** `κ(γ) = min((2γ − 1)/3, 1 − γ)` of the `γ > 1/2` branch (referee §4.3). -/
@[expose] noncomputable def kappaHalf (γ : ℝ) : ℝ := min ((2 * γ - 1) / 3) (1 - γ)

theorem kappaHalf_pos {γ : ℝ} (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) : 0 < kappaHalf γ :=
  lt_min (by linarith [hγ.1]) (by linarith [hγ.2])

theorem kappaHalf_le_third (γ : ℝ) : kappaHalf γ ≤ (2 * γ - 1) / 3 := min_le_left _ _

theorem kappaHalf_le_one_sub (γ : ℝ) : kappaHalf γ ≤ 1 - γ := min_le_right _ _

theorem growth_two_mul_add_one : (fun L : ℝ => 2 * L + 1) =O[atTop] (fun L : ℝ => L ^ (1 : ℝ)) := by
  apply IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  rw [Real.norm_of_nonneg (by linarith), Real.rpow_one, Real.norm_of_nonneg (by linarith)]
  linarith

theorem growth_of_le {f g : ℝ → ℝ} {a : ℝ} (hg : g =O[atTop] fun L => L ^ a)
    (h : ∀ᶠ L in atTop, 0 ≤ f L ∧ f L ≤ g L) : f =O[atTop] fun L => L ^ a := by
  refine IsBigO.trans ?_ hg
  apply IsBigO.of_bound 1
  filter_upwards [h] with L hL
  rw [Real.norm_of_nonneg hL.1, one_mul]
  exact hL.2.trans (le_abs_self _) |>.trans_eq (Real.norm_eq_abs _).symm

/-- `(2⌈ρ⌉+1)`, `⌈ρ⌉ ≤ 2ρ` for `ρ ≥ 1`. -/
theorem nat_ceil_le_two_mul {ρ : ℝ} (hρ : 1 ≤ ρ) : (⌈ρ⌉₊ : ℝ) ≤ 2 * ρ := by
  have := Nat.ceil_lt_add_one (show 0 ≤ ρ by linarith)
  linarith

/-- **DH23 Lemma A.2(3), `γ > 1/2`, selector `ζ = x − v`** (`d = n + 3`): saving `κ(γ)` up to `(1 + log L)²`. -/
theorem coupledTriple_star_bound_half (n : ℕ) (γ : ℝ) (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀,
      ∀ (a b c : Mom (n + 3)) (nv : Fin (n + 3) → ℤ) (α β : ℝ),
        ((coupledTripleSet L a b c (latticePoint L nv) α β (δ⁻¹ * L ^ (-2 * γ)) 0).ncard : ℝ) ≤
          C * δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 *
            L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ) := by
  obtain ⟨Cs, hCs, hstar⟩ := sum_star_le n
  refine ⟨4 * Cs + 9, by positivity, fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ.2
  set κ := kappaHalf γ with hκdef
  set D : ℝ := ((n + 3 : ℕ) : ℝ) with hD
  have hD3 : 3 ≤ D := by simp [hD]
  set T := 3 * (D - γ) - (1 - γ) - κ with hT
  have hκ0 : 0 < κ := kappaHalf_pos hγ
  have hκ1 : κ ≤ (2 * γ - 1) / 3 := kappaHalf_le_third γ
  have hκ2 : κ ≤ 1 - γ := kappaHalf_le_one_sub γ
  set gap := min (1 - γ) ((2 * γ - 1) / 3) with hgap
  have hgap0 : 0 < gap := lt_min (by linarith [hγ.2]) (by linarith [hγ.1])
  have hgap1 : gap ≤ 1 - γ := min_le_left _ _
  have hgap2 : gap ≤ (2 * γ - 1) / 3 := min_le_right _ _
  set μ := gap / 2 with hμ
  set T' := T - gap / 2 with hT'
  set K := estcrossConst n
  have hK := estcrossConst_nonneg n
  -- the parameters as functions of `L`
  set τf : ℝ → ℝ := fun L => δ⁻¹ * L ^ (-2 * γ)
  set ρf : ℝ → ℝ := fun L => τf L * L ^ 2
  set wf : ℝ → ℝ := fun L => L ^ (D - 1 - κ)
  set kf : ℝ → ℕ := fun L => ⌈wf L⌉₊
  set lgf : ℝ → ℝ := fun L => (1 + Real.log L) ^ 2
  set Mf : ℝ → ℝ := fun L => 3 * (2 * L + 1) ^ (n + 2)
  have hρf : ∀ L, 0 < L → ρf L = δ⁻¹ * L ^ (2 - 2 * γ) := fun L hL => by
    simp only [ρf, τf]
    rw [mul_assoc, ← Real.rpow_natCast L 2, ← Real.rpow_add hL]
    congr 2
    push_cast
    ring
  have hρ1 : ∀ L, 1 ≤ L → 1 ≤ ρf L := fun L hL => by
    rw [hρf L (by linarith)]
    have : 1 ≤ L ^ (2 - 2 * γ) := Real.one_le_rpow hL (by linarith [hγ.2])
    nlinarith
  have hw1 : ∀ L, 1 ≤ L → 1 ≤ wf L := fun L hL => Real.one_le_rpow hL (by linarith)
  -- big-O building blocks
  have Oρ : ρf =O[atTop] fun L => L ^ (2 - 2 * γ) :=
    growth_of_le ((growth_rpow (2 - 2 * γ)).const_mul_left δ⁻¹) (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      exact ⟨by rw [hρf L hL]; positivity, le_of_eq (hρf L hL)⟩)
  have Oceil : (fun L => (⌈ρf L⌉₊ : ℝ)) =O[atTop] fun L => L ^ (2 - 2 * γ) :=
    growth_of_le (Oρ.const_mul_left 2) (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
      exact ⟨by positivity, nat_ceil_le_two_mul (hρ1 L hL)⟩)
  have Ok : (fun L => (kf L : ℝ)) =O[atTop] fun L => L ^ (D - 1 - κ) :=
    growth_of_le ((growth_rpow (D - 1 - κ)).const_mul_left 2) (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
      exact ⟨by positivity, nat_ceil_le_two_mul (hw1 L hL)⟩)
  have Okinv : (fun L => ((kf L : ℝ))⁻¹) =O[atTop] fun L => L ^ (-(D - 1 - κ)) :=
    growth_of_le (growth_rpow _) (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
      refine ⟨by positivity, ?_⟩
      rw [Real.rpow_neg (by linarith)]
      exact inv_anti₀ (by linarith [hw1 L hL]) (Nat.le_ceil _))
  have Oθ : (fun L => max 1 (L ^ (n + 2) / (kf L : ℝ))) =O[atTop] fun L => L ^ κ :=
    growth_of_le (growth_rpow κ) (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
      have hLp : 0 < L := by linarith
      refine ⟨le_trans zero_le_one (le_max_left _ _), max_le (Real.one_le_rpow hL hκ0.le) ?_⟩
      have hk : wf L ≤ (kf L : ℝ) := Nat.le_ceil _
      calc L ^ (n + 2) / (kf L : ℝ) ≤ L ^ (n + 2) / wf L :=
            div_le_div_of_nonneg_left (by positivity) (by linarith [hw1 L hL]) hk
        _ = L ^ κ := by
            simp only [wf]
            rw [← Real.rpow_natCast, ← Real.rpow_sub hLp]
            congr 1
            simp only [hD]
            push_cast
            ring)
  have OM : Mf =O[atTop] fun L => L ^ ((n + 2 : ℕ) : ℝ) := by
    have := (growth_pow growth_two_mul_add_one (n + 2)).const_mul_left 3
    simpa only [one_mul] using this
  have OMfl : (fun L => (⌊Mf L⌋₊ : ℝ)) =O[atTop] fun L => L ^ ((n + 2 : ℕ) : ℝ) :=
    growth_of_le OM (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
      exact ⟨by positivity, Nat.floor_le (by simp only [Mf]; positivity)⟩)
  have Olg : lgf =O[atTop] fun L => L ^ μ := growth_log_sq (by positivity)
  have O2L : ∀ k : ℕ, (fun L : ℝ => (2 * L + 1) ^ k) =O[atTop] fun L => L ^ ((k : ℕ) : ℝ) := fun k => by
    simpa only [one_mul] using growth_pow growth_two_mul_add_one k
  have ONat : ∀ k : ℕ, (fun L : ℝ => L ^ k) =O[atTop] fun L => L ^ ((k : ℕ) : ℝ) := growth_natpow
  have Oc : ∀ c : ℝ, (fun _ : ℝ => c) =O[atTop] fun L : ℝ => L ^ (0 : ℝ) := growth_const
  -- the non-sparse part `G`
  set G : ℝ → ℝ := fun L => 2 * (2 * L + 1) ^ (2 * (n + 3)) + (2 * L + 1) ^ (2 * (n + 3) - 2) *
      (20 * (2 * ⌈ρf L⌉₊ + 1) ^ (n + 3) +
        16 * (n + 3) * 3 ^ (n + 2) * (ρf L) ^ 2 * (⌈ρf L⌉₊ : ℝ) ^ (n + 1)) +
      Mf L * denseBound n L (ρf L) (kf L) ⌊Mf L⌋₊
  have hu : 0 ≤ 2 - 2 * γ := by linarith [hγ.2]
  have OG : G =O[atTop] fun L => L ^ T' := by
    -- the first two pieces
    have O1 : (fun L : ℝ => 2 * (2 * L + 1) ^ (2 * (n + 3))) =O[atTop] fun L => L ^ T' := by
      refine ((O2L _).const_mul_left 2).trans (growth_mono ?_)
      simp only [hT', hT, hD]; push_cast; nlinarith [hγ.2]
    have Oceil1 : (fun L => 2 * (⌈ρf L⌉₊ : ℝ) + 1) =O[atTop] fun L => L ^ (2 - 2 * γ) :=
      growth_add (Oceil.const_mul_left 2) (Oc 1) le_rfl hu
    have O2a : (fun L => 20 * (2 * (⌈ρf L⌉₊ : ℝ) + 1) ^ (n + 3)) =O[atTop]
        fun L => L ^ ((2 - 2 * γ) * ((n + 3 : ℕ) : ℝ)) := (growth_pow Oceil1 (n + 3)).const_mul_left 20
    have O2b : (fun L => 16 * (n + 3) * 3 ^ (n + 2) * (ρf L) ^ 2 * (⌈ρf L⌉₊ : ℝ) ^ (n + 1)) =O[atTop]
        fun L => L ^ ((2 - 2 * γ) * ((n + 3 : ℕ) : ℝ)) := by
      have h := growth_mul ((growth_pow Oρ 2).const_mul_left (16 * (n + 3) * 3 ^ (n + 2) : ℝ))
        (growth_pow Oceil (n + 1)) (c := (2 - 2 * γ) * ((n + 3 : ℕ) : ℝ)) (by push_cast; ring_nf; exact le_rfl)
      refine h.congr' (Eventually.of_forall fun L => ?_) EventuallyEq.rfl
      ring
    have O2 : (fun L : ℝ => (2 * L + 1) ^ (2 * (n + 3) - 2) *
        (20 * (2 * ⌈ρf L⌉₊ + 1) ^ (n + 3) +
          16 * (n + 3) * 3 ^ (n + 2) * (ρf L) ^ 2 * (⌈ρf L⌉₊ : ℝ) ^ (n + 1))) =O[atTop] fun L => L ^ T' := by
      refine growth_mul (O2L _) (growth_add O2a O2b le_rfl le_rfl) ?_
      simp only [hT', hT, hD]
      rw [show 2 * (n + 3) - 2 = 2 * n + 4 by omega]
      push_cast
      nlinarith [hgap2, hκ1, hγ.1]
    -- the dense part: exponents
    set c₅ := T' - (D - 1) with hc₅
    have hD1 : ((n + 2 : ℕ) : ℝ) = D - 1 := by simp only [hD]; push_cast; ring
    have hD2 : ((n + 1 : ℕ) : ℝ) = D - 2 := by simp only [hD]; push_cast; ring
    have hε : 0 ≤ (D - 3) * (2 * γ - 1) := mul_nonneg (by linarith) (by linarith [hγ.1])
    have Oθ2 := growth_pow Oθ 2
    have Oρ2 := growth_pow Oρ 2
    have Oρd := growth_pow Oρ (n + 3)
    have OL1 := ONat (n + 1)
    -- term 1: `k₀ K (ρ^{n+3} + L^{n+1} ρ² θ² lg)`
    have Ot1 : (fun L => (kf L : ℝ) * (K * ((ρf L) ^ (n + 3) + L ^ (n + 1) * (ρf L) ^ 2 *
        max 1 (L ^ (n + 2) / (kf L : ℝ)) ^ 2 * lgf L))) =O[atTop] fun L => L ^ c₅ := by
      have hin : (fun L => (ρf L) ^ (n + 3) + L ^ (n + 1) * (ρf L) ^ 2 *
          max 1 (L ^ (n + 2) / (kf L : ℝ)) ^ 2 * lgf L) =O[atTop] fun L => L ^ (c₅ - (D - 1 - κ)) := by
        have hg := growth_mul (growth_mul (growth_mul OL1 Oρ2 le_rfl) Oθ2 le_rfl) Olg le_rfl
        refine growth_add Oρd hg ?_ ?_
        · simp only [hc₅, hT', hT, hD] at *; push_cast at *; nlinarith [hε, hgap2]
        · rw [hD2]; simp only [hc₅, hT', hT, hμ]; linarith [hκ1, hgap2]
      refine growth_mul Ok (hin.const_mul_left K) (by linarith)
    -- term 2: `M K (ρ^{n+3} + L^{n+1} ρ² lg)`
    have Ot2 : (fun L => (⌊Mf L⌋₊ : ℝ) * (K * ((ρf L) ^ (n + 3) + L ^ (n + 1) * (ρf L) ^ 2 * lgf L))) =O[atTop]
        fun L => L ^ c₅ := by
      have hin : (fun L => (ρf L) ^ (n + 3) + L ^ (n + 1) * (ρf L) ^ 2 * lgf L) =O[atTop]
          fun L => L ^ (c₅ - (D - 1)) := by
        refine growth_add Oρd (growth_mul (growth_mul OL1 Oρ2 le_rfl) Olg le_rfl) ?_ ?_
        · simp only [hc₅, hT', hT, hD] at *; push_cast at *; nlinarith [hε, hgap2, hκ1]
        · rw [hD2]; simp only [hc₅, hT', hT, hμ]; linarith [hκ1, hgap2]
      refine growth_mul OMfl (hin.const_mul_left K) (by rw [hD1]; linarith)
    -- term 3: `K L^{n+1} ρ² lg (L^{n+2})² k₀⁻¹`
    have Ot3 : (fun L => K * L ^ (n + 1) * (ρf L) ^ 2 * lgf L * (L ^ (n + 2)) ^ 2 * ((kf L : ℝ))⁻¹) =O[atTop]
        fun L => L ^ c₅ := by
      have g1 := growth_mul (OL1.const_mul_left K) Oρ2 le_rfl
      have g2 := growth_mul g1 Olg le_rfl
      have g3 := growth_mul g2 (growth_pow (ONat (n + 2)) 2) le_rfl
      have h := growth_mul g3 Okinv (c := c₅) (by
          rw [hD2, hD1]; simp only [hc₅, hT', hT, hμ]; push_cast; linarith [hκ1, hgap2])
      refine h.congr' (Eventually.of_forall fun L => ?_) EventuallyEq.rfl
      simp only
    have Odense : (fun L => denseBound n L (ρf L) (kf L) ⌊Mf L⌋₊) =O[atTop] fun L => L ^ c₅ := by
      have h := growth_add (growth_add Ot1 Ot2 le_rfl le_rfl) Ot3 le_rfl le_rfl
      refine h.congr' (Eventually.of_forall fun L => ?_) EventuallyEq.rfl
      simp only [denseBound]
      ring
    have O3 : (fun L => Mf L * denseBound n L (ρf L) (kf L) ⌊Mf L⌋₊) =O[atTop] fun L => L ^ T' :=
      growth_mul OM Odense (by rw [hD1]; simp only [hc₅]; linarith)
    have h := growth_add (growth_add O1 O2 le_rfl le_rfl) O3 le_rfl le_rfl
    refine h.congr' (Eventually.of_forall fun L => ?_) EventuallyEq.rfl
    simp only [G]
  -- the critical sparse term
  have hθle : ∀ L, 1 ≤ L → max 1 (L ^ (n + 2) / (kf L : ℝ)) ≤ L ^ κ := fun L hL => by
    have hLp : 0 < L := by linarith
    refine max_le (Real.one_le_rpow hL hκ0.le) ?_
    have hk : wf L ≤ (kf L : ℝ) := Nat.le_ceil _
    calc L ^ (n + 2) / (kf L : ℝ) ≤ L ^ (n + 2) / wf L :=
          div_le_div_of_nonneg_left (by positivity) (by linarith [hw1 L hL]) hk
      _ = L ^ κ := by
          simp only [wf]
          rw [← Real.rpow_natCast, ← Real.rpow_sub hLp]
          congr 1
          simp only [hD]
          push_cast
          ring
  have hsparse : ∀ L, 1 ≤ L → 2 * (kf L : ℝ) * Cs * τf L * L ^ (2 * D) ≤ 4 * Cs * δ⁻¹ * L ^ T := fun L hL => by
    have hLp : 0 < L := by linarith
    have hk : (kf L : ℝ) ≤ 2 * wf L := nat_ceil_le_two_mul (hw1 L hL)
    have hpow : wf L * L ^ (-2 * γ) * L ^ (2 * D) = L ^ T := by
      simp only [wf]
      rw [← Real.rpow_add hLp, ← Real.rpow_add hLp]
      congr 1
      simp only [hT]
      ring
    calc 2 * (kf L : ℝ) * Cs * τf L * L ^ (2 * D) ≤ 2 * (2 * wf L) * Cs * τf L * L ^ (2 * D) := by
          gcongr
      _ = 4 * Cs * δ⁻¹ * (wf L * L ^ (-2 * γ) * L ^ (2 * D)) := by simp only [τf]; ring
      _ = _ := by rw [hpow]
  -- eventual facts
  obtain ⟨c, hc0, hcG⟩ := OG.exists_nonneg
  have ev1 := hcG.bound
  have ev2 := eventually_monomial_log_le (a := T') (b := T) (by simp only [hT']; linarith) hc0 0
  have ev3 := eventually_monomial_log_le (a := 2 - 2 * γ) (b := 1) (by linarith [hγ.1])
    (show (0 : ℝ) ≤ δ⁻¹ by positivity) 0
  have ev4 := eventually_monomial_log_le (a := κ) (b := 2 - 2 * γ) (by linarith [hκ2, hγ.2])
    (show (0 : ℝ) ≤ 16 * 3 ^ (n + 1) by positivity) 0
  obtain ⟨L₀, hL₀⟩ := (((ev1.and ev2).and ev3).and (ev4.and (eventually_ge_atTop (2 : ℝ)))).exists_forall_of_atTop
  refine ⟨L₀, fun L hL a b c' nv α β => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4, hL2⟩ := hL₀ L hL
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  simp only [pow_zero, mul_one, Real.rpow_one] at h2 h3 h4
  have hρ := hρf L hLp
  have hτ : 0 < τf L := by simp only [τf]; positivity
  have hwin : 1 / τf L ≤ L ^ 2 := by
    rw [div_le_iff₀ hτ]
    have := hρ1 L hL1
    simp only [ρf] at this
    linarith
  have hρL : τf L * L ^ 2 ≤ L := by
    change ρf L ≤ L
    rw [hρ]; exact h3
  have hscale : 16 * ((3 : ℝ) ^ (n + 1) * max 1 (L ^ (n + 2) / (kf L : ℝ))) ≤ τf L * L ^ 2 := by
    change _ ≤ ρf L
    rw [hρ]
    have := hθle L hL1
    have hu1 : L ^ (2 - 2 * γ) ≤ δ⁻¹ * L ^ (2 - 2 * γ) := by
      have : 0 ≤ L ^ (2 - 2 * γ) := by positivity
      nlinarith
    calc 16 * ((3 : ℝ) ^ (n + 1) * max 1 (L ^ (n + 2) / (kf L : ℝ))) ≤ 16 * 3 ^ (n + 1) * L ^ κ := by
          rw [← mul_assoc]; gcongr
      _ ≤ L ^ (2 - 2 * γ) := h4
      _ ≤ _ := hu1
  have hk1 : 1 ≤ kf L := Nat.one_le_iff_ne_zero.mpr (by
    simp only [kf]; exact (Nat.ceil_pos.mpr (lt_of_lt_of_le one_pos (hw1 L hL1))).ne')
  have hb := hstar L (τf L) (kf L) hL2 hτ hwin (hρ1 L hL1) hρL hk1 hscale a b c' nv α β
  have hG : ‖G L‖ ≤ c * ‖L ^ T'‖ := h1
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ L ^ T')] at hG
  have hGle : G L ≤ L ^ T := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hG) |>.trans h2
  have hsp := hsparse L hL1
  have hbound : ((coupledTripleSet L a b c' (latticePoint L nv) α β (τf L) 0).ncard : ℝ) ≤
      L ^ T + 4 * Cs * δ⁻¹ * L ^ T := by
    refine hb.trans ?_
    have hD' : ((n + 3 : ℕ) : ℝ) = D := rfl
    have heq : 2 * (2 * L + 1) ^ (2 * (n + 3)) + (2 * L + 1) ^ (2 * (n + 3) - 2) *
        (20 * (2 * ⌈τf L * L ^ 2⌉₊ + 1) ^ (n + 3) +
          16 * (n + 3) * 3 ^ (n + 2) * (τf L * L ^ 2) ^ 2 * (⌈τf L * L ^ 2⌉₊ : ℝ) ^ (n + 1)) +
        (2 * (kf L) * Cs * τf L * L ^ (2 * ((n + 3 : ℕ) : ℝ)) +
          3 * (2 * L + 1) ^ (n + 2) * denseBound n L (τf L * L ^ 2) (kf L) ⌊3 * (2 * L + 1) ^ (n + 2)⌋₊) =
        G L + 2 * (kf L : ℝ) * Cs * τf L * L ^ (2 * D) := by
      simp only [G, ρf, Mf, hD']
      abel
    rw [heq]
    exact add_le_add hGle hsp
  have hlg : 1 ≤ (1 + Real.log L) ^ 2 :=
    one_le_pow₀ (by linarith only [Real.log_nonneg hL1])
  have hδ2 : δ⁻¹ ≤ δ⁻¹ ^ 2 := le_self_pow₀ hδi (by norm_num)
  have hLT : 0 ≤ L ^ T := by positivity
  calc ((coupledTripleSet L a b c' (latticePoint L nv) α β (δ⁻¹ * L ^ (-2 * γ)) 0).ncard : ℝ)
      ≤ L ^ T + 4 * Cs * δ⁻¹ * L ^ T := hbound
    _ ≤ (4 * Cs + 9) * δ⁻¹ ^ 2 * 1 * L ^ T := by
        have h1 : 1 ≤ δ⁻¹ ^ 2 := one_le_pow₀ hδi
        have e1 : L ^ T ≤ δ⁻¹ ^ 2 * L ^ T := le_mul_of_one_le_left hLT h1
        have e2 : 4 * Cs * δ⁻¹ * L ^ T ≤ 4 * Cs * δ⁻¹ ^ 2 * L ^ T :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ2 (by positivity)) hLT
        have e3 : 0 ≤ δ⁻¹ ^ 2 * L ^ T := by positivity
        linarith only [e1, e2, e3]
    _ ≤ (4 * Cs + 9) * δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 * L ^ T := by gcongr

end WaveTurbulence.CountLemmas
