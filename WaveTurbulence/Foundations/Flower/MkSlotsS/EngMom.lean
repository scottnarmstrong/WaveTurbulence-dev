/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngDom

/-! # B3s-HELPER4 (δ) S1 (3): the selection moments are paid by the adjacent slots

The frequency of a pinned assembled mode at a branch `v` that is not a unit clock is the sum of the non-routed slot
frequencies at the clock `v` (main `AsmCtxH.freqH`, `modeFreq`, `frqR`). Since `1 + |Σ a| ≤ ∏ (1 + |a|)`, the selection
moment `momS sel freq = ∏_{v ∈ sel} (1 + |freq v|)^{1/18}` is at most `∏_{s,i} (1 + |m_s(i)|)^{selE s i}` with
`selE s i = 1/18` iff the clock `i` of the slot `s` is (non-routed and) a selected branch (`momS_routed_le`).
A slot then pays its two clock losses `(1+|m_i|)^c` and its moments with its time weight `⟨m/2⟩^{θ_s}` as soon as
`θ_s ≥ 2c + Σ_i selE s i`, at the constant `3^{2c + Σ selE} ≤ 9·selF s` (`selF s = 3` at a slot adjacent to a
selected branch, `1` elsewhere): `slot_moment_le`, `modes_mass_sel_le` (U1's `ModesMomentSel` with two moments per
slot and per-slot constants). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg.Skeleton
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsS

variable {w : ℕ}

/-! ## Selected clocks of slots -/

section Sel

variable {G : Garden w} {J : Type} (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
  (sel : Finset (GBranch G.tree))

open scoped Classical in
/-- The moment exponent of the clock `i` of the slot `s`: `1/18` if the clock is a non-routed selected branch. -/
def selE (s : ReplacementSlot G) (i : Fin 2) : ℝ :=
  if ∃ v ∈ sel, route s i = Sum.inl (Sum.inr v) then 1 / 18 else 0

/-- A slot with a non-routed selected clock. -/
def AdjS (s : ReplacementSlot G) : Prop := ∃ i, ∃ v ∈ sel, route s i = Sum.inl (Sum.inr v)

open scoped Classical in
/-- The extra constant of a slot adjacent to a selected branch (`27 = 9·3` instead of `9`). -/
def selF (s : ReplacementSlot G) : ℝ := if AdjS route sel s then 3 else 1

theorem selE_nonneg (s : ReplacementSlot G) (i : Fin 2) : 0 ≤ selE route sel s i := by
  unfold selE; split_ifs <;> norm_num

theorem selE_le (s : ReplacementSlot G) (i : Fin 2) : selE route sel s i ≤ 1 / 18 := by
  unfold selE; split_ifs <;> norm_num

theorem one_le_selF (s : ReplacementSlot G) : 1 ≤ selF route sel s := by
  unfold selF; split_ifs <;> norm_num

theorem selF_nonneg (s : ReplacementSlot G) : 0 ≤ selF route sel s := zero_le_one.trans (one_le_selF route sel s)

theorem selE_eq_zero_of_not_adj (s : ReplacementSlot G) (h : ¬ AdjS route sel s) (i : Fin 2) :
    selE route sel s i = 0 := by
  unfold selE
  rw [if_neg]
  exact fun hv => h ⟨i, hv⟩

@[simp] theorem selE_empty (s : ReplacementSlot G) (i : Fin 2) : selE route ∅ s i = 0 := by simp [selE]

@[simp] theorem selF_empty (s : ReplacementSlot G) : selF route ∅ s = 1 := by simp [selF, AdjS]

/-- The per-slot constant dominates `3^{2c + Σ_i selE s i}` for `c ≤ 1`. -/
theorem three_rpow_le_selF (s : ReplacementSlot G) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (3 : ℝ) ^ (2 * c + (selE route sel s 0 + selE route sel s 1)) ≤ 9 * selF route sel s := by
  classical
  have h3 : ∀ x : ℝ, x ≤ 3 → (3 : ℝ) ^ x ≤ 27 := fun x hx => by
    calc (3 : ℝ) ^ x ≤ (3 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
      _ = 27 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  by_cases h : AdjS route sel s
  · have he0 := selE_le route sel s 0
    have he1 := selE_le route sel s 1
    simp only [selF, if_pos h]
    have := h3 (2 * c + (selE route sel s 0 + selE route sel s 1)) (by linarith)
    linarith
  · simp only [selF, if_neg h, selE_eq_zero_of_not_adj route sel s h, add_zero, mul_one]
    calc (3 : ℝ) ^ (2 * c) ≤ (3 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 9 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]; norm_num

end Sel

/-! ## `1 + |Σ a| ≤ ∏ (1 + |a|)` and the moments of the routed frequencies -/

theorem one_add_abs_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    1 + |∑ i ∈ s, a i| ≤ ∏ i ∈ s, (1 + |a i|) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have h0 : 0 ≤ |a x| := abs_nonneg _
    have h1 : 0 ≤ |∑ i ∈ s, a i| := abs_nonneg _
    calc 1 + |a x + ∑ i ∈ s, a i| ≤ 1 + (|a x| + |∑ i ∈ s, a i|) := by
          have := abs_add_le (a x) (∑ i ∈ s, a i); linarith
      _ ≤ (1 + |a x|) * (1 + |∑ i ∈ s, a i|) := by nlinarith
      _ ≤ (1 + |a x|) * ∏ i ∈ s, (1 + |a i|) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (by linarith)

section Routed

variable {G : Garden w} (hS : G.IsPlain) {J : Type} (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J)
  (sel : Finset (GBranch G.tree))

/-- The non-routed slot frequency at the clock `v` (the slot part of main's `AsmCtxH.freqH` at a one-mode family). -/
def routedFreq (frq : ReplacementSlot G → Fin 2 → ℤ) (v : GBranch G.tree) : ℝ :=
  ∑ s, ∑ i, if argSrc hS s i = Sum.inr v then ((frqR frq route s i : ℤ) : ℝ) else 0

/-- **The selection moment of the routed frequencies is paid by the adjacent slots.** -/
theorem momS_routed_le (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (frq : ReplacementSlot G → Fin 2 → ℤ) :
    momS sel (routedFreq hS route frq) ≤ ∏ s, ∏ i, (1 + |(frq s i : ℝ)|) ^ selE route sel s i := by
  classical
  -- the summands, through the routing
  set b : GBranch G.tree → ReplacementSlot G → Fin 2 → ℝ := fun v s i =>
    if route s i = Sum.inl (Sum.inr v) then (frq s i : ℝ) else 0 with hb
  have hsum : ∀ v, routedFreq hS route frq v = ∑ s, ∑ i, b v s i := by
    intro v
    unfold routedFreq
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [hb]
    rcases hroute s i with h | ⟨j, h⟩
    · simp only [frqR, h, Sum.inl.injEq]
    · simp only [frqR, h, Int.cast_zero, reduceCtorEq, if_false]; split_ifs <;> rfl
  -- one selected branch
  have hv : ∀ v, (1 + |routedFreq hS route frq v|) ^ (1 / 18 : ℝ) ≤
      ∏ s, ∏ i, (if route s i = Sum.inl (Sum.inr v) then (1 + |(frq s i : ℝ)|) ^ (1 / 18 : ℝ) else 1) := by
    intro v
    have h1 : 1 + |routedFreq hS route frq v| ≤ ∏ s, ∏ i, (1 + |b v s i|) := by
      rw [hsum v]
      refine (one_add_abs_sum_le_prod _ _).trans (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun s _ => ?_)
      exact one_add_abs_sum_le_prod _ _
    have h2 : (∏ s, ∏ i, (1 + |b v s i|)) ^ (1 / 18 : ℝ) =
        ∏ s, ∏ i, (if route s i = Sum.inl (Sum.inr v) then (1 + |(frq s i : ℝ)|) ^ (1 / 18 : ℝ) else 1) := by
      rw [← Real.finsetProd_rpow _ _ (fun s _ => Finset.prod_nonneg fun i _ => by positivity)]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hb]
      split_ifs <;> simp
    calc _ ≤ (∏ s, ∏ i, (1 + |b v s i|)) ^ (1 / 18 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      _ = _ := h2
  unfold momS
  calc ∏ v ∈ sel, (1 + |routedFreq hS route frq v|) ^ (1 / 18 : ℝ)
      ≤ ∏ v ∈ sel, ∏ s, ∏ i,
          (if route s i = Sum.inl (Sum.inr v) then (1 + |(frq s i : ℝ)|) ^ (1 / 18 : ℝ) else 1) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) fun v _ => hv v
    _ = ∏ s, ∏ i, ∏ v ∈ sel,
          (if route s i = Sum.inl (Sum.inr v) then (1 + |(frq s i : ℝ)|) ^ (1 / 18 : ℝ) else 1) := by
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [Finset.prod_comm]
    _ = _ := by
        refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
        unfold selE
        by_cases hex : ∃ v ∈ sel, route s i = Sum.inl (Sum.inr v)
        · obtain ⟨v₀, hv₀, hr⟩ := hex
          rw [if_pos ⟨v₀, hv₀, hr⟩, Finset.prod_eq_single v₀]
          · rw [if_pos hr]
          · intro v _ hne
            rw [if_neg]
            intro h'
            rw [hr] at h'
            exact hne (Sum.inr_injective (Sum.inl_injective h')).symm
          · intro h'; exact absurd hv₀ h'
        · rw [if_neg hex, Real.rpow_zero]
          refine Finset.prod_eq_one fun v hv => ?_
          rw [if_neg]
          exact fun h' => hex ⟨v, hv, h'⟩

@[simp] theorem routedFreq_apply (frq : ReplacementSlot G → Fin 2 → ℤ) (v : GBranch G.tree) :
    routedFreq hS route frq v = ∑ s, ∑ i, if argSrc hS s i = Sum.inr v then ((frqR frq route s i : ℤ) : ℝ) else 0 :=
  rfl

end Routed

/-! ## The slot bound and the mode sum -/

/-- Per-slot bound (copy-generalization of U1's `prod_one_add_abs_mul_le_maxBracketPow`): two clock losses of
exponent `c` and two moments of exponents `e i` are paid by `K ⟨m/2⟩^θ` when `θ ≥ 2c + Σ e` and
`K ≥ 3^{2c + Σ e}`. -/
theorem slot_moment_le (m : Fin 2 → ℤ) (e : Fin 2 → ℝ) {c θ K : ℝ} (hc : 0 ≤ c) (he : ∀ i, 0 ≤ e i)
    (hθ : 2 * c + (e 0 + e 1) ≤ θ) (hK : (3 : ℝ) ^ (2 * c + (e 0 + e 1)) ≤ K) :
    ENNReal.ofReal ((∏ i, (1 + |(m i : ℝ)|) ^ c) * ∏ i, (1 + |(m i : ℝ)|) ^ e i) ≤
      ENNReal.ofReal K * maxBracketPow θ (half m) := by
  unfold maxBracketPow half
  set X : ℝ := (⨆ i, Real.sqrt (1 + ((m i : ℝ) / 2) ^ 2)) ⊔ 1 with hX
  have hX1 : 1 ≤ X := le_sup_right
  have hbdd : BddAbove (Set.range fun i : Fin 2 => Real.sqrt (1 + ((m i : ℝ) / 2) ^ 2)) :=
    (Set.finite_range _).bddAbove
  have hi : ∀ i, 1 + |(m i : ℝ)| ≤ 3 * X := fun i =>
    (one_add_abs_int_le (m i)).trans (mul_le_mul_of_nonneg_left
      ((le_ciSup hbdd i).trans le_sup_left) (by norm_num))
  have hX0 : 0 < 3 * X := by linarith
  have hp : ∀ i (r : ℝ), 0 ≤ r → (1 + |(m i : ℝ)|) ^ r ≤ (3 * X) ^ r := fun i r hr =>
    Real.rpow_le_rpow (by positivity) (hi i) hr
  have hsplit : (3 * X) ^ (2 * c + (e 0 + e 1)) =
      ((3 * X) ^ c * (3 * X) ^ c) * ((3 * X) ^ e 0 * (3 * X) ^ e 1) := by
    rw [show 2 * c + (e 0 + e 1) = (c + c) + (e 0 + e 1) by ring, Real.rpow_add hX0, Real.rpow_add hX0,
      Real.rpow_add hX0]
  have h1 : (∏ i, (1 + |(m i : ℝ)|) ^ c) * ∏ i, (1 + |(m i : ℝ)|) ^ e i ≤
      (3 * X) ^ (2 * c + (e 0 + e 1)) := by
    rw [Fin.prod_univ_two, Fin.prod_univ_two, hsplit]
    exact mul_le_mul (mul_le_mul (hp 0 c hc) (hp 1 c hc) (by positivity) (by positivity))
      (mul_le_mul (hp 0 _ (he 0)) (hp 1 _ (he 1)) (by positivity) (by positivity)) (by positivity)
      (by positivity)
  have h2 : (3 * X) ^ (2 * c + (e 0 + e 1)) = (3 : ℝ) ^ (2 * c + (e 0 + e 1)) * X ^ (2 * c + (e 0 + e 1)) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h5 : X ^ (2 * c + (e 0 + e 1)) ≤ X ^ θ := Real.rpow_le_rpow_of_exponent_le hX1 hθ
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  have h6 : (∏ i, (1 + |(m i : ℝ)|) ^ c) * ∏ i, (1 + |(m i : ℝ)|) ^ e i ≤ K * X ^ θ := by
    refine h1.trans ?_
    rw [h2]
    exact mul_le_mul hK h5 (by positivity) hK0
  calc _ ≤ ENNReal.ofReal (K * X ^ θ) := ENNReal.ofReal_le_ofReal h6
    _ = ENNReal.ofReal K * ENNReal.ofReal (X ^ θ) := ENNReal.ofReal_mul hK0

/-- **The mode sum with selection moments** (main's `modes_mass_le` + U1's `ModesMomentSel`, two moments per slot,
per-slot time weights `θ s` and per-slot constants `Ks s ≥ 3^{2c + Σ_i e s i}`). -/
theorem modes_mass_sel_le {G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) {Λ : ReplacementSlot G → Type}
    (W : ∀ s, Λ s → ℝ) (hW : ∀ s l, 0 ≤ W s l) (m : ∀ s, Λ s → Fin 2 → ℤ) {c : ℝ} (hc : 0 ≤ c)
    (e : ReplacementSlot G → Fin 2 → ℝ) (he : ∀ s i, 0 ≤ e s i) (θ : ReplacementSlot G → ℝ)
    (hθ : ∀ s, 2 * c + (e s 0 + e s 1) ≤ θ s) (Ks : ReplacementSlot G → ℝ)
    (hKs : ∀ s, (3 : ℝ) ^ (2 * c + (e s 0 + e s 1)) ≤ Ks s) (μ : ReplacementSlot G → ℝ≥0∞)
    (hμ : ∀ s, ∑' l, maxBracketPow (θ s) (half (m s l)) * ENNReal.ofReal (W s l) ≤ μ s) (Kc : ℝ) (hKc : 0 ≤ Kc) :
    ∑' ξ : ∀ s, Λ s, ENNReal.ofReal (‖(((∏ s, W s (ξ s) : ℝ)) : ℂ)‖ *
      (Kc * ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
      ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i) ≤
      ENNReal.ofReal Kc * ∏ s, (ENNReal.ofReal (Ks s) * μ s) := by
  have h1 : ∀ ξ : ∀ s, Λ s, ENNReal.ofReal (‖(((∏ s, W s (ξ s) : ℝ)) : ℂ)‖ *
      (Kc * ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
      ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i) ≤
      ENNReal.ofReal Kc * ∏ s, (ENNReal.ofReal (Ks s) *
        (maxBracketPow (θ s) (half (m s (ξ s))) * ENNReal.ofReal (W s (ξ s)))) := by
    intro ξ
    have hb := prod_modLam_le (fun s => m s (ξ s)) route hc
    have hp : 0 ≤ ∏ s, W s (ξ s) := Finset.prod_nonneg fun s _ => hW s _
    have hq : 0 ≤ ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i :=
      Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun i _ => by positivity
    rw [Complex.norm_real, Real.norm_of_nonneg hp]
    calc ENNReal.ofReal ((∏ s, W s (ξ s)) * (Kc * ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
          ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i)
        ≤ ENNReal.ofReal ((∏ s, W s (ξ s)) * (Kc * ∏ s, ∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
          ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hb hKc) hp) hq
      _ = ENNReal.ofReal (Kc * ∏ s, (W s (ξ s) * ((∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
            ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring_nf
      _ = ENNReal.ofReal Kc * ∏ s, ENNReal.ofReal (W s (ξ s) * ((∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
            ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i)) := by
          rw [ENNReal.ofReal_mul hKc, ENNReal.ofReal_prod_of_nonneg fun s _ => mul_nonneg (hW s _)
            (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (Finset.prod_nonneg fun i _ => by positivity))]
      _ ≤ _ := by
          gcongr with s
          rw [ENNReal.ofReal_mul (hW s _)]
          calc _ ≤ ENNReal.ofReal (W s (ξ s)) *
                (ENNReal.ofReal (Ks s) * maxBracketPow (θ s) (half (m s (ξ s)))) := by
                gcongr
                exact slot_moment_le _ (e s) hc (he s) (hθ s) (hKs s)
            _ = _ := by ring
  calc _ ≤ ∑' ξ : ∀ s, Λ s, ENNReal.ofReal Kc * ∏ s, (ENNReal.ofReal (Ks s) *
        (maxBracketPow (θ s) (half (m s (ξ s))) * ENNReal.ofReal (W s (ξ s)))) := ENNReal.tsum_le_tsum h1
    _ = ENNReal.ofReal Kc * ∏ s, ∑' l, ENNReal.ofReal (Ks s) *
          (maxBracketPow (θ s) (half (m s l)) * ENNReal.ofReal (W s l)) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact ennreal_tsum_pi_prod_fintype
          (fun s l => ENNReal.ofReal (Ks s) * (maxBracketPow (θ s) (half (m s l)) * ENNReal.ofReal (W s l)))
    _ ≤ _ := by
        gcongr with s
        rw [ENNReal.tsum_mul_left]
        gcongr; exact hμ s

end WaveTurbulence.Flower.MkSlotsS
