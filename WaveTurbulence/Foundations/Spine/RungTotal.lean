/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RungSupp
public import WaveTurbulence.Foundations.Spine.RungBudget
/-! # The total one-rung time bound (S3b LADDER-DECAY)

Every good rung weight (kinds F, X, Y, Z; `R = L^{1-γ+η}`) has rung time integral
`≲ δ⁻¹ L^{2d-2γ}`, and `≲ δ⁻¹ L^{2d-2γ} L^{-x}` for rungs on different layers. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory Set Filter WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint

variable {d : ℕ}

/-- The four kinds of rung weights (constant, x-ball, y-ball, finite set). -/
def GoodTerm (L R : ℝ) (a b : Fin d → ℝ) (χ : Pt d → ℝ) : Prop :=
  (∀ p, χ p = 1) ∨ KindX R χ ∨ KindY R χ ∨
    ((∀ p, |χ p| ≤ 1) ∧ ∃ T : Finset (Pt d),
      (T.card : ℝ) ≤ (2 * R + 1) ^ (2 * d) + (8 * L + 1) ^ d ∧
      ∀ p, ((χ p : ℝ) : ℂ) * cutW L a b p ≠ 0 → p ∈ T)

/-- The conclusion of the rung bound for a fixed weight. -/
def RungOK (γ x T1 δ L C0 : ℝ) (a b : Fin d → ℝ) (χ : Pt d → ℝ) : Prop :=
  ∀ (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ) (l u v w : ℝ),
      (∀ p, ((χ p : ℝ) : ℂ) * cutW L a b p ≠ 0 → p ∈ S) → l ≤ u → v ≤ w → u - l ≤ 1 → w - v ≤ 1 →
      WindowOK T1 L (δ * L ^ (2 * γ)) l u v w γ →
      (∫ t in Icc v w, ∫ s in Icc l u, ‖rungSum L (δ * L ^ (2 * γ))
          (fun p => ((χ p : ℝ) : ℂ) * cutW L a b p) S lam ν (s, t)‖) ≤
        C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ)) ∧
      (u ≤ v ∨ w ≤ l →
        (∫ t in Icc v w, ∫ s in Icc l u, ‖rungSum L (δ * L ^ (2 * γ))
          (fun p => ((χ p : ℝ) : ℂ) * cutW L a b p) S lam ν (s, t)‖) ≤
        C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x)))

lemma eventually_le_rpow (K e : ℝ) (he : 0 < e) : ∀ᶠ L : ℝ in atTop, K ≤ L ^ e :=
  (tendsto_rpow_atTop he).eventually_ge_atTop K


lemma rung_env {γ η T1 x δ : ℝ} (hγ0 : 0 < γ) (_hγ1 : γ < 1) (hη : 0 < η)
    (hη2 : η < 1 - γ) (hx1 : x < 2 * γ) :
    ∃ L1 : ℝ, 2 ≤ L1 ∧ ∀ L : ℝ, L1 ≤ L → δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x) ∧
      6 * (16 * T1 + 1) ≤ 16 * L ^ (1 - γ - η) := by
  have hev : ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧ δ⁻¹ ≤ L ^ (2 * γ - x) ∧
      6 * (16 * T1 + 1) ≤ 16 * L ^ (1 - γ - η) := by
    refine (eventually_ge_atTop 2).and ((eventually_le_rpow _ _ (by linarith)).and ?_)
    have := eventually_le_rpow (6 * (16 * T1 + 1) / 16) (1 - γ - η) (by linarith)
    filter_upwards [this] with L hL
    linarith
  obtain ⟨L1, hL1⟩ := eventually_atTop.mp hev
  refine ⟨L1, (hL1 L1 le_rfl).1, fun L hL => ?_⟩
  obtain ⟨h2L, hδL, hT⟩ := hL1 L hL
  refine ⟨?_, hT⟩
  have hL0 : 0 < L := by linarith
  have : L ^ (2 * γ - x) = L ^ (2 * γ) * L ^ (-x) := by
    rw [sub_eq_add_neg, Real.rpow_add hL0]
  have hpos : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL0 _
  calc δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (2 * γ - x) * (L ^ (2 * γ))⁻¹ := by gcongr
    _ = L ^ (-x) := by rw [this]; field_simp

lemma ball_cube_facts {γ η T1 L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ γ) (hL : 1 ≤ L) (hT : 6 * (16 * T1 + 1) ≤ 16 * L ^ (1 - γ - η)) (hT1 : 0 < T1) :
    1 ≤ L ^ (1 - γ + η) ∧ 2 * L ^ (1 - γ + η) + 1 ≤ 4 * L ∧
    2 * (16 * T1 * L ^ (2 * γ) + 1) * (2 * L ^ (1 - γ + η) + 1) ≤ (4 * L) ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hR1 : 1 ≤ L ^ (1 - γ + η) := Real.one_le_rpow hL (by linarith)
  have hRL : L ^ (1 - γ + η) ≤ L := by
    calc L ^ (1 - γ + η) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
      _ = L := Real.rpow_one L
  refine ⟨hR1, by linarith, ?_⟩
  have hp : 1 ≤ L ^ (2 * γ) := Real.one_le_rpow hL (by linarith)
  have e1 : 16 * T1 * L ^ (2 * γ) + 1 ≤ (16 * T1 + 1) * L ^ (2 * γ) := by nlinarith
  have e2 : 2 * L ^ (1 - γ + η) + 1 ≤ 3 * L ^ (1 - γ + η) := by linarith
  have e3 : L ^ (2 * γ) * L ^ (1 - γ + η) = L ^ (1 + γ + η) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have e4 : (4 * L) ^ 2 = 16 * L ^ (1 - γ - η) * L ^ (1 + γ + η) := by
    rw [mul_assoc, ← Real.rpow_add hL0]
    have : (1 - γ - η + (1 + γ + η)) = ((2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]; ring
  have hpos : 0 ≤ L ^ (1 + γ + η) := by positivity
  calc 2 * (16 * T1 * L ^ (2 * γ) + 1) * (2 * L ^ (1 - γ + η) + 1)
      ≤ 2 * ((16 * T1 + 1) * L ^ (2 * γ)) * (3 * L ^ (1 - γ + η)) := by gcongr
    _ = 6 * (16 * T1 + 1) * (L ^ (2 * γ) * L ^ (1 - γ + η)) := by ring
    _ = 6 * (16 * T1 + 1) * L ^ (1 + γ + η) := by rw [e3]
    _ ≤ 16 * L ^ (1 - γ - η) * L ^ (1 + γ + η) := by gcongr
    _ = _ := e4.symm

lemma window_ball {γ T1 L c l u v w : ℝ}
    (hwin : WindowOK T1 L c l u v w γ) :
    ∀ t ∈ Icc v w, -(16 * T1 * L ^ (2 * γ)) ≤ 16 * c * (l - t) ∧
      16 * c * (u - t) ≤ 16 * T1 * L ^ (2 * γ) := by
  intro t ht
  have := hwin t ht
  constructor <;> linarith [this.1, this.2]

lemma RungOK.mono {γ x T1 δ L C0 C0' : ℝ} {a b : Fin d → ℝ} {χ : Pt d → ℝ} (hL : 0 < L) (hδ : 0 < δ) (h : C0 ≤ C0')
    (hok : RungOK γ x T1 δ L C0 a b χ) : RungOK γ x T1 δ L C0' a b χ := by
  intro S lam ν l u v w hS hlu hvw hul hwv hwin
  obtain ⟨h1, h2⟩ := hok S lam ν l u v w hS hlu hvw hul hwv hwin
  have hE0 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
  have hE1 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x) := by positivity
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right h hE0), fun hd => (h2 hd).trans (mul_le_mul_of_nonneg_right h hE1)⟩


lemma ball_finish_same {γ δ L Cb vw ul I : ℝ} (hd : 3 ≤ d) (hγ1 : γ < 1) (hL1' : 1 ≤ L) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hCb : 0 ≤ Cb) (hvw0 : 0 ≤ vw) (hwv : vw ≤ 1) (hul0 : 0 ≤ ul) (hul : ul ≤ 1)
    (hI : I ≤ vw * (ul * (Cb * (4 * L)) ^ d * 1 + (16 * (δ * L ^ (2 * γ)))⁻¹ *
        ((Cb * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1))))) :
    I ≤ ((4 * Cb) ^ d + (16 * Cb) ^ d / 16) * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ)) := by
  have h2 := budget_ball_same (γ := γ) hd hγ1 hL1' hδ hδ1 hCb hvw0 hwv hul0 hul
  have hL0 : 0 < L := by linarith
  have hE0 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
  exact (hI.trans h2)

lemma ball_finish_diff {γ x δ L Cb vw ul I : ℝ} (hd : 3 ≤ d) (hγ1 : γ < 1) (hx2 : x ≤ 1) (hL1' : 1 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x)) (hCb : 0 ≤ Cb)
    (hvw0 : 0 ≤ vw) (hwv : vw ≤ 1) (hul0 : 0 ≤ ul) (hul : ul ≤ 1)
    (hI : I ≤ vw * (ul * (Cb * (4 * L)) ^ d * 1) + (16 * (δ * L ^ (2 * γ)))⁻¹ *
        ((Cb * (4 * L) ^ 2) ^ d * (2 / ((d : ℝ) - 1))) * (16 * (δ * L ^ (2 * γ)))⁻¹) :
    I ≤ ((4 * Cb) ^ d + (16 * Cb) ^ d / 256) * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x)) :=
  hI.trans (budget_ball_diff (γ := γ) (x := x) hd hγ1 hx2 hL1' hδ hδ1 hB hCb hvw0 hwv hul0 hul)

section kinds
variable (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hη1 : 10 * (d : ℝ) * η ≤ γ) (hη2 : 10 * (d : ℝ) * η ≤ 1 - γ) {T1 : ℝ} (hT1 : 0 < T1) {x : ℝ}
    (hx1 : x < 2 * γ) (hx2 : x ≤ 1) (hx3 : -2 * ((d : ℝ) - 1) * (1 - γ) + η ≤ -x)

include hd hγ hη hη1 hη2 hT1 hx1 hx2 hx3

omit hη1 hx2 in
lemma rung_total_F : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ L1 : ℝ, 2 ≤ L1 ∧ ∀ L : ℝ, L1 ≤ L →
    ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), (∀ p, χ p = 1) → RungOK γ x T1 δ L C0 a b χ := by
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hηd : η ≤ 2 * ((d : ℝ) - 1) * (1 - γ) := by nlinarith
  obtain ⟨Cs, Ls0, hCs, hLs0, hsame⟩ := rung_full_same hd γ ⟨hγ0, hγ1⟩ η hη hηd T1 hT1
  obtain ⟨Cd, Ld0, hCd, hLd0, hdiff⟩ := rung_full_diff hd γ ⟨hγ0, hγ1⟩ η hη hηd T1 hT1
  refine ⟨Cs * 16 ^ d / 16 + Cd * 16 ^ d / 8, by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨L2, hL2, henv⟩ := rung_env (T1 := T1) (δ := δ) hγ0 hγ1 hη (by nlinarith) hx1
  refine ⟨max L2 (max Ls0 Ld0), (hL2.trans (le_max_left _ _)), ?_⟩
  intro L hL a b χ hF S lam ν l u v w hS hlu hvw hul hwv hwin
  have hL2' : L2 ≤ L := (le_max_left _ _).trans hL
  have hLs : Ls0 ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLd : Ld0 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  obtain ⟨hB, -⟩ := henv L hL2'
  have hL1' : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hc : 0 < δ * L ^ (2 * γ) := mul_pos hδ (Real.rpow_pos_of_pos hL0 _)
  have hvw0 : 0 ≤ w - v := sub_nonneg.mpr hvw
  have hE0 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
  have hE1 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x) := by positivity
  have fin : ∀ (a q b C : ℝ), 0 ≤ q → a ≤ C → b ≤ a * q → b ≤ C * q := fun a q b C hq hac hb =>
    hb.trans (mul_le_mul_of_nonneg_right hac hq)
  have hv0 : 0 ≤ Cs * 16 ^ d / 16 := by positivity
  have hv1 : 0 ≤ Cd * 16 ^ d / 8 := by positivity
  have hw : (fun p : Pt d => ((χ p : ℝ) : ℂ) * cutW L a b p) = cutW L a b := by
    funext p; simp [hF p]
  have hS' : ∀ p, cutW L a b p ≠ 0 → p ∈ S := fun p hp => hS p (by simpa [hF p] using hp)
  rw [hw]
  refine ⟨?_, fun hdl => ?_⟩
  · have h1 := hsame L hLs a b _ l u v w lam ν S hc hlu hvw hS' hwin
    have h2 := budget_F_same (γ := γ) hd hL1' hδ hCs hvw0 hwv
    exact fin (Cs * 16 ^ d / 16) _ _ _ hE0 (by linarith) (h1.trans h2)
  · have h1 := hdiff L hLd a b _ l u v w lam ν S hc hlu hvw hS' hwin hdl
    have h2 := budget_F_diff (γ := γ) (x := x) hd hL1' hδ hB hCd hvw0 hwv hx3 (by nlinarith)
    exact fin (Cd * 16 ^ d / 8) _ _ _ hE1 (by linarith) (h1.trans h2)

omit hx3 in
lemma rung_total_X : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ L1 : ℝ, 2 ≤ L1 ∧ ∀ L : ℝ, L1 ≤ L →
    ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), KindX (L ^ (1 - γ + η)) χ → RungOK γ x T1 δ L C0 a b χ := by
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cb, hCb, hball⟩ := rung_ball_time hd
  refine ⟨(4 * Cb) ^ d + (16 * Cb) ^ d / 16 + ((4 * Cb) ^ d + (16 * Cb) ^ d / 256), by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨L2, hL2, henv⟩ := rung_env (T1 := T1) (δ := δ) hγ0 hγ1 hη (by nlinarith) hx1
  refine ⟨L2, hL2, ?_⟩
  intro L hL a b χ hK S lam ν l u v w hS hlu hvw hul hwv hwin
  obtain ⟨hB, hT⟩ := henv L hL
  have hL1' : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hc : 0 < δ * L ^ (2 * γ) := mul_pos hδ (Real.rpow_pos_of_pos hL0 _)
  have hvw0 : 0 ≤ w - v := sub_nonneg.mpr hvw
  have hul0 : 0 ≤ u - l := sub_nonneg.mpr hlu
  have hE0 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
  have hE1 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x) := by positivity
  have fin : ∀ (a q b C : ℝ), 0 ≤ q → a ≤ C → b ≤ a * q → b ≤ C * q := fun a q b C hq hac hb =>
    hb.trans (mul_le_mul_of_nonneg_right hac hq)
  have hv2 : 0 ≤ (4 * Cb) ^ d + (16 * Cb) ^ d / 16 := by positivity
  have hv4 : 0 ≤ (4 * Cb) ^ d + (16 * Cb) ^ d / 256 := by positivity
  obtain ⟨hR1, hKc, hKc2⟩ := ball_cube_facts (η := η) (T1 := T1) hγ0 hγ1 hη (by nlinarith) hL1' hT hT1
  have hwin' := window_ball hwin
  obtain ⟨q, f, hf, hs, he⟩ := hK
  set ι : (Fin d → ℤ) → ℂ := fun x => ((f x : ℝ) : ℂ) with hι
  have hw : (fun p : Pt d => ((χ p : ℝ) : ℂ) * cutW L a b p) = ballW L a b ι := by
    funext p; simp [ballW, hι, he p]
  have hS2 : ∀ p, ballW L a b ι p ≠ 0 → p ∈ S := fun p hp => hS p (by rw [congrFun hw p]; exact hp)
  set Ii := cubeI q (L ^ (1 - γ + η)) with hIi
  have hsupp : ∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset Ii := fun x hx =>
    mem_cubeI (hs x (by intro h; apply hx; simp [hι, h]))
  have hS1 : ∀ p, ballW L a b ι p ≠ 0 → p ∈ Fintype.piFinset Ii ×ˢ byBox L b := by
    intro p hp
    have h1 : ι p.1 ≠ 0 := left_ne_zero_of_mul hp
    have h2 : cutW L a b p ≠ 0 := right_ne_zero_of_mul hp
    exact Finset.mem_product.mpr ⟨hsupp _ h1, (cutW_ne_zero_x hL0 a b p h2).2⟩
  have hcongr : ∀ t s : ℝ, rungSum L (δ * L ^ (2 * γ)) (ballW L a b ι) S lam ν (s, t) =
      rungSum L (δ * L ^ (2 * γ)) (ballW L a b ι) (Fintype.piFinset Ii ×ˢ byBox L b) lam ν (s, t) :=
    fun t s => rungSum_congr_support L _ _ _ _ hS2 hS1 lam ν _
  rw [hw]
  simp only [hcongr]
  have hI : ∀ i, ((Ii i).card : ℝ) ≤ 2 * L ^ (1 - γ + η) + 1 ∧
      ∀ n ∈ Ii i, ∀ n' ∈ Ii i, |(n : ℝ) - n'| ≤ 2 * L ^ (1 - γ + η) + 1 :=
    fun i => ⟨(cubeI_card (by linarith) i), cubeI_diam (by linarith) i⟩
  obtain ⟨hb1, hb2⟩ := hball hL1' a b ι (fun x => by simp [hι]; exact hf x) Ii hsupp lam ν
    (δ * L ^ (2 * γ)) l u v w (16 * T1 * L ^ (2 * γ)) (2 * L ^ (1 - γ + η) + 1) hc hlu hvw hwin'
    (by linarith) hI hKc hKc2
  clear_value ι Ii
  refine ⟨?_, fun hdl => ?_⟩
  · have h3 := ball_finish_same hd hγ1 hL1' hδ hδ1 hCb hvw0 hwv hul0 hul hb1
    exact fin ((4 * Cb) ^ d + (16 * Cb) ^ d / 16) _ _ _ hE0 (by linarith) h3
  · have h3 := ball_finish_diff hd hγ1 hx2 hL1' hδ hδ1 hB hCb hvw0 hwv hul0 hul (hb2 hdl)
    exact fin ((4 * Cb) ^ d + (16 * Cb) ^ d / 256) _ _ _ hE1 (by linarith) h3

omit hx3 in
lemma rung_total_Y : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ L1 : ℝ, 2 ≤ L1 ∧ ∀ L : ℝ, L1 ≤ L →
    ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), KindY (L ^ (1 - γ + η)) χ → RungOK γ x T1 δ L C0 a b χ := by
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cb, hCb, hball⟩ := rung_ballY_time hd
  refine ⟨(4 * Cb) ^ d + (16 * Cb) ^ d / 16 + ((4 * Cb) ^ d + (16 * Cb) ^ d / 256), by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨L2, hL2, henv⟩ := rung_env (T1 := T1) (δ := δ) hγ0 hγ1 hη (by nlinarith) hx1
  refine ⟨L2, hL2, ?_⟩
  intro L hL a b χ hK S lam ν l u v w hS hlu hvw hul hwv hwin
  obtain ⟨hB, hT⟩ := henv L hL
  have hL1' : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hc : 0 < δ * L ^ (2 * γ) := mul_pos hδ (Real.rpow_pos_of_pos hL0 _)
  have hvw0 : 0 ≤ w - v := sub_nonneg.mpr hvw
  have hul0 : 0 ≤ u - l := sub_nonneg.mpr hlu
  have hE0 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
  have hE1 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x) := by positivity
  have fin : ∀ (a q b C : ℝ), 0 ≤ q → a ≤ C → b ≤ a * q → b ≤ C * q := fun a q b C hq hac hb =>
    hb.trans (mul_le_mul_of_nonneg_right hac hq)
  have hv2 : 0 ≤ (4 * Cb) ^ d + (16 * Cb) ^ d / 16 := by positivity
  have hv4 : 0 ≤ (4 * Cb) ^ d + (16 * Cb) ^ d / 256 := by positivity
  obtain ⟨hR1, hKc, hKc2⟩ := ball_cube_facts (η := η) (T1 := T1) hγ0 hγ1 hη (by nlinarith) hL1' hT hT1
  have hwin' := window_ball hwin
  obtain ⟨q, f, hf, hs, he⟩ := hK
  set ι : (Fin d → ℤ) → ℂ := fun x => ((f x : ℝ) : ℂ) with hι
  have hw : (fun p : Pt d => ((χ p : ℝ) : ℂ) * cutW L a b p) = ballWY L a b ι := by
    funext p; simp [ballWY, hι, he p]
  have hS2 : ∀ p, ballWY L a b ι p ≠ 0 → p ∈ S := fun p hp => hS p (by rw [congrFun hw p]; exact hp)
  set Ii := cubeI q (L ^ (1 - γ + η)) with hIi
  have hsupp : ∀ x, ι x ≠ 0 → x ∈ Fintype.piFinset Ii := fun x hx =>
    mem_cubeI (hs x (by intro h; apply hx; simp [hι, h]))
  have hS1 : ∀ p, ballWY L a b ι p ≠ 0 → p ∈ byBox L a ×ˢ Fintype.piFinset Ii := by
    intro p hp
    have h1 : ι p.2 ≠ 0 := left_ne_zero_of_mul hp
    have h2 : cutW L a b p ≠ 0 := right_ne_zero_of_mul hp
    exact Finset.mem_product.mpr ⟨(cutW_ne_zero_x hL0 a b p h2).1, hsupp _ h1⟩
  have hcongr : ∀ t s : ℝ, rungSum L (δ * L ^ (2 * γ)) (ballWY L a b ι) S lam ν (s, t) =
      rungSum L (δ * L ^ (2 * γ)) (ballWY L a b ι) (byBox L a ×ˢ Fintype.piFinset Ii) lam ν (s, t) :=
    fun t s => rungSum_congr_support L _ _ _ _ hS2 hS1 lam ν _
  rw [hw]
  simp only [hcongr]
  have hI : ∀ i, ((Ii i).card : ℝ) ≤ 2 * L ^ (1 - γ + η) + 1 ∧
      ∀ n ∈ Ii i, ∀ n' ∈ Ii i, |(n : ℝ) - n'| ≤ 2 * L ^ (1 - γ + η) + 1 :=
    fun i => ⟨(cubeI_card (by linarith) i), cubeI_diam (by linarith) i⟩
  obtain ⟨hb1, hb2⟩ := hball hL1' a b ι (fun x => by simp [hι]; exact hf x) Ii hsupp lam ν
    (δ * L ^ (2 * γ)) l u v w (16 * T1 * L ^ (2 * γ)) (2 * L ^ (1 - γ + η) + 1) hc hlu hvw hwin'
    (by linarith) hI hKc hKc2
  clear_value ι Ii
  refine ⟨?_, fun hdl => ?_⟩
  · have h3 := ball_finish_same hd hγ1 hL1' hδ hδ1 hCb hvw0 hwv hul0 hul hb1
    exact fin ((4 * Cb) ^ d + (16 * Cb) ^ d / 16) _ _ _ hE0 (by linarith) h3
  · have h3 := ball_finish_diff hd hγ1 hx2 hL1' hδ hδ1 hB hCb hvw0 hwv hul0 hul (hb2 hdl)
    exact fin ((4 * Cb) ^ d + (16 * Cb) ^ d / 256) _ _ _ hE1 (by linarith) h3

omit hT1 hx3 in
lemma rung_total_Z : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ L1 : ℝ, 2 ≤ L1 ∧ ∀ L : ℝ, L1 ≤ L →
    ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), ((∀ p, |χ p| ≤ 1) ∧ ∃ T : Finset (Pt d),
      (T.card : ℝ) ≤ (2 * L ^ (1 - γ + η) + 1) ^ (2 * d) + (8 * L + 1) ^ d ∧
      ∀ p, ((χ p : ℝ) : ℂ) * cutW L a b p ≠ 0 → p ∈ T) → RungOK γ x T1 δ L C0 a b χ := by
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨2 * 9 ^ d, by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨L2, hL2, henv⟩ := rung_env (T1 := T1) (δ := δ) hγ0 hγ1 hη (by nlinarith) hx1
  refine ⟨L2, hL2, ?_⟩
  intro L hL a b χ hZ S lam ν l u v w hS hlu hvw hul hwv hwin
  have hL1' : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hE0 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
  have hE1 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x) := by positivity
  have fin : ∀ (a q b C : ℝ), 0 ≤ q → a ≤ C → b ≤ a * q → b ≤ C * q := fun a q b C hq hac hb =>
    hb.trans (mul_le_mul_of_nonneg_right hac hq)
  obtain ⟨hχb, T, hT, hsupT⟩ := hZ
  have hw1 : ∀ p, ‖((χ p : ℝ) : ℂ) * cutW L a b p‖ ≤ 1 := by
    intro p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχb p)).trans (norm_cutW_le L a b p)
  have hcongr : ∀ t s : ℝ, rungSum L (δ * L ^ (2 * γ)) (fun p => ((χ p : ℝ) : ℂ) * cutW L a b p) S lam ν (s, t) =
      rungSum L (δ * L ^ (2 * γ)) (fun p => ((χ p : ℝ) : ℂ) * cutW L a b p) T lam ν (s, t) :=
    fun t s => rungSum_congr_support L _ _ _ _ hS hsupT lam ν _
  simp only [hcongr]
  have h1 := rung_trivial L (δ * L ^ (2 * γ)) T (fun p => ((χ p : ℝ) : ℂ) * cutW L a b p) hw1 lam ν l u v w hlu hvw
  have hcard : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hvw0 : 0 ≤ w - v := sub_nonneg.mpr hvw
  have hul0 : 0 ≤ u - l := sub_nonneg.mpr hlu
  have h3 : (w - v) * ((u - l) * T.card) ≤ T.card := by
    calc (w - v) * ((u - l) * T.card) ≤ 1 * (1 * T.card) := by gcongr
      _ = _ := by ring
  have hbz := budget_Z (γ := γ) (x := x) (η := η) (δ := δ) hd hγ0 hγ1 hη hη1 hx1 hx2 hL1' hδ hδ1
  have hbz0 := budget_Z (γ := γ) (x := 0) (η := η) (δ := δ) hd hγ0 hγ1 hη hη1 (by linarith) (by norm_num)
    hL1' hδ hδ1
  rw [neg_zero, Real.rpow_zero, mul_one] at hbz0
  refine ⟨?_, fun hdl => ?_⟩
  · exact fin (2 * 9 ^ d) _ _ _ hE0 le_rfl (h1.trans (h3.trans (hT.trans hbz0)))
  · exact fin (2 * 9 ^ d) _ _ _ hE1 le_rfl (h1.trans (h3.trans (hT.trans hbz)))

/-- **The total one-rung bound**: all good weights, with one constant. -/
theorem rung_total : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ L1 : ℝ, 2 ≤ L1 ∧ ∀ L : ℝ, L1 ≤ L →
    ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ → RungOK γ x T1 δ L C0 a b χ := by
  obtain ⟨CF, hCF, hF⟩ := rung_total_F hd hγ hη hη2 hT1 hx1 hx3
  obtain ⟨CX, hCX, hX⟩ := rung_total_X hd hγ hη hη1 hη2 hT1 hx1 hx2
  obtain ⟨CY, hCY, hY⟩ := rung_total_Y hd hγ hη hη1 hη2 hT1 hx1 hx2
  obtain ⟨CZ, hCZ, hZ⟩ := rung_total_Z hd hγ hη hη1 hη2 hx1 hx2
  refine ⟨CF + CX + CY + CZ, by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨LF, hLF, hF'⟩ := hF δ hδ hδ1
  obtain ⟨LX, hLX, hX'⟩ := hX δ hδ hδ1
  obtain ⟨LY, hLY, hY'⟩ := hY δ hδ hδ1
  obtain ⟨LZ, hLZ, hZ'⟩ := hZ δ hδ hδ1
  refine ⟨max (max LF LX) (max LY LZ), (hLF.trans ((le_max_left _ _).trans (le_max_left _ _))), ?_⟩
  intro L hL a b χ hχ
  have hL0 : 0 < L := by
    have := (hLF.trans ((le_max_left _ _).trans (le_max_left _ _))).trans hL; linarith
  have hLF' : LF ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLX' : LX ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hLY' : LY ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLZ' : LZ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  rcases hχ with h | h | h | h
  · exact (hF' L hLF' a b χ h).mono hL0 hδ (by linarith)
  · exact (hX' L hLX' a b χ h).mono hL0 hδ (by linarith)
  · exact (hY' L hLY' a b χ h).mono hL0 hδ (by linarith)
  · exact (hZ' L hLZ' a b χ h).mono hL0 hδ (by linarith)

end kinds
end WaveTurbulence.LadderDecay
