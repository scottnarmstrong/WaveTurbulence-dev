/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.LGLow.Assembly
public import WaveTurbulence.Foundations.FlowerTop.P7Prefix

/-! # LG-low (packet L07): the flower couple clause through the waist, part 1

Main's `FlowerP7.LGContext` (`FlowerTop/Port/P7/Slices.lean`) with its gate fields (`hcoarse`, `hfourier`, `hcount`,
`habs`, `hgate`) replaced by `hTG : TypeGateAt P`; main's slice estimates `garden_estimate_slice_of_gate_tt`,
`couple_estimate_slice_of_gate_tt` (`Port/P7/LGTT.lean`) through the waist; and the P7 declarations that carry an
`LGContext`, copied by source (sha256 in `COPIED-SHA256SUMS`; replacements listed there). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow.CC
open WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.GammaLow.LGLow

section
-- source: FlowerTop/Port/P7/Slices.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

/-- The shared hypotheses of LG-SPINE's estimates (as in `garden_estimate_slice_of_gate`). -/
structure LGContext (C₀ : ℕ) (P : WTParams) where
  hs : PieceSmall P
  hTG : TypeGateAt P
  hlog : 1 ≤ Real.log P.L
  hd : 1 ≤ P.d
  hlowP : LowProfileAt P
  htime : P.τstar = (P.D : ℝ) * P.δ
  Cφ : ℝ
  hCφ : 0 ≤ Cφ
  hφ : ∀ τ ∈ Set.Icc (0 : ℝ) P.τstar, SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ

end

section
-- source: FlowerTop/Port/P7/LGTT.lean
open WaveTurbulence.FlowerP7
open MeasureTheory Set Finset NormBridgeScratch WaveTurbulence.LGSpine
open scoped Classical ENNReal

theorem garden_estimate_slice_of_typeGate_tt (P : WTParams) (hs : PieceSmall P) (hTG : TypeGateAt P)
    (hd : 1 ≤ P.d) (hlowP : LowProfileAt P) (htime : P.τstar = (P.D : ℝ) * P.δ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ)
    {p : ℕ} (hp : p < P.D) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    {m : ℕ} (hm2 : 2 ≤ m) (hmmax : m ≤ 10 * P.R (p + 1)) (ζ : Fin (2 * m) → ℤˣ)
    (hζ : IsBalancedSig ζ) (n : Fin (2 * m) → (Fin P.d → ℤ)) (k : Mom P.d) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) (tt : Fin (2 * m) → ℝ) (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1))
    (A : Finset (LayeredGarden (2 * m)))
    (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1))
      (P.N (p + 1 - 1)) ∧ LG.garden.sig = ζ ∧ LG.garden.order = N)
    (hTC : TwistClosed p A)
    (hnum : ((P.d : ℝ) + 1) ^ (4 * m * P.Lambda (p + 1)) * gardenT P Cφ p m N ^ (8 * m * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N + m) * P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) / 70) ≤ 1) :
    ‖∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun b => tt b.1.1) 0 k n 0‖ ≤
      jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
        P.δ ^ (2 * P.ν * N) := by
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hδ0 := hs.delta_pos
  have hC₁ := hs.c1_ge
  set Λ := P.Lambda (p + 1) with hΛ
  set W : ℝ := jbrProdAt P.L k n ^ (4 * Λ) with hW
  have hJ : 0 < jbrProdAt P.L k n := Finset.prod_pos fun j _ => WaveTurbulence.Induct.jbr_pos _
  have hWpos : 0 < W := by
    rw [hW]
    exact pow_pos hJ _
  have hrpow : jbrProdAt P.L k n ^ (-(4 * Λ : ℝ)) = W⁻¹ := by
    rw [hW, Real.rpow_neg hJ.le]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  have hrhs : 0 ≤ P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * N) :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hδ0.le _)
  rw [hrpow]
  by_cases hN0 : N = 0
  · subst hN0
    have hz : ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun b => tt b.1.1) 0 k n 0 = 0 := by
      apply Finset.sum_eq_zero
      intro LG hLG
      exfalso
      have hmem := hA LG hLG
      exact garden_support_order_ne_zero P hm2 LG hmem.1 hmem.2.2.2
    rw [hz, norm_zero]
    have : 0 ≤ W⁻¹ * P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * ((0 : ℕ) : ℝ)) := by
      have := hrhs
      positivity
    exact this
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have hmemA := hA
  set A0 := A with hA0
  have hcar : ∀ LG ∈ A0, Stage1Carries P p N LG :=
    fun LG hLG => stage1Carries_of_garden_support P hm2 ζ hζ LG (hmemA LG hLG)
  have hplain : ∀ LG ∈ A0, LG.garden.IsPlain := fun LG h => (hmemA LG h).1.1
  have hlay : ∀ LG ∈ A0, ∀ a, LG.layer a ≤ p := fun LG h => Canon.layer_le_of_isCanonGC (hmemA LG h).1
  have hcard : ∀ LG ∈ A0, (inputLeaves LG.garden).card = N + m := by
    intro LG hLG
    have h1 := twice_card_inputLeaves LG.garden (hplain LG hLG)
    have h2 : LG.garden.order = N := (hmemA LG hLG).2.2.2
    omega
  have hΛ40 : 40 * P.d ≤ Λ := forty_dim_le_Lambda P hd (show p + 1 ≤ P.D by omega)
  set M : ℕ := (N + m + 1) / 2 with hMdef
  have hM1 : 1 ≤ M := by omega
  set Lops : ℕ := 8 * m * Λ with hLops
  have hLops1 : 1 ≤ Lops := by
    have : 1 ≤ m := by omega
    have : 1 ≤ Λ := by omega
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  set U : ℝ := Cφ + 1 with hUdef
  have hU0 : 0 ≤ U := by linarith
  set y : ℝ := P.C₁ / (2 * max U P.C₁ * Lops) with hy
  obtain ⟨hy1, hy2⟩ := step_params (C₁ := P.C₁) (U := U) (by linarith) hU0 Lops hLops1
  have hLopsR : (0 : ℝ) < Lops := by exact_mod_cast hLops1
  have hymax : 0 < max U P.C₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hypos : 0 < y := by rw [hy]; positivity
  set κ : ℝ := (2 * (P.d : ℝ)) ^ (40 * P.d + 0) with hκ
  have hd1 : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hκ1 : 1 ≤ κ := one_le_pow₀ (by linarith)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set xs : ℝ := y / κ with hxs
  have hxspos : 0 < xs := by positivity
  set lam : ℝ := xs / M with hlam
  have hlampos : 0 < lam := by positivity
  have hxsκ : xs * κ = y := by rw [hxs]; field_simp
  -- the input bounds
  have hinp := all_stage_input_bounds P hd hL1 hδ0.le htime hlowP hC₁ hCφ hφ hp Rr hRr
  have hbud := modification_order_budget P hd hp
  have hhi := stage_input_bounds_gen P hd hL1 hδ0.le htime hlowP hC₁ hCφ hφ hp Rr hRr
    (a := 0) (b := 4 * (2 * Λ)) (by omega) (by omega)
  let h0 : TProf P.d (2 * m) := fun q _ _ => inputsF P Rr q
  have hInv : ∀ c : Fin (2 * m) → Fin (2 * Λ) → Option (Fin P.d),
      Inv p (40 * P.d) (40 * P.d) ((opsOfChoice c).map fun f => TOp.form f.1 f.2) U P.C₁ h0 := by
    intro c q hq j j'
    rw [dcnt_forms]
    obtain ⟨h1, h2⟩ := hhi q hq
    have hf := fcnt_opsOfChoice c j j'
    refine ⟨h1, ?_, (hinp q hq).2.2⟩
    exact SNormR_mono_bound le_rfl (by omega) _ h1 U hU0 h2
  let σ : Fin (2 * m) → ℝ := fun j => ((ζ j : ℤ) : ℝ)
  have hctx : EvalCtx P A0 p M σ :=
    { hd := hd, hL := hL1, hM1 := hM1, plain := hplain, lay := hlay
      card := fun LG hLG => by rw [hcard LG hLG]; omega
      sig := fun LG hLG j0 => by
        rw [nodeSign_root_eq, (hmemA LG hLG).2.2.1] }
  have hσ2 : ∀ j, σ j ^ 2 = 1 := fun j => units_sq_real (ζ j)
  have hadm : ∀ c : Fin (2 * m) → Fin (2 * Λ) → Option (Fin P.d),
      AdmI P p ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 :=
    fun c => AdmI_of_Inv hd hU0 (by linarith) (hInv c)
  have hid := garden_weight_identity_at hctx hσ2 tt n k lam hlampos.ne' (2 * Λ) h0 hadm
  -- the bound on each term
  set T : ℝ := gardenT P Cφ p m N with hT
  have hTeq : (2 * (M : ℝ) + 1) / |lam| = T := by
    rw [abs_of_pos hlampos, hlam, hxs, hT, gardenT, hy]
    push_cast [hLops]
    field_simp
    rw [← hMdef, ← hUdef, ← hΛ, hκ, Nat.add_zero]
    ring
  have hT1 : 1 ≤ T := by
    rw [← hTeq, abs_of_pos hlampos, hlam, hxs, hy]
    have h2 : 1 ≤ (2 * (M : ℝ) + 1) := by linarith
    have h3 : 1 ≤ (2 * (M : ℝ) + 1) * M * κ := by
      have := one_le_mul_of_one_le_of_one_le h2 hMR
      exact one_le_mul_of_one_le_of_one_le this hκ1
    have e : (2 * (M : ℝ) + 1) / (P.C₁ / (2 * max U P.C₁ * Lops) / κ / M) =
        (2 * (M : ℝ) + 1) * M * κ * (2 * max U P.C₁ * Lops / P.C₁) := by
      field_simp
    rw [e]
    refine one_le_mul_of_one_le_of_one_le h3 ?_
    rw [le_div_iff₀ (by linarith)]
    have hLR : (1 : ℝ) ≤ Lops := by exact_mod_cast hLops1
    have := le_max_right U P.C₁
    nlinarith
  let B₀ : NNReal := ⟨2 * P.C₁, by linarith⟩
  have hB₀ : 0 < (B₀ : ℝ) := by show 0 < 2 * P.C₁; linarith
  have hxM : ∀ m' ∈ Finset.range (2 * M + 1), |lam * ((m' : ℝ) - M)| ≤ xs := by
    intro m' hm'
    have hm'2 : m' ≤ 2 * M := by have := Finset.mem_range.mp hm'; omega
    rw [abs_mul, abs_of_pos hlampos]
    have : |(m' : ℝ) - M| ≤ M := by
      rw [abs_le]
      have : (m' : ℝ) ≤ 2 * M := by exact_mod_cast hm'2
      constructor <;> linarith [(Nat.cast_nonneg m' : (0 : ℝ) ≤ m')]
    calc lam * |(m' : ℝ) - M| ≤ lam * M := mul_le_mul_of_nonneg_left this hlampos.le
      _ = xs := by rw [hlam]; field_simp
  have hterm : ∀ c : Fin (2 * m) → Fin (2 * Λ) → Option (Fin P.d),
      ‖evalOps (evalV P A0 tt n) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 k‖ ≤
        T ^ Lops * (((B₀ : ℝ)) ^ (N + m) *
          (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) * (1 / 4 + 1 / 70))))) := by
    intro c
    refine evalOps_typeGate_bound P hs hTG hd hp (by omega) hmmax hN1 hN A0 hcar
      hTC tt htt n hplain k M lam T hT1 hTeq.le xs hxspos.le hxM 0 B₀ hB₀ Lops _
      (le_trans ((by simpa using length_opsOfChoice_le (d := P.d) (w := 2 * m) (n := 2 * Λ) c)) (by rw [hLops]; ring_nf; exact le_rfl)) (by rw [dcnt_forms]) h0 U P.C₁ hU0 (by linarith)
      (hInv c) ?_
    rw [hxsκ]
    show P.C₁ + U * ((1 + y) ^ Lops - 1) ≤ 2 * P.C₁
    exact hy2
  have hsumV : evalV P A0 tt n h0 k =
      ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun b => tt b.1.1) 0 k n 0 := by
    unfold evalV
    refine Finset.sum_congr rfl fun LG _ => ?_
    rw [show typeProfiles LG h0 = layerProfiles LG (inputsF P Rr) from typeProfiles_layer LG _]
  have hW2 : (∏ j, jbr (k + latticePoint P.L (n j)) ^ (2 * (2 * Λ))) = W := by
    rw [hW, jbrProdAt, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring_nf
  have hnorm : W * ‖∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun b => tt b.1.1) 0 k n 0‖ ≤
      ((P.d : ℝ) + 1) ^ (2 * m * (2 * Λ)) * (T ^ Lops * ((2 * P.C₁) ^ (N + m) *
        (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) * (1 / 4 + 1 / 70)))))) := by
    have h1 : ((W : ℝ) : ℂ) * ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun b => tt b.1.1) 0 k n 0 =
        ∑ c : Fin (2 * m) → Fin (2 * Λ) → Option (Fin P.d),
          evalOps (evalV P A0 tt n) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 k := by
      rw [← hsumV, ← hW2]
      exact hid
    have hnm : W * ‖∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun b => tt b.1.1) 0 k n 0‖ =
        ‖((W : ℝ) : ℂ) * ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun b => tt b.1.1) 0 k n 0‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hWpos.le]
    rw [hnm, h1]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ => hterm c).trans ?_
    rw [Finset.sum_const, Finset.card_univ, card_choices, nsmul_eq_mul]
    push_cast
    simp only [B₀]
    exact le_rfl
  have e1 : P.δ ^ (8 * P.ν * (N : ℝ)) = P.δ ^ (6 * P.ν * (N : ℝ)) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have e2 : P.L ^ (-((m : ℝ) - 1) * (1 / 4 + 1 / 70)) =
      P.L ^ (-((m : ℝ) - 1) / 4) * P.L ^ (-((m : ℝ) - 1) / 70) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have hc4 : 2 * m * (2 * Λ) = 4 * m * Λ := by ring
  have hmain : W * ‖∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun b => tt b.1.1) 0 k n 0‖ ≤
      P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
    refine hnorm.trans ?_
    rw [e1, e2, hc4]
    have := mul_le_mul_of_nonneg_right hnum hrhs
    calc _ = (((P.d : ℝ) + 1) ^ (4 * m * Λ) * T ^ (8 * m * Λ) * (2 * P.C₁) ^ (N + m) *
          P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) / 70)) *
          (P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * (N : ℝ))) := by rw [hLops]; ring
      _ ≤ 1 * (P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * (N : ℝ))) := this
      _ = _ := one_mul _
  have := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hWpos.le)
  rw [← mul_assoc, inv_mul_cancel₀ hWpos.ne', one_mul] at this
  calc _ ≤ _ := this
    _ = _ := by ring

theorem couple_estimate_slice_of_typeGate_tt (P : WTParams) (hs : PieceSmall P) (hTG : TypeGateAt P)
    (hd : 1 ≤ P.d) (hlowP : LowProfileAt P) (htime : P.τstar = (P.D : ℝ) * P.δ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ)
    {p : ℕ} (hp : p < P.D) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ} (hN : N ≤ P.N (p + 1) ^ 4) {t s : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1))
    (A1 : Finset (LayeredGarden 2))
    (hmemA : ∀ LG ∈ A1, IsCanonC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1))
      (P.N (p + 1 - 1)) ∧ LG.garden.order = N ∧ ¬ IsRegularCouple LG.garden)
    (hTC : TwistClosed p A1)
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P Cφ p N ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N + 1) * P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) :
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
        (fun k => ∑ LG ∈ A1, KQstar P.L P.γ P.δ (inputsF P Rr) LG t s k) ≤
      ENNReal.ofReal (P.δ ^ (2 * P.ν * N) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) := by
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hδ0 := hs.delta_pos
  have hC₁ := hs.c1_ge
  set Λ := P.Lambda (p + 1) with hΛ
  have hrhs : 0 ≤ P.δ ^ (2 * P.ν * (N : ℝ)) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) :=
    mul_nonneg (Real.rpow_nonneg hδ0.le _) (Real.rpow_nonneg hL0.le _)
  by_cases hN0 : N = 0
  · subst hN0
    have hz : A1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro LG hLG
      have hm := hmemA LG hLG
      exact hm.2.2.2 (coherent_of_couple_order_zero LG hm.1.1 hm.2.2.1).1
    rw [hz]
    simp only [Finset.sum_empty]
    rw [SNorm_zero_function]
    exact bot_le
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have hcar : ∀ LG ∈ A1, Stage1Carries P p N LG := fun LG hLG =>
    stage1Carries_of_nonregular_couple P LG ⟨(hmemA LG hLG).1, (hmemA LG hLG).2.1, (hmemA LG hLG).2.2.1⟩
      (hmemA LG hLG).2.2.2
  have hplain : ∀ LG ∈ A1, LG.garden.IsPlain := fun LG h => (hmemA LG h).1.1.1
  have hlay : ∀ LG ∈ A1, ∀ a, LG.layer a ≤ p := fun LG h => Canon.layer_le_of_isCanonC (hmemA LG h).1
  have hcard : ∀ LG ∈ A1, (inputLeaves LG.garden).card = N + 1 := by
    intro LG hLG
    have h1 := twice_card_inputLeaves LG.garden (hplain LG hLG)
    have h2 : LG.garden.order = N := (hmemA LG hLG).2.2.1
    omega
  have hΛ40 : 40 * P.d ≤ Λ := forty_dim_le_Lambda P hd (show p + 1 ≤ P.D by omega)
  set M : ℕ := (N + 2) / 2 with hMdef
  have hM1 : 1 ≤ M := by omega
  set Lops : ℕ := 8 * Λ with hLops
  have hLops1 : 1 ≤ Lops := by omega
  set U : ℝ := Cφ + 1 with hUdef
  have hU0 : 0 ≤ U := by linarith
  set y : ℝ := P.C₁ / (2 * max U P.C₁ * Lops) with hy
  obtain ⟨hy1, hy2⟩ := step_params (C₁ := P.C₁) (U := U) (by linarith) hU0 Lops hLops1
  have hLopsR : (0 : ℝ) < Lops := by exact_mod_cast hLops1
  have hymax : 0 < max U P.C₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hypos : 0 < y := by rw [hy]; positivity
  set κ : ℝ := (2 * (P.d : ℝ)) ^ (40 * P.d + 4 * Λ) with hκ
  have hd1 : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hκ1 : 1 ≤ κ := one_le_pow₀ (by linarith)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set xs : ℝ := y / κ with hxs
  have hxspos : 0 < xs := by positivity
  set lam : ℝ := xs / M with hlam
  have hlampos : 0 < lam := by positivity
  have hxsκ : xs * κ = y := by rw [hxs]; field_simp
  have hinp := all_stage_input_bounds P hd hL1 hδ0.le htime hlowP hC₁ hCφ hφ hp Rr hRr
  let h0 : TProf P.d 2 := fun q _ _ => inputsF P Rr q
  let σ : Fin 2 → ℝ := fun j => (((![1, -1] : Fin 2 → ℤˣ) j : ℤ) : ℝ)
  have hctx : EvalCtx P A1 p M σ :=
    { hd := hd, hL := hL1, hM1 := hM1, plain := hplain, lay := hlay
      card := fun LG hLG => by rw [hcard LG hLG]; omega
      sig := fun LG hLG j0 => by
        have hs2 : LG.garden.sig = ![1, -1] := (hmemA LG hLG).1.1.2
        rw [nodeSign_root_eq, hs2] }
  have hσ2 : ∀ j, σ j ^ 2 = 1 := fun j => units_sq_real _
  have hInvG : ∀ os : List (TOp P.d 2), dcnt os ≤ 4 * Λ → (∀ j j', fcnt j j' os ≤ 4 * Λ) →
      Inv p (40 * P.d) (40 * P.d) os U P.C₁ h0 := by
    intro os hdc hfc q hq j j'
    obtain ⟨hc1, hc2, hc3⟩ := hinp q hq
    refine ⟨hc1.of_le (by exact_mod_cast (show 40 * P.d + dcnt os ≤ 40 * P.d + 4 * Λ by omega)), ?_, hc3⟩
    exact SNormR_mono_bound (by omega) (by have := hfc j j'; omega) _ hc1 U hU0 hc2
  -- smoothness of the sum
  have hfV : (fun k => ∑ LG ∈ A1, KQstar P.L P.γ P.δ (inputsF P Rr) LG t s k) =
      evalV P A1 (fun j => if j = 0 then t else s) (fun _ => 0) h0 := by
    funext k
    unfold evalV
    refine Finset.sum_congr rfl fun LG _ => ?_
    show _ = kernelLeaves P.L P.γ P.δ LG (typeProfiles LG h0) (fun b => if b.1.1 = 0 then t else s) 0 k
      (fun _ => 0) 0
    rw [show typeProfiles LG h0 = layerProfiles LG (inputsF P Rr) from typeProfiles_layer LG _,
      kernelLeaves_layerProfiles]
    rfl
  have hf : ContDiff ℝ (4 * Λ : ℕ) (evalV P A1 (fun j => if j = 0 then t else s) (fun _ => 0) h0) := by
    let i0 : Fin P.d := ⟨0, by omega⟩
    have hI := hInvG (List.replicate (4 * Λ) (TOp.der (w := 2) i0)) (by simp [dcnt, TOp.dc])
      (fun j j' => by simp [fcnt, TOp.fc])
    have := evalV_contDiff hctx (fun j => if j = 0 then t else s) (fun _ => 0)
      (AdmI_of_Inv hd hU0 (by linarith) hI)
    simpa [dcnt, TOp.dc] using this
  rw [hfV]
  apply SNorm_le_of_word_enorm_bounds _ hf
  intro word hw x
  have hadm : ∀ c : Fin (2 * Λ) → Option (Fin P.d),
      Inv p (40 * P.d) (40 * P.d) (word.reverse.map TOp.der ++ (opsOfChoice0 (0 : Fin 2) c).map
        fun f => TOp.form f.1 f.2) U P.C₁ h0 := by
    intro c
    refine hInvG _ ?_ ?_
    · rw [dcnt_append, dcnt_ders, dcnt_forms]
      simp only [List.length_reverse, Nat.add_zero]
      omega
    · intro j j'
      rw [fcnt_append, fcnt_ders, zero_add]
      have := fcnt_opsOfChoice0 (d := P.d) (0 : Fin 2) c j j'
      omega
  have hid := couple_weight_identity hctx (0 : Fin 2) (hσ2 0) (fun j => if j = 0 then t else s)
    (fun _ => 0) rfl lam hlampos.ne' (2 * Λ) h0 word x
    (fun c => AdmI_of_Inv hd hU0 (by linarith) (hadm c))
  set T : ℝ := coupleT P Cφ p N with hT
  have hTeq : (2 * (M : ℝ) + 1) / |lam| = T := by
    rw [abs_of_pos hlampos, hlam, hxs, hT, coupleT, hy]
    push_cast [hLops]
    field_simp
    rw [← hMdef, ← hUdef, ← hΛ, hκ]
    ring
  have hT1 : 1 ≤ T := by
    rw [← hTeq, abs_of_pos hlampos, hlam, hxs, hy]
    have h2 : 1 ≤ (2 * (M : ℝ) + 1) := by linarith
    have h3 : 1 ≤ (2 * (M : ℝ) + 1) * M * κ := by
      have := one_le_mul_of_one_le_of_one_le h2 hMR
      exact one_le_mul_of_one_le_of_one_le this hκ1
    have e : (2 * (M : ℝ) + 1) / (P.C₁ / (2 * max U P.C₁ * Lops) / κ / M) =
        (2 * (M : ℝ) + 1) * M * κ * (2 * max U P.C₁ * Lops / P.C₁) := by
      field_simp
    rw [e]
    refine one_le_mul_of_one_le_of_one_le h3 ?_
    rw [le_div_iff₀ (by linarith)]
    have hLR : (1 : ℝ) ≤ Lops := by exact_mod_cast hLops1
    have := le_max_right U P.C₁
    nlinarith
  let B₀ : NNReal := ⟨2 * P.C₁, by linarith⟩
  have hB₀ : 0 < (B₀ : ℝ) := by show 0 < 2 * P.C₁; linarith
  have hxM : ∀ m' ∈ Finset.range (2 * M + 1), |lam * ((m' : ℝ) - M)| ≤ xs := by
    intro m' hm'
    have hm'2 : m' ≤ 2 * M := by have := Finset.mem_range.mp hm'; omega
    rw [abs_mul, abs_of_pos hlampos]
    have : |(m' : ℝ) - M| ≤ M := by
      rw [abs_le]
      have : (m' : ℝ) ≤ 2 * M := by exact_mod_cast hm'2
      constructor <;> linarith [(Nat.cast_nonneg m' : (0 : ℝ) ≤ m')]
    calc lam * |(m' : ℝ) - M| ≤ lam * M := mul_le_mul_of_nonneg_left this hlampos.le
      _ = xs := by rw [hlam]; field_simp
  have hterm : ∀ c : Fin (2 * Λ) → Option (Fin P.d),
      ‖evalOps (evalV P A1 (fun j => if j = 0 then t else s) (fun _ => 0)) M lam
          (word.reverse.map TOp.der ++ (opsOfChoice0 (0 : Fin 2) c).map fun f => TOp.form f.1 f.2) h0 x‖ ≤
        T ^ Lops * (((B₀ : ℝ)) ^ (N + 1) *
          (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-(((1 : ℕ) : ℝ) - 1) * (1 / 4 + 1 / 70))))) := by
    intro c
    refine evalOps_typeGate_bound (R := 1) P hs hTG hd hp le_rfl
      (by omega) hN1 hN A1 hcar hTC (fun j => if j = 0 then t else s) (fun j => by split_ifs; exact ht; exact hts)
      (fun _ => 0) hplain x M lam T hT1 hTeq.le xs hxspos.le hxM (4 * Λ) B₀ hB₀ Lops _ ?_ ?_ h0 U P.C₁ hU0
      (by linarith) (hadm c) ?_
    · rw [List.length_append, List.length_map, List.length_map, List.length_reverse]
      have := length_opsOfChoice0_le (d := P.d) (0 : Fin 2) c
      omega
    · rw [dcnt_append, dcnt_ders, dcnt_forms]
      simp only [List.length_reverse, Nat.add_zero]
      omega
    · rw [hxsκ]
      show P.C₁ + U * ((1 + y) ^ Lops - 1) ≤ 2 * P.C₁
      exact hy2
  have hnorm : ‖((jbr x ^ (4 * Λ) : ℝ) : ℂ) * wordD word (evalV P A1 (fun j => if j = 0 then t else s)
        (fun _ => 0) h0) x‖ ≤
      ((P.d : ℝ) + 1) ^ (2 * Λ) * (T ^ Lops * ((2 * P.C₁) ^ (N + 1) *
        (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-(((1 : ℕ) : ℝ) - 1) * (1 / 4 + 1 / 70)))))) := by
    have e4 : 4 * Λ = 2 * (2 * Λ) := by ring
    rw [e4, hid]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ => hterm c).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [Fintype.card_option, B₀]
    exact le_rfl
  rw [← ofReal_norm]
  refine le_trans (ENNReal.ofReal_le_ofReal hnorm) (ENNReal.ofReal_le_ofReal ?_)
  simp only [Nat.cast_one, sub_self, neg_zero, zero_mul, Real.rpow_zero, mul_one]
  have e1 : P.δ ^ (8 * P.ν * (N : ℝ)) = P.δ ^ (6 * P.ν * (N : ℝ)) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  rw [e1]
  have := mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hδ0.le (2 * P.ν * (N : ℝ)))
  calc _ = ((P.d : ℝ) + 1) ^ (2 * Λ) * T ^ (8 * Λ) * (2 * P.C₁) ^ (N + 1) * P.δ ^ (6 * P.ν * (N : ℝ)) *
        P.L ^ (-P.η ^ 7) * P.δ ^ (2 * P.ν * (N : ℝ)) := by rw [hLops]; ring
    _ ≤ _ := this
    _ = _ := by ring

end

section
-- source: FlowerTop/Port/P7/Slices.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
/-- **Irreducible block, one slice** (`m = 2, 3`): the sum of the six-tree kernels over the canonical truncated
gardens of fixed order and fixed top-order vector. -/
theorem garden_slice_kernelKgen (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) {m : ℕ} (hm2 : 2 ≤ m) (hmmax : m ≤ 10 * P.R (p + 1))
    (ζ : Fin (2 * m) → ℤˣ) (hζ : IsBalancedSig ζ) (n : Fin (2 * m) → (Fin P.d → ℤ)) (k : Mom P.d) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) (tt : Fin (2 * m) → ℝ) (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (v : Fin (2 * m) → ℕ)
    (hnum : ((P.d : ℝ) + 1) ^ (4 * m * P.Lambda (p + 1)) * gardenT P G.Cφ p m N ^ (8 * m * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N + m) * P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) / 70) ≤ 1) :
    ‖∑ LG ∈ (gardenSet P p N m ζ).filter (fun LG => ∀ j, LG.topOrder p j = v j),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LG (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * N) := by
  have hmem : ∀ LG ∈ (gardenSet P p N m ζ).filter (fun LG => ∀ j, LG.topOrder p j = v j),
      IsCanonGC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
        LG.garden.sig = ζ ∧ LG.garden.order = N := fun LG h =>
    (Canon.finite_truncSum_support P (p + 1) N (2 * m) ζ).mem_toFinset.mp (Finset.mem_filter.1 h).1
  have h := garden_estimate_slice_of_typeGate_tt P G.hs G.hTG G.hd
    G.hlowP G.htime G.hCφ G.hφ hp Rr hRr hm2 hmmax ζ hζ n k hN tt htt _ hmem
    (twistClosed_topFilter p _ (twistClosed_gardenSet P G.hd hp hm2 ζ hN) v) hnum
  refine le_of_eq_of_le ?_ h
  congr 1
  refine Finset.sum_congr rfl fun LG hLG => ?_
  exact kernelKgen_eq_kernelLeaves P.L P.γ P.δ (inputsF P Rr) LG (hmem LG hLG).1.1 tt k n

end

section
-- source: FlowerTop/Port/P7/Level0.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
/-- **Bound for the irreducible width-six piece.** -/
theorem piece0_norm_le (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (kind : TreeKind) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hmmax : 3 ≤ 10 * P.R (p + 1)) (n : Fin (2 * 3) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * 3) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hnum : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 3 * P.Lambda (p + 1)) *
      gardenT P G.Cφ p 3 N' ^ (8 * 3 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 3) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) * P.L ^ (-((3 : ℕ) - 1 : ℝ) / 70) ≤ 1) :
    ‖∑ᶠ y ∈ Irr6 P p N kind,
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      ∑ d ∈ (Irr6_finite P p N kind).toFinset.image (compData p),
        jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-(((3 : ℕ) : ℝ) - 1) / 4) *
          P.δ ^ (2 * P.ν * d.1) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (Irr6_finite P p N kind)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Irr6_finite P p N kind).toFinset)
    (t := (Irr6_finite P p N kind).toFinset.image (compData p)) (g := compData p)
    (fun y hy => Finset.mem_image_of_mem _ hy)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hd
  have hy0' := (Irr6_finite P p N kind).mem_toFinset.1 hy0
  have hcond := hy0'.1.2
  have hord : (compData p y0).1 + 2 = N := hcond.2.2.2.1
  have hvk : VecKindOK (P.N (p + 1)) kind (compData p y0).2 := hcond.2.2.2.2
  have hvle : ∀ i, (compData p y0).2 i ≤ P.N (p + 1) := fun i => hvk.le i
  rw [Irr6_slice_eq P p N kind _ hord hvk hvle]
  have hbal : IsBalancedSig (fun i : Fin (2 * 3) => childSig i) := by
    have hpl : y0.garden.IsPlain := hy0'.1.2.1
    have := Comb.balanced_of_plain hpl
    have hs : y0.garden.sig = fun i => childSig i := funext hy0'.1.1
    rw [← hs]; exact this
  have hle : (compData p y0).1 ≤ P.N (p + 1) ^ 4 := by
    have : (compData p y0).1 ≤ N := by omega
    exact this.trans hN
  have := garden_slice_kernelKgen C₀ P G hp Rr hRr (m := 3) (by norm_num) hmmax _ hbal n k hle tt htt
    (compData p y0).2 (hnum _ hle)
  simpa using this

end

section
-- source: FlowerTop/Port/P7/Level1Est.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
/-- **Slice bound for the irreducible first component** of a first-level piece (`m = 2, 3`). -/
theorem Acomp1_slice_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) {b m : ℕ}
    (hm2 : 2 ≤ m) (hmmax : m ≤ 10 * P.R (p + 1)) (σ : Fin (2 * m) ⊕ Fin b ≃ Fin (2 * 3)) (i0 : Fin (2 * m))
    (n : Fin (2 * m) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * m) → ℝ) (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (d : ℕ × (Fin (2 * m) → ℕ)) (hd : d.1 ≤ N) (hv : ∀ i, d.2 i ≤ P.N (p + 1))
    (hnum : ((P.d : ℝ) + 1) ^ (4 * m * P.Lambda (p + 1)) * gardenT P G.Cφ p m d.1 ^ (8 * m * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (d.1 + m) * P.δ ^ (6 * P.ν * d.1) * P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) / 70) ≤ 1) :
    ‖∑ LA ∈ (Acomp1_finite P p N σ i0).toFinset.filter (fun LA => compData p LA = d),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LA (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      jbrProdAt P.L k n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * d.1) := by
  rw [Acomp1_slice_eq P p N σ i0 hm2 d hd hv]
  by_cases hbal : IsBalancedSig (fun i => childSig (σ (.inl i)))
  · exact garden_slice_kernelKgen C₀ P G hp Rr hRr hm2 hmmax _ hbal n k (hd.trans hN) tt htt d.2 hnum
  · -- the slice is empty (plain gardens have balanced signatures)
    have hemp : (gardenSet P p d.1 m (fun i => childSig (σ (.inl i)))).filter
        (fun LG => ∀ j, LG.topOrder p j = d.2 j) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun LG hLG => hbal ?_
      have h1 := (Canon.finite_truncSum_support P (p + 1) d.1 (2 * m)
        (fun i => childSig (σ (.inl i)))).mem_toFinset.mp (Finset.mem_filter.1 hLG).1
      have hpl : LG.garden.IsPlain := h1.1.1
      have := Comb.balanced_of_plain hpl
      rw [← h1.2.2.1]
      exact this
    rw [hemp, Finset.sum_empty, norm_zero]
    have hL0 : 0 < P.L := by linarith [G.hs.L_ge]
    have hJ : 0 < jbrProdAt P.L k n := Finset.prod_pos fun j _ => WaveTurbulence.Induct.jbr_pos _
    have hδ : 0 < P.δ := G.hs.delta_pos
    positivity

end

section
-- source: FlowerTop/Port/P7/Level1Couple.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
/-- Nonregular couples of a top-order slice, pointwise (from LG-SPINE's couple estimate). -/
theorem couple_nonreg_slice_pointwise (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N' : ℕ}
    (hN' : N' ≤ P.N (p + 1) ^ 4) (k : Mom P.d) {t s : ℝ} (ht : t ∈ Set.Icc (p : ℝ) (p + 1))
    (hts : s ∈ Set.Icc (p : ℝ) (p + 1)) (v : Fin 2 → ℕ)
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) :
    ‖∑ LG ∈ (coupleSet P p N').filter (fun LG => ∀ j, LG.topOrder p j = v j),
        KQstar P.L P.γ P.δ (inputsF P Rr) LG t s k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
        (P.δ ^ (2 * P.ν * N') * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) := by
  have hmemA : ∀ LG ∈ (coupleSet P p N').filter (fun LG => ∀ j, LG.topOrder p j = v j),
      IsCanonC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
        LG.garden.order = N' ∧ ¬ IsRegularCouple LG.garden := by
    intro LG hLG
    obtain ⟨h1, -⟩ := Finset.mem_filter.1 hLG
    simp only [coupleSet, coupleCarrier, Finset.mem_filter, Set.Finite.mem_toFinset] at h1
    exact ⟨h1.1.1, h1.1.2.1, h1.1.2.2, h1.2⟩
  have hSN := couple_estimate_slice_of_typeGate_tt P G.hs G.hTG G.hd
    G.hlowP G.htime G.hCφ G.hφ hp Rr hRr hR1 hN' ht hts _ hmemA
    (twistClosed_topFilter p _ (twistClosed_coupleSet P G.hd hp hN') v) hnum
  have hδ : 0 < P.δ := G.hs.delta_pos
  have hL : 0 < P.L := by linarith [G.hs.L_ge]
  have hC : 0 ≤ P.δ ^ (2 * P.ν * (N' : ℝ)) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) :=
    mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hL.le _)
  set C : ℝ := P.δ ^ (2 * P.ν * (N' : ℝ)) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) with hCdef
  have hnr : ‖(fun k => ∑ LG ∈ (coupleSet P p N').filter (fun LG => ∀ j, LG.topOrder p j = v j),
      KQstar P.L P.γ P.δ (inputsF P Rr) LG t s k) k‖ ≤ jbr k ^ (-((4 * P.Lambda (p + 1) : ℕ) : ℝ)) * C :=
    norm_le_of_SNorm_le' (A := 4 * P.Lambda (p + 1)) (B := 4 * P.Lambda (p + 1)) _ C hC hSN k
  have hcast : ((4 * P.Lambda (p + 1) : ℕ) : ℝ) = 4 * (P.Lambda (p + 1) : ℝ) := by norm_num
  rw [hcast] at hnr
  exact hnr

open scoped Classical in
/-- A finset of canonical truncated couples of one order and one top-order vector: pointwise bound of the sum of
the couple kernels (nonregular part by LG-SPINE, regular part by the interface). -/
theorem couple_family_pointwise (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N' : ℕ}
    (hN' : N' ≤ P.N (p + 1) ^ 4) (k : Mom P.d) {t s : ℝ} (ht : t ∈ Set.Icc (p : ℝ) (p + 1))
    (hts : s ∈ Set.Icc (p : ℝ) (p + 1)) (v : Fin 2 → ℕ)
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg)
    (S : Finset (LayeredGarden 2))
    (hS : ∀ LB ∈ S, (IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LB.garden.order = N') ∧ ∀ j, LB.topOrder p j = v j)
    (hSfull : ∀ LB, ((IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LB.garden.order = N') ∧ ∀ j, LB.topOrder p j = v j) → LB ∈ S) :
    ‖∑ LB ∈ S, KQstar P.L P.γ P.δ (inputsF P Rr) LB t s k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
        (P.δ ^ (2 * P.ν * N') * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
          Creg N' * P.δ ^ ((N' : ℝ) / 4)) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun LB => IsRegularCouple LB.garden)]
  refine (norm_add_le _ _).trans ?_
  have hreg' := hreg N' hN' t s ht hts k (S.filter fun LB => IsRegularCouple LB.garden) (fun LB hLB => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hLB
    exact ⟨(hS LB h1).1.1, (hS LB h1).1.2.2, h2⟩)
  have hA1 : S.filter (fun LB => ¬ IsRegularCouple LB.garden) =
      (coupleSet P p N').filter (fun LG => ∀ j, LG.topOrder p j = v j) := by
    ext LB
    simp only [Finset.mem_filter, coupleSet, coupleCarrier, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨⟨hc, htr, hord⟩, hvec⟩ := hS LB h1
      exact ⟨⟨⟨hc, htr, hord⟩, h2⟩, hvec⟩
    · rintro ⟨⟨⟨hc, htr, hord⟩, h2⟩, hvec⟩
      exact ⟨hSfull LB ⟨⟨hc, htr, hord⟩, hvec⟩, h2⟩
  have hnr := couple_nonreg_slice_pointwise C₀ P G hp Rr hRr hR1 hN' k ht hts v hnum
  rw [← hA1] at hnr
  calc _ ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * Creg N' * P.δ ^ ((N' : ℝ) / 4) +
        jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * (P.δ ^ (2 * P.ν * N') *
          P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) := add_le_add hreg' hnr
    _ = _ := by ring

open scoped Classical in
/-- **Couple component of a first-level piece: slice bound** (root labels `nB`, base `k`, caps `t`). -/
theorem couple_slice_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) {a : ℕ} (σ : Fin a ⊕ Fin 2 ≃ Fin (2 * 3))
    (hs2 : (fun i => childSig (σ (.inr i))) = ![1, -1]) (nB : Fin 2 → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin 2 → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (e : ℕ × (Fin 2 → ℕ)) (he : e.1 ≤ N) (hv : ∀ i, e.2 i ≤ P.N (p + 1))
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P G.Cφ p e.1 ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (e.1 + 1) * P.δ ^ (6 * P.ν * e.1) * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
      if nB 0 = nB 1 then
        jbr (k + latticePoint P.L (nB 0)) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
          (P.δ ^ (2 * P.ν * e.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
            Creg e.1 * P.δ ^ ((e.1 : ℝ) / 4))
      else 0 := by
  have hmem := Bcomp1_couple_mem_iff P p N σ hs2 e he hv
  have hplain : ∀ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
      LB.garden.IsPlain := fun LB h => ((hmem LB).1 h).1.1.1.1
  have hsig : ∀ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
      LB.garden.sig = ![1, -1] := fun LB h => ((hmem LB).1 h).1.1.1.2
  by_cases hn : nB 0 = nB 1
  · rw [if_pos hn]
    have hnB : nB = fun _ => nB 0 := by
      funext i; fin_cases i
      · rfl
      · exact hn.symm
    have hK : ∀ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0 =
          KQstar P.L P.γ P.δ (inputsF P Rr) LB (tt 0) (tt 1) (k + latticePoint P.L (nB 0)) := by
      intro LB hLB
      rw [hnB, kernelKgen_shift P.L P.γ P.δ (inputsF P Rr) LB (hplain LB hLB) (fun x => tt x.1.1) k (nB 0),
        kernelKgen_eq_KQstar P.L P.γ P.δ (inputsF P Rr) LB (hplain LB hLB)]
    rw [Finset.sum_congr rfl hK]
    exact couple_family_pointwise C₀ P G hp Rr hRr hR1 (he.trans hN) _ (htt 0) (htt 1) e.2 hnum Creg hreg _
      (fun LB h => (hmem LB).1 h) (fun LB h => (hmem LB).2 h)
  · rw [if_neg hn]
    rw [Finset.sum_eq_zero fun LB hLB => couple_kernel_offdiag P.L P.γ P.δ _ LB (hplain LB hLB)
      (hsig LB hLB) (fun x => tt x.1.1) k nB hn, norm_zero]

end

section
-- source: FlowerTop/Port/P7/Piece42.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
/-- **Pieces with an irreducible width-four first block and a couple second block.** -/
theorem piece42_norm_le (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (kind : TreeKind) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hmmax : 2 ≤ 10 * P.R (p + 1)) (hR1 : 1 ≤ P.R (p + 1)) (σ : Fin (2 * 2) ⊕ Fin 2 ≃ Fin (2 * 3))
    (i0 : Fin (2 * 2)) (hs2 : (fun i => childSig (σ (.inr i))) = ![1, -1])
    (n : Fin (2 * 3) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * 3) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hnumA : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 2 * P.Lambda (p + 1)) *
      gardenT P G.Cφ p 2 N' ^ (8 * 2 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 2) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) * P.L ^ (-((2 : ℕ) - 1 : ℝ) / 70) ≤ 1)
    (hnumB : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
      coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧
        MinimalAt y.garden (σ (.inl i0)) (Finset.univ.image fun i => σ (.inl i))},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      ∑ d ∈ (Acomp1_finite P p N σ i0).toFinset.image (compData p),
        ∑ e ∈ (Bcomp1_finite P p N (a := 2 * 2) σ).toFinset.image (compData p),
          if Joint1 P p N kind σ d e then
            (jbrProdAt P.L k (fun i => n (σ (.inl i))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
                P.L ^ (-(((2 : ℕ) : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * d.1)) *
              (if n (σ (.inr 0)) = n (σ (.inr 1)) then
                jbr (k + latticePoint P.L (n (σ (.inr 0)))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
                  (P.δ ^ (2 * P.ν * e.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
                    Creg e.1 * P.δ ^ ((e.1 : ℝ) / 4))
              else 0)
          else 0 := by
  refine piece1_norm_le P (inputsF P Rr) p N kind σ i0 tt k n hF
    (fun d => d.1 ≤ N ∧ ∀ i, d.2 i ≤ P.N (p + 1)) (fun e => e.1 ≤ N ∧ ∀ i, e.2 i ≤ P.N (p + 1))
    (fun d e h => joint1_allowed P p N kind σ d e h) _ _ ?_ ?_
  · intro d _ ⟨hd, hv⟩
    exact Acomp1_slice_bound C₀ P G hp hN Rr hRr (m := 2) (by norm_num) hmmax σ i0 _ k (fun i => tt (σ (.inl i))) (fun i => htt _) d hd hv (hnumA d.1 (hd.trans hN))
  · intro e _ ⟨he, hv⟩
    exact couple_slice_bound C₀ P G hp hN Rr hRr hR1 σ hs2 _ k (fun i => tt (σ (.inr i))) (fun i => htt _) e he hv (hnumB e.1 (he.trans hN)) Creg hreg

end

section
-- source: FlowerTop/Port/P7/Level2.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
/-- **Slice bound for a finite set of canonical truncated couples with root labels `nB`** (diagonal: pointwise at
`k + nB 0 / L`; off the diagonal: `0`). -/
theorem couple_set_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p : ℕ} (hp : p < P.D)
    (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1)) {N' : ℕ}
    (hN' : N' ≤ P.N (p + 1) ^ 4) (nB : Fin 2 → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin 2 → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (v : Fin 2 → ℕ)
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) (S : Finset (LayeredGarden 2))
    (hS : ∀ LB ∈ S, (IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LB.garden.order = N') ∧ ∀ j, LB.topOrder p j = v j)
    (hSfull : ∀ LB, ((IsCanonC (p + 1) LB ∧ LB.IsTrunc (p + 1 - 1) (P.N (p + 1)) (P.N (p + 1 - 1)) ∧
      LB.garden.order = N') ∧ ∀ j, LB.topOrder p j = v j) → LB ∈ S) :
    ‖∑ LB ∈ S, kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
      if nB 0 = nB 1 then
        jbr (k + latticePoint P.L (nB 0)) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
          (P.δ ^ (2 * P.ν * N') * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
            Creg N' * P.δ ^ ((N' : ℝ) / 4))
      else 0 := by
  have hplain : ∀ LB ∈ S, LB.garden.IsPlain := fun LB h => (hS LB h).1.1.1.1
  have hsig : ∀ LB ∈ S, LB.garden.sig = ![1, -1] := fun LB h => (hS LB h).1.1.1.2
  by_cases hn : nB 0 = nB 1
  · rw [if_pos hn]
    have hnB : nB = fun _ => nB 0 := by
      funext i; fin_cases i
      · rfl
      · exact hn.symm
    have hK : ∀ LB ∈ S,
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0 =
          KQstar P.L P.γ P.δ (inputsF P Rr) LB (tt 0) (tt 1) (k + latticePoint P.L (nB 0)) := by
      intro LB hLB
      rw [hnB, kernelKgen_shift P.L P.γ P.δ (inputsF P Rr) LB (hplain LB hLB) (fun x => tt x.1.1) k (nB 0),
        kernelKgen_eq_KQstar P.L P.γ P.δ (inputsF P Rr) LB (hplain LB hLB)]
    rw [Finset.sum_congr rfl hK]
    exact couple_family_pointwise C₀ P G hp Rr hRr hR1 hN' _ (htt 0) (htt 1) v hnum Creg hreg S hS hSfull
  · rw [if_neg hn]
    rw [Finset.sum_eq_zero fun LB hLB => couple_kernel_offdiag P.L P.γ P.δ _ LB (hplain LB hLB)
      (hsig LB hLB) (fun x => tt x.1.1) k nB hn, norm_zero]

open scoped Classical in
/-- **A second-level piece: explicit bound.** -/
theorem piece2_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p) (hR1 : 1 ≤ P.R (p + 1))
    (τ : Fin 2 ⊕ Fin 2 ≃ Fin 4) (ζ : Fin 4 → ℤˣ) (hC : (fun i => ζ (τ (.inl i))) = ![1, -1])
    (hD : (fun i => ζ (τ (.inr i))) = ![1, -1]) (e : ℕ × (Fin 4 → ℕ)) (he : e.1 ≤ N)
    (hev : ∀ i, e.2 i ≤ P.N (p + 1)) (nB : Fin 4 → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin 4 → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hnumC : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
      coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ᶠ LB ∈ {LB : LayeredGarden 4 | LB.garden.sig = ζ ∧ (CompCond P p LB ∧ compData p LB = e) ∧
        MinimalAt LB.garden (τ (.inl 0)) (Finset.univ.image fun i => τ (.inl i))},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
      ∑ c ∈ (Ccomp2_finite P p N (fun i => ζ (τ (.inl i)))).toFinset.image (compData p),
        ∑ c' ∈ (Dcomp2_finite P p N (fun i => ζ (τ (.inr i)))).toFinset.image (compData p),
          if Joint2 τ e c c' then
            (if nB (τ (.inl 0)) = nB (τ (.inl 1)) then
              jbr (k + latticePoint P.L (nB (τ (.inl 0)))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
                (P.δ ^ (2 * P.ν * c.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
                  Creg c.1 * P.δ ^ ((c.1 : ℝ) / 4)) else 0) *
            (if nB (τ (.inr 0)) = nB (τ (.inr 1)) then
              jbr (k + latticePoint P.L (nB (τ (.inr 0)))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
                (P.δ ^ (2 * P.ν * c'.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
                  Creg c'.1 * P.δ ^ ((c'.1 : ℝ) / 4)) else 0)
          else 0 := by
  refine piece2_norm_le P (inputsF P Rr) p N τ ζ e he tt k nB hF
    (fun c => c.1 ≤ N ∧ ∀ i, c.2 i ≤ P.N (p + 1)) (fun c => c.1 ≤ N ∧ ∀ i, c.2 i ≤ P.N (p + 1))
    (fun c c' h => joint2_allowed P p N τ e he hev c c' h) _ _ ?_ ?_
  · intro c _ ⟨hc, hv⟩
    exact couple_set_bound C₀ P G hp Rr hRr hR1 (hc.trans hN) (fun i => nB (τ (.inl i))) k (fun i => tt (τ (.inl i))) (fun i => htt _) c.2
      (hnumC c.1 (hc.trans hN)) Creg hreg _
      (fun LB h => (Ccomp2_mem_iff P p N ζ τ hC c hc hv LB).1 h)
      (fun LB h => (Ccomp2_mem_iff P p N ζ τ hC c hc hv LB).2 h)
  · intro c _ ⟨hc, hv⟩
    exact couple_set_bound C₀ P G hp Rr hRr hR1 (hc.trans hN) (fun i => nB (τ (.inr i))) k (fun i => tt (τ (.inr i))) (fun i => htt _) c.2
      (hnumC c.1 (hc.trans hN)) Creg hreg _
      (fun LB h => (Dcomp2_mem_iff P p N ζ τ hD c hc hv LB).1 h)
      (fun LB h => (Dcomp2_mem_iff P p N ζ τ hD c hc hv LB).2 h)

end

section
-- source: FlowerTop/Port/P7/Level2b.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
/-- **Plain width-four second component of a first-level piece: slice bound.** -/
theorem Bplain4_slice_bound (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) (hmmax : 2 ≤ 10 * P.R (p + 1)) {a : ℕ} (σ : Fin a ⊕ Fin (2 * 2) ≃ Fin (2 * 3))
    (hs4 : (fun i => childSig (σ (.inr i))) = ![1, -1, 1, -1]) (e : ℕ × (Fin (2 * 2) → ℕ)) (he : e.1 ≤ N)
    (hev : ∀ i, e.2 i ≤ P.N (p + 1)) (nB : Fin (2 * 2) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * 2) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hnumA : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 2 * P.Lambda (p + 1)) *
      gardenT P G.Cφ p 2 N' ^ (8 * 2 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 2) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) * P.L ^ (-((2 : ℕ) - 1 : ℝ) / 70) ≤ 1)
    (hnumC : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
      coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ LB ∈ (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e),
        kernelKgen P.L P.γ P.δ (inputsF P Rr) LB (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k nB 0‖ ≤
      PieceBound2 P p N τ1 (fun i => childSig (σ (.inr i))) e Creg nB k +
        PieceBound2 P p N τ2 (fun i => childSig (σ (.inr i))) e Creg nB k +
        jbrProdAt P.L k nB ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-(((2 : ℕ) : ℝ) - 1) / 4) *
          P.δ ^ (2 * P.ν * e.1) := by
  set T := (Bcomp1_finite P p N (a := a) σ).toFinset.filter (fun LB => compData p LB = e) with hT
  have hTpl : ∀ LB ∈ T, LB.garden.IsPlain ∧ LB.garden.sig = ![1, -1, 1, -1] := by
    intro LB hLB
    simp only [hT, Finset.mem_filter, Set.Finite.mem_toFinset, Bcomp1, Set.mem_ofPred_eq] at hLB
    exact ⟨hLB.1.2.1.1, hLB.1.1.trans hs4⟩
  rw [sum_partition4 T hTpl]
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · -- `τ1`
    rw [← finsum_mem_coe_finset, Bplain4_piece_set_eq P p N σ e he τ1 {0, 1} τ1_image.symm τ1_inl0]
    exact piece2_bound C₀ P G hp hN Rr hRr hR1 τ1 (fun i => childSig (σ (.inr i)))
      (by funext i; fin_cases i <;> simp [τ1, congrFun hs4])
      (by funext i; fin_cases i <;> simp [τ1, congrFun hs4]) e he hev nB k tt htt hF hnumC Creg hreg
  · -- `τ2`
    rw [← finsum_mem_coe_finset, Bplain4_piece_set_eq P p N σ e he τ2 {0, 3} τ2_image.symm τ2_inl0]
    exact piece2_bound C₀ P G hp hN Rr hRr hR1 τ2 (fun i => childSig (σ (.inr i)))
      (by funext i; fin_cases i <;> simp [τ2, congrFun hs4])
      (by funext i; fin_cases i <;> simp [τ2, congrFun hs4]) e he hev nB k tt htt hF hnumC Creg hreg
  · -- irreducible
    rw [Bplain4_irr_eq P p N σ e he hev]
    have hbal : IsBalancedSig (fun i : Fin (2 * 2) => childSig (σ (.inr i))) := by
      rw [hs4]; simp [IsBalancedSig, Fin.sum_univ_four]
    exact garden_slice_kernelKgen C₀ P G hp Rr hRr (m := 2) (by norm_num) hmmax _ hbal nB k (he.trans hN) tt htt e.2
      (hnumA e.1 (he.trans hN))

end

section
-- source: FlowerTop/Port/P7/Piece24.lean
open WaveTurbulence.FlowerP7
open TTree Finset LGSpine

open scoped Classical in
/-- **Pieces with a couple first block and a plain width-four second block.** -/
theorem piece24_norm_le (C₀ : ℕ) (P : WTParams) (G : LGContext C₀ P) {p N : ℕ} (hp : p < P.D)
    (hN : N ≤ P.N (p + 1) ^ 4) (kind : TreeKind) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) (hmmax : 2 ≤ 10 * P.R (p + 1)) (σ : Fin 2 ⊕ Fin (2 * 2) ≃ Fin (2 * 3))
    (hsA : (fun i => childSig (σ (.inl i))) = ![1, -1])
    (hs4 : (fun i => childSig (σ (.inr i))) = ![1, -1, 1, -1])
    (n : Fin (2 * 3) → (Fin P.d → ℤ)) (k : Mom P.d) (tt : Fin (2 * 3) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1))
    (hF : ∀ q : ℕ, Summable fun m : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L m)|)
    (hnumA : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (4 * 2 * P.Lambda (p + 1)) *
      gardenT P G.Cφ p 2 N' ^ (8 * 2 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 2) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) * P.L ^ (-((2 : ℕ) - 1 : ℝ) / 70) ≤ 1)
    (hnumC : ∀ N' ≤ P.N (p + 1) ^ 4, ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
      coupleT P G.Cφ p N' ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁) ^ (N' + 1) * P.δ ^ (6 * P.ν * N') *
      P.L ^ (-P.η ^ 7) ≤ P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))
    (Creg : ℕ → ℝ) (hreg : RegularFamilyBound P (inputsF P Rr) p Creg) :
    ‖∑ᶠ y ∈ {y | y ∈ Y6Set P p N kind ∧
        MinimalAt y.garden (σ (.inl 0)) (Finset.univ.image fun i => σ (.inl i))},
        kernelKgen P.L P.γ P.δ (inputsF P Rr) y (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0‖ ≤
      ∑ d ∈ (Acomp1_finite P p N σ (0 : Fin 2)).toFinset.image (compData p),
        ∑ e ∈ (Bcomp1_finite P p N (a := 2) σ).toFinset.image (compData p),
          if Joint1 P p N kind σ d e then
            (if n (σ (.inl 0)) = n (σ (.inl 1)) then
              jbr (k + latticePoint P.L (n (σ (.inl 0)))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
                (P.δ ^ (2 * P.ν * d.1) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) +
                  Creg d.1 * P.δ ^ ((d.1 : ℝ) / 4)) else 0) *
            (PieceBound2 P p N τ1 (fun i => childSig (σ (.inr i))) e Creg (fun i => n (σ (.inr i))) k +
              PieceBound2 P p N τ2 (fun i => childSig (σ (.inr i))) e Creg (fun i => n (σ (.inr i))) k +
              jbrProdAt P.L k (fun i => n (σ (.inr i))) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
                P.L ^ (-(((2 : ℕ) : ℝ) - 1) / 4) * P.δ ^ (2 * P.ν * e.1))
          else 0 := by
  refine piece1_norm_le P (inputsF P Rr) p N kind σ 0 tt k n hF
    (fun d => d.1 ≤ N ∧ ∀ i, d.2 i ≤ P.N (p + 1)) (fun e => e.1 ≤ N ∧ ∀ i, e.2 i ≤ P.N (p + 1))
    (fun d e h => joint1_allowed P p N kind σ d e h) _ _ ?_ ?_
  · intro d _ ⟨hd, hv⟩
    exact couple_set_bound C₀ P G hp Rr hRr hR1 (hd.trans hN) (fun i => n (σ (.inl i))) k (fun i => tt (σ (.inl i))) (fun i => htt _) d.2
      (hnumC d.1 (hd.trans hN)) Creg hreg _
      (fun LA h => (Acomp1_couple_mem_iff P p N σ hsA 0 rfl d hd hv LA).1 h)
      (fun LA h => (Acomp1_couple_mem_iff P p N σ hsA 0 rfl d hd hv LA).2 h)
  · intro e _ ⟨he, hv⟩
    exact Bplain4_slice_bound C₀ P G hp hN Rr hRr hR1 hmmax σ hs4 e he hv _ k (fun i => tt (σ (.inr i))) (fun i => htt _) hF hnumA hnumC Creg hreg

end

end WaveTurbulence.GammaLow.LGLow.CC
