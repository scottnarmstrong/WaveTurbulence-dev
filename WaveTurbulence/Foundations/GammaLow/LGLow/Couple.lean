/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.LGLow.TypeGate
public import WaveTurbulence.Foundations.Spine.NonregularCoupleP

/-! # LG-low (packet L07): TARGET term (b) through the waist

`couple_estimate_of_typeGate` is main's `LGSpine.couple_estimate_of_gate` (`Spine/NonregularCoupleP.lean`), copied by
source with the gate bundle replaced by `hTG : TypeGateAt P` (its only use is `evalOps_gate_bound`). -/

public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open MeasureTheory Set Finset NormBridgeScratch
open scoped Classical ENNReal

/-- Main's `couple_estimate_of_gate` through the waist. -/
theorem couple_estimate_of_typeGate (P : WTParams) (hs : PieceSmall P) (hTG : TypeGateAt P)
    (hd : 1 ≤ P.d) (hlowP : LowProfileAt P) (htime : P.τstar = (P.D : ℝ) * P.δ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ)
    {p : ℕ} (hp : p < P.D) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    (hR1 : 1 ≤ P.R (p + 1)) {N : ℕ} (hN : N ≤ P.N (p + 1) ^ 4) {t : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1))
    (hTC : TwistClosed p (coupleSet P p N))
    (hnum : ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P Cφ p N ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N + 1) * P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) :
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
        (fun k => nonregularCoupleSum P (inputsF P Rr) (p + 1) N t k) ≤
      ENNReal.ofReal (P.δ ^ (2 * P.ν * N) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))) := by
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hδ0 := hs.delta_pos
  have hC₁ := hs.c1_ge
  set Λ := P.Lambda (p + 1) with hΛ
  set A1 := coupleSet P p N with hA1
  have hmemA : ∀ LG ∈ A1, IsCanonC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1))
      (P.N (p + 1 - 1)) ∧ LG.garden.order = N ∧ ¬ IsRegularCouple LG.garden := by
    intro LG hLG
    rw [hA1, coupleSet, Finset.mem_filter] at hLG
    have := (Canon.finite_truncSumC_support P (p + 1) N).mem_toFinset.mp hLG.1
    exact ⟨this.1, this.2.1, this.2.2, hLG.2⟩
  have hrhs : 0 ≤ P.δ ^ (2 * P.ν * (N : ℝ)) * P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) :=
    mul_nonneg (Real.rpow_nonneg hδ0.le _) (Real.rpow_nonneg hL0.le _)
  have hfeq : (fun k => nonregularCoupleSum P (inputsF P Rr) (p + 1) N t k) =
      fun k => ∑ LG ∈ A1, KQ P.L P.γ P.δ (inputsF P Rr) LG t k := rfl
  rw [hfeq]
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
  have hfV : (fun k => ∑ LG ∈ A1, KQ P.L P.γ P.δ (inputsF P Rr) LG t k) =
      evalV P A1 (fun j => if j = 0 then t else t) (fun _ => 0) h0 := by
    funext k
    unfold evalV
    refine Finset.sum_congr rfl fun LG _ => ?_
    show _ = kernelLeaves P.L P.γ P.δ LG (typeProfiles LG h0) (fun b => if b.1.1 = 0 then t else t) 0 k
      (fun _ => 0) 0
    rw [show typeProfiles LG h0 = layerProfiles LG (inputsF P Rr) from typeProfiles_layer LG _,
      kernelLeaves_layerProfiles]
    rfl
  have hf : ContDiff ℝ (4 * Λ : ℕ) (evalV P A1 (fun j => if j = 0 then t else t) (fun _ => 0) h0) := by
    let i0 : Fin P.d := ⟨0, by omega⟩
    have hI := hInvG (List.replicate (4 * Λ) (TOp.der (w := 2) i0)) (by simp [dcnt, TOp.dc])
      (fun j j' => by simp [fcnt, TOp.fc])
    have := evalV_contDiff hctx (fun j => if j = 0 then t else t) (fun _ => 0)
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
  have hid := couple_weight_identity hctx (0 : Fin 2) (hσ2 0) (fun j => if j = 0 then t else t)
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
      ‖evalOps (evalV P A1 (fun j => if j = 0 then t else t) (fun _ => 0)) M lam
          (word.reverse.map TOp.der ++ (opsOfChoice0 (0 : Fin 2) c).map fun f => TOp.form f.1 f.2) h0 x‖ ≤
        T ^ Lops * (((B₀ : ℝ)) ^ (N + 1) *
          (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-(((1 : ℕ) : ℝ) - 1) * (1 / 4 + 1 / 70))))) := by
    intro c
    refine evalOps_typeGate_bound (R := 1) P hs hTG hd hp le_rfl
      (by omega) hN1 hN A1 hcar hTC (fun j => if j = 0 then t else t) (fun j => by split_ifs <;> exact ht)
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
  have hnorm : ‖((jbr x ^ (4 * Λ) : ℝ) : ℂ) * wordD word (evalV P A1 (fun j => if j = 0 then t else t)
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

end WaveTurbulence.GammaLow.LGLow
