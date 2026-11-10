/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.NonregularGardenP
public import WaveTurbulence.Foundations.XChain.JbrBounds
public import WaveTurbulence.Foundations.FlowerTop.Port.GardenEvalAt
/-! AMEND-ST3 (R69): the garden estimate for an arbitrary TWIST-CLOSED sub-family `A` of the truncated gardens
(for instance the slices at a fixed vector of per-tree top orders and component orders; LF twists preserve those),
at an arbitrary BASE momentum `k` (weights `jbr(k + n_j / L)`, `jbrProdAt`). The current `garden_estimate_of_gate`
is the case `A = gardenSet`, `k = 0` (`garden_estimate_of_gate_of_slice`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset NormBridgeScratch WaveTurbulence.Induct
open scoped Classical ENNReal

/-- The root weight at the base momentum `k`: `∏_j <k + n_j / L>`. -/
@[expose] noncomputable def jbrProdAt {w d : ℕ} (L : ℝ) (k : Mom d) (n : Fin w → (Fin d → ℤ)) : ℝ :=
  ∏ j, jbr (k + latticePoint L (n j))

theorem garden_estimate_slice_of_gate (C₀ : ℕ) (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L) (hgate : Stage1ReductionAt C₀ P)
    (hd : 1 ≤ P.d) (hlowP : LowProfileAt P) (htime : P.τstar = (P.D : ℝ) * P.δ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ)
    {p : ℕ} (hp : p < P.D) (Rr : ℕ → Mom P.d → ℝ) (hRr : RemainderBound P Rr p)
    {m : ℕ} (hm2 : 2 ≤ m) (hmmax : m ≤ 10 * P.R (p + 1)) (ζ : Fin (2 * m) → ℤˣ)
    (hζ : IsBalancedSig ζ) (n : Fin (2 * m) → (Fin P.d → ℤ)) (k : Mom P.d) {N : ℕ}
    (hN : N ≤ P.N (p + 1) ^ 4) {t : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1))
    (A : Finset (LayeredGarden (2 * m)))
    (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1))
      (P.N (p + 1 - 1)) ∧ LG.garden.sig = ζ ∧ LG.garden.order = N)
    (hTC : TwistClosed p A)
    (hnum : ((P.d : ℝ) + 1) ^ (4 * m * P.Lambda (p + 1)) * gardenT P Cφ p m N ^ (8 * m * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N + m) * P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) / 70) ≤ 1) :
    ‖∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun _ => t) 0 k n 0‖ ≤
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
    have hz : ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun _ => t) 0 k n 0 = 0 := by
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
  have hid := garden_weight_identity_at hctx hσ2 (fun _ => t) n k lam hlampos.ne' (2 * Λ) h0 hadm
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
      ‖evalOps (evalV P A0 (fun _ => t) n) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 k‖ ≤
        T ^ Lops * (((B₀ : ℝ)) ^ (N + m) *
          (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) * (1 / 4 + 1 / 70))))) := by
    intro c
    refine evalOps_gate_bound C₀ P hs hcoarse hfourier hcount habs hlog hd hgate hp (by omega) hmmax hN1 hN A0 hcar
      hTC (fun _ => t) (fun _ => ht) n hplain k M lam T hT1 hTeq.le xs hxspos.le hxM 0 B₀ hB₀ Lops _
      (le_trans ((by simpa using length_opsOfChoice_le (d := P.d) (w := 2 * m) (n := 2 * Λ) c)) (by rw [hLops]; ring_nf; exact le_rfl)) (by rw [dcnt_forms]) h0 U P.C₁ hU0 (by linarith)
      (hInv c) ?_
    rw [hxsκ]
    show P.C₁ + U * ((1 + y) ^ Lops - 1) ≤ 2 * P.C₁
    exact hy2
  have hsumV : evalV P A0 (fun _ => t) n h0 k =
      ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun _ => t) 0 k n 0 := by
    unfold evalV
    refine Finset.sum_congr rfl fun LG _ => ?_
    rw [show typeProfiles LG h0 = layerProfiles LG (inputsF P Rr) from typeProfiles_layer LG _]
  have hW2 : (∏ j, jbr (k + latticePoint P.L (n j)) ^ (2 * (2 * Λ))) = W := by
    rw [hW, jbrProdAt, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring_nf
  have hnorm : W * ‖∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun _ => t) 0 k n 0‖ ≤
      ((P.d : ℝ) + 1) ^ (2 * m * (2 * Λ)) * (T ^ Lops * ((2 * P.C₁) ^ (N + m) *
        (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) * (1 / 4 + 1 / 70)))))) := by
    have h1 : ((W : ℝ) : ℂ) * ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun _ => t) 0 k n 0 =
        ∑ c : Fin (2 * m) → Fin (2 * Λ) → Option (Fin P.d),
          evalOps (evalV P A0 (fun _ => t) n) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 k := by
      rw [← hsumV, ← hW2]
      exact hid
    have hnm : W * ‖∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun _ => t) 0 k n 0‖ =
        ‖((W : ℝ) : ℂ) * ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun _ => t) 0 k n 0‖ := by
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
  have hmain : W * ‖∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (layerProfiles LG (inputsF P Rr)) (fun _ => t) 0 k n 0‖ ≤
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


end WaveTurbulence.LGSpine
