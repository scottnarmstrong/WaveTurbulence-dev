/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.GateCouple
public import WaveTurbulence.Foundations.Spine.RA1LW.GateTree
public import WaveTurbulence.Foundations.Spine.RA1LW.GateItems
public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.Orders
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability

/-! # RA1-LEAFWISE: `LeafwiseRegularAsymptoticsGate`

TARGET regref1–3 (L1145–L1232), applied to individually modified leaf inputs (L2065–L2067); DH23 Prop 6.1.
Proved from the leafwise RA1 statements `ra1_couple_leafwise`, `ra1_tree_leafwise` (unit leaf bound, layer 0),
reduced to arbitrary leaf bounds `B_ℓ` by multilinearity (`couple_scaled`, `tree_scaled`), translated to layer
`r` (`couple_item_le`) and, for trees with `q' < r`, relayered, frozen at `s = r` and traced (`tree_item_le`). -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp MeasureTheory Set Finset TTree WaveTurbulence.Regref WaveTurbulence.Fourier
open scoped ENNReal

theorem traceConst_ne_top' (θ : ℝ) : traceConst (r := 2) θ chiUnit ≠ ⊤ := by
  unfold traceConst
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (timeFourierNorm_lt_top_of_smooth_compact θ (coordinateCutoff_hasCompactSupport chiUnit_hasCompactSupport)
      (coordinateCutoff_contDiff chiUnit_contDiff)).ne

/-- The real trace constant `Ktr θ = 2^θ ‖χ₀ ⊗ χ₀‖_{𝔛^θ}`. -/
@[expose] def Ktr' (θ : ℝ) : ℝ := (traceConst (r := 2) θ chiUnit).toReal

theorem one_le_Ktr' {θ : ℝ} (hθ : 0 ≤ θ) : 1 ≤ Ktr' θ := by
  have h := one_le_traceConst (r := 2) hθ chiUnit_contDiff (coordinateCutoff_chiUnit (t := fun _ => 0)
    ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩)
  have := ENNReal.toReal_mono (traceConst_ne_top' θ) h
  simpa [Ktr'] using this

theorem traceConst_mul_ofReal' (θ : ℝ) (x : ℝ) :
    traceConst (r := 2) θ chiUnit * ENNReal.ofReal x = ENNReal.ofReal (Ktr' θ * x) := by
  rw [Ktr', ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (traceConst_ne_top' θ)]

theorem bound_mono_K'' {K C C' δ x : ℝ} (n : ℕ) (hK : 1 ≤ K) (hC : 0 ≤ C) (hCC : K * C ≤ C') (hδ : 0 ≤ δ)
    (hx : 0 ≤ x) : K * (C * (C * δ) ^ n * x) ≤ C' * (C' * δ) ^ n * x := by
  have hC' : C ≤ C' := (le_mul_of_one_le_left hC hK).trans hCC
  have h1 : (C * δ) ^ n ≤ (C' * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hC hδ) (mul_le_mul_of_nonneg_right hC' hδ) n
  have hC'0 : 0 ≤ C' := hC.trans hC'
  calc K * (C * (C * δ) ^ n * x) = (K * C) * (C * δ) ^ n * x := by ring
    _ ≤ C' * (C' * δ) ^ n * x := by gcongr

theorem bound_mono_K''' {K C C' : ℝ} (n : ℕ) (hK : 1 ≤ K) (hC : 0 ≤ C) (hCC : K * C ≤ C') :
    K * (C * C ^ n) ≤ C' * C' ^ n := by
  have hC' : C ≤ C' := (le_mul_of_one_le_left hC hK).trans hCC
  have hC'0 : 0 ≤ C' := hC.trans hC'
  calc K * (C * C ^ n) = (K * C) * C ^ n := by ring
    _ ≤ C' * C' ^ n := by gcongr

theorem one_le_log_of_exp_le' {L : ℝ} (h : Real.exp 1 ≤ L) : 1 ≤ Real.log L := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) h

theorem regBound_one' (P : WTParams) (n : ℕ) :
    regBound P n 1 = ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(gam1L P.d P.γ - Real.sqrt P.η))) := by
  simp only [regBound, Nat.cast_one, mul_one]
  rfl

/-- **`LeafwiseRegularAsymptoticsGate`** (DH23 Prop 6.1 / TARGET regref1–3 with individually modified leaf
inputs, L2065–L2067), at the exact type of the lg-spine statement. -/
theorem leafwiseRegularAsymptotics : LGSpine.LeafwiseRegularAsymptoticsGate := by
  intro d hd γ hγ
  obtain ⟨ηc, hηc, Hc⟩ := ra1_couple_leafwise d hd γ hγ
  obtain ⟨ηt, hηt, Ht⟩ := ra1_tree_leafwise d hd γ hγ
  refine ⟨min (min ηc ηt) 1, lt_min (lt_min hηc hηt) one_pos, fun η hη φin _ τs _ φ hφ => ?_⟩
  have hη0 : 0 < η := hη.1
  have hηc' : η ∈ Ioc 0 ηc := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hηt' : η ∈ Ioc 0 ηt := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  obtain ⟨Cc, hCc, δc, hδc, Hc2⟩ := Hc η hηc' 1
  obtain ⟨Ct, hCt, δt, hδt, Ht2⟩ := Ht η hηt' 1
  set K := Ktr' η with hKdef
  have hK1 : 1 ≤ K := one_le_Ktr' hη0.le
  set Cm := max Cc Ct with hCmdef
  have hCm0 : 0 ≤ Cm := le_max_of_le_left (zero_le_one.trans hCc)
  set C₁ := K * Cm with hC₁def
  have hC₁ : 1 ≤ C₁ := one_le_mul_of_one_le_of_one_le hK1 (le_max_of_le_left hCc)
  have hKc : 1 * Cc ≤ C₁ := by
    rw [one_mul]
    exact (le_max_left _ _).trans (le_mul_of_one_le_left hCm0 hK1)
  have hKt2 : K * Ct ≤ C₁ :=
    mul_le_mul le_rfl (le_max_right _ _) (zero_le_one.trans hCt) (zero_le_one.trans hK1)
  have hKt1 : 1 * Ct ≤ C₁ := by
    rw [one_mul]
    exact (le_max_right _ _).trans (le_mul_of_one_le_left hCm0 hK1)
  refine ⟨C₁, hC₁, 1, one_pos, fun ν _ => ⟨min δc δt, lt_min hδc hδt, fun δ hδ D hD hτ => ?_⟩⟩
  have hδc' : δ ∈ Ioc 0 δc := ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩
  have hδt' : δ ∈ Ioc 0 δt := ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩
  obtain ⟨Lc, Hc3⟩ := Hc2 δ hδc' (ordExp d D)
  obtain ⟨Lt, Ht3⟩ := Ht2 δ hδt' (ordExp d D)
  refine ⟨1, le_rfl, max (max (max 2 Lc) Lt) (Real.exp 1),
    le_max_of_le_left (le_max_of_le_left (le_max_left _ _)), fun L hL => ?_⟩
  intro p hp r hr n hn
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLc : Lc ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLt : Lt ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hlog : 1 ≤ Real.log L := one_le_log_of_exp_le' ((le_max_right _ _).trans hL)
  have hnA : (n : ℝ) ≤ Real.log L ^ ((ordExp d D : ℕ) : ℝ) :=
    le_logPow_ordExp ⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ (by show 1 ≤ d; omega) hlog p n hn
  have hx : 0 ≤ L ^ (-(gam1L d γ - Real.sqrt η)) := Real.rpow_nonneg (by linarith) _
  have hδ0 : 0 ≤ δ := hδ.1.le
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Hc1, Hc2'⟩ := Hc3 L hLc n hnA
  obtain ⟨Ht1, Ht2'⟩ := Ht3 L hLt n hnA
  refine ⟨?_, ?_⟩
  · -- couples
    intro Q hQ hsz LG hdec hlay H B hctl
    have hctl0 : LGSpine.LeafwiseControlled (layer0 LG) H B := hctl
    have hX : ENNReal.ofReal (Cc * (Cc * δ) ^ n * L ^ (-(gam1L d γ - Real.sqrt η))) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hdec0 : Q.Decodes (layer0 LG).garden := hdec
    have hsc := couple_scaled L γ δ η hd1 Q (layer0 LG) hdec0 _ hX
      (fun H' hH' => Hc1 Q hQ hsz (layer0 LG) hdec0 (fun _ => rfl) H' hH') H B hctl0
    have hit := couple_item_le L γ δ H hdec hlay (η := η) (Λ := 30 * d) hsc
    constructor
    · rw [regBound_one']
      refine hit.trans ?_
      have e0 : LGSpine.leafSizeProduct (layer0 LG) B = LGSpine.leafSizeProduct LG B := rfl
      rw [e0, mul_comm]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      simpa only [one_mul] using bound_mono_K'' n le_rfl (zero_le_one.trans hCc) hKc hδ0 hx
    · intro hdom Z hZ
      have hm := couple_Mstar_scaled hd1 Q (layer0 LG) hdec0 (Cc * Cc ^ n)
        (mul_nonneg (zero_le_one.trans hCc) (pow_nonneg (zero_le_one.trans hCc) _))
        (fun H' hH' Z hZ => ((Hc2' Q hQ hdom hsz).2 H' hH' Z hZ)) H B hctl0 Z hZ
      refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · simpa only [one_mul] using bound_mono_K''' n le_rfl (zero_le_one.trans hCc) hKc
      · exact Finset.prod_nonneg fun ℓ _ => (B ℓ.1).2
  · -- trees
    intro X hX hsz LG hdec q' hq hlay H B hctl
    have hctl0 : LGSpine.LeafwiseControlled (layer0 LG) H B := hctl
    have hM : ENNReal.ofReal (Ct * (Ct * δ) ^ n * L ^ (-(gam1L d γ - Real.sqrt η))) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hdec0 : X.DecodesTree (layer0 LG).garden := hdec
    have hsc := tree_scaled L γ δ η hd1 X (layer0 LG) hdec0 _ hM
      (fun H' hH' => Ht1 X hX hsz (layer0 LG) hdec0 (fun _ => rfl) H' hH') H B hctl0
    have hFs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k : Mom d,
        Summable fun m : Fin d → ℤ => |H ℓ.1 (k + latticePoint L m)| := fun ℓ hℓ k =>
      LGSpine.summable_abs_coset_of_SNormR (by linarith) (by omega : d + 1 ≤ 40 * d)
        (B ℓ.1).2 (H ℓ.1) (hctl ℓ hℓ) k
    have hit := tree_item_le L γ δ H hdec hFs hq hlay hη0.le (Λ := 30 * d) (by omega) hsc
    constructor
    · rw [regBound_one']
      refine hit.trans ?_
      have e0 : LGSpine.leafSizeProduct (layer0 LG) B = LGSpine.leafSizeProduct LG B := rfl
      rw [e0, mul_comm (ENNReal.ofReal (LGSpine.leafSizeProduct LG B)), ← mul_assoc, traceConst_mul_ofReal']
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      exact bound_mono_K'' n hK1 (zero_le_one.trans hCt) hKt2 hδ0 hx
    · intro hdom Z hZ
      have hm := tree_Nstar_scaled hd1 X (layer0 LG) hdec0 (Ct * Ct ^ n)
        (mul_nonneg (zero_le_one.trans hCt) (pow_nonneg (zero_le_one.trans hCt) _))
        (fun H' hH' Z hZ => ((Ht2' X hX hdom hsz (LG.garden.sig 0)).2 H' hH' Z hZ)) H B hctl0 Z hZ
      refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · simpa only [one_mul] using bound_mono_K''' n le_rfl (zero_le_one.trans hCt) hKt1
      · exact Finset.prod_nonneg fun ℓ _ => (B ℓ.1).2

end WaveTurbulence.RA1Leafwise
