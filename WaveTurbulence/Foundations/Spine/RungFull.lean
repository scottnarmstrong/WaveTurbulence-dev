/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RungDefs
public import WaveTurbulence.Foundations.Spine.Corner
public import WaveTurbulence.Foundations.Sumint.BilinearReversedPairWindow
public import WaveTurbulence.Foundations.Sumint.BilinearSplitIntegral
public import WaveTurbulence.Foundations.Sumint.BilinearTimeSign
public import WaveTurbulence.Foundations.Sumint.BilinearCutoffRescale
public import WaveTurbulence.Foundations.Sumint.BilinearWeylBridge
/-! # The fully smooth rung: same layer and different layers (S3b LADDER-DECAY)

`rungSum` with the inserted scale-four cutoffs is a bilinear lattice sum at mesh `4 L`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory Set WaveTurbulence WaveTurbulence.WeylSums WaveTurbulence.Sumint

variable {d : ℕ}

/-- The inserted cutoff weights of a rung (scale four). -/
noncomputable def cutW (L : ℝ) (a b : Fin d → ℝ) (p : Pt d) : ℂ :=
  ((inputCutoff a (latticePoint L p.1) * inputCutoff b (latticePoint L p.2) : ℝ) : ℂ)

/-- Identification of the cutoff rung sum with the landed bilinear lattice sum. -/
theorem rungSum_cutW_eq {L : ℝ} (hL : 0 < L) (a b : Fin d → ℝ) (c : ℝ) (S : Finset (Pt d))
    (hS : ∀ p, cutW L a b p ≠ 0 → p ∈ S) (lam ν : Pt d →+ ℝ) (t : ℝ × ℝ) :
    rungSum L c (cutW L a b) S lam ν t =
      bilinearLatticeSum (4 * L) (16 * (c * (t.2 - t.1))) ((1 / 4 : ℝ) • WithLp.toLp 2 a)
        ((1 / 4 : ℝ) • WithLp.toLp 2 b)
        ((4 : ℝ) • repVec L (Pt.left (t.2 • lam + ν))) ((4 : ℝ) • repVec L (Pt.right (t.2 • lam + ν))) := by
  rw [← inputCutoff_bilinear_sum_eq]
  unfold rungSum
  symm
  rw [tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [cutW, fourierChar_eq_e]
    congr 2
    have h := addHom_pt_eq hL.ne' (t.2 • lam + ν) p
    simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] at h
    rw [bil]
    linarith [h]
  · intro p hp
    have h0 : ((inputCutoff a (latticePoint L p.1) * inputCutoff b (latticePoint L p.2) : ℝ) : ℂ) = 0 := by
      by_contra h; exact hp (hS p h)
    simp [h0]

/-- Window hypothesis for the rung: the kernel time stays below `T1 L^{2γ}`. -/
def WindowOK (T1 L c l u v w γ : ℝ) : Prop :=
  ∀ t ∈ Icc v w, -(T1 * L ^ (2 * γ)) ≤ c * (l - t) ∧ c * (u - t) ≤ T1 * L ^ (2 * γ)

/-- **The smooth rung, same layer.** -/
theorem rung_full_same (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηγ : η ≤ 2 * ((d : ℝ) - 1) * (1 - γ)) (T1 : ℝ) (hT1 : 0 < T1) :
    ∃ C L0 : ℝ, 0 ≤ C ∧ 2 ≤ L0 ∧ ∀ L ≥ L0, ∀ (a b : Fin d → ℝ) (c l u v w : ℝ)
      (lam ν : Pt d →+ ℝ) (S : Finset (Pt d)), 0 < c → l ≤ u → v ≤ w →
      (∀ p, cutW L a b p ≠ 0 → p ∈ S) → WindowOK T1 L c l u v w γ →
      (∫ t in Icc v w, ∫ s in Icc l u, ‖rungSum L c (cutW L a b) S lam ν (s, t)‖) ≤
        (w - v) * (16 * c)⁻¹ * C * (4 * L) ^ (2 * d) := by
  obtain ⟨C, L0, hC, hL0, hb⟩ := exists_bilinear_reversed_pair_window_bound d hd γ hγ η hη hηγ
    (16 * T1) (by positivity)
  refine ⟨C, max (L0 / 4) 2, hC, le_max_right _ _, ?_⟩
  intro L hL a b c l u v w lam ν S hc hlu hvw hS hwin
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL0' : L0 ≤ 4 * L := by
    have := (le_max_left _ _).trans hL
    linarith
  have hLp : 0 < L := by linarith
  have hwin' : ∀ t ∈ Icc v w, -(16 * T1 * (4 * L) ^ (2 * γ)) ≤ 16 * c * (l - t) ∧
      16 * c * (u - t) ≤ 16 * T1 * (4 * L) ^ (2 * γ) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hwin t ht
    have hpow : L ^ (2 * γ) ≤ (4 * L) ^ (2 * γ) :=
      Real.rpow_le_rpow hLp.le (by linarith) (by linarith [hγ.1])
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hpow hT1.le]
  have h := hb (4 * L) hL0' ((1 / 4 : ℝ) • WithLp.toLp 2 a) ((1 / 4 : ℝ) • WithLp.toLp 2 b)
    (fun t => (4 : ℝ) • repVec L (Pt.left (t • lam + ν)))
    (fun t => (4 : ℝ) • repVec L (Pt.right (t • lam + ν))) (16 * c) l u v w (by positivity) hlu hvw hwin'
  refine le_trans (le_of_eq ?_) h
  refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
  refine setIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
  rw [rungSum_cutW_eq hLp a b c S hS lam ν (s, t)]
  simp only [mul_assoc]

lemma scalarBracket_pow_inv_le {d : ℕ} (σ : ℝ) :
    ((scalarBracket σ) ^ d)⁻¹ ≤ (Real.sqrt 2) ^ d * ((1 + |σ|) ^ d)⁻¹ := by
  have h1 : (1 + |σ|) ≤ Real.sqrt 2 * scalarBracket σ := by
    unfold scalarBracket
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs σ, sq_nonneg (1 - |σ|)]
  have h2 : 0 < scalarBracket σ := lt_of_lt_of_le one_pos (one_le_scalarBracket σ)
  have h3 : 0 < 1 + |σ| := by positivity
  have h4 : (1 + |σ|) ^ d ≤ (Real.sqrt 2 * scalarBracket σ) ^ d := pow_le_pow_left₀ h3.le h1 d
  have h5 : (Real.sqrt 2) ^ d ≠ 0 := by positivity
  calc ((scalarBracket σ) ^ d)⁻¹ = (Real.sqrt 2) ^ d * ((Real.sqrt 2 * scalarBracket σ) ^ d)⁻¹ := by
        rw [mul_pow, mul_inv, mul_inv_cancel_left₀ h5]
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos h3 d) h4) (by positivity)

/-- **The smooth rung, different layers** (`u ≤ v` or `w ≤ l`): the extra time distance gains. -/
theorem rung_full_diff (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηγ : η ≤ 2 * ((d : ℝ) - 1) * (1 - γ)) (T1 : ℝ) (hT1 : 0 < T1) :
    ∃ C L0 : ℝ, 0 ≤ C ∧ 2 ≤ L0 ∧ ∀ L ≥ L0, ∀ (a b : Fin d → ℝ) (c l u v w : ℝ)
      (lam ν : Pt d →+ ℝ) (S : Finset (Pt d)), 0 < c → l ≤ u → v ≤ w →
      (∀ p, cutW L a b p ≠ 0 → p ∈ S) → WindowOK T1 L c l u v w γ → (u ≤ v ∨ w ≤ l) →
      (∫ t in Icc v w, ∫ s in Icc l u, ‖rungSum L c (cutW L a b) S lam ν (s, t)‖) ≤
        C * (4 * L) ^ (2 * d) * ((16 * c)⁻¹ * (16 * c)⁻¹ +
          (w - v) * (16 * c)⁻¹ * (4 * L) ^ (-2 * ((d : ℝ) - 1) * (1 - γ) + η)) := by
  obtain ⟨Cs, Cm, L1, hCs, hCm, hL1, hsplit⟩ :=
    exists_bilinear_split_integral_bound d hd γ hγ η hη (16 * T1) (by positivity)
  obtain ⟨Cw, hCw, hweyl⟩ := exists_bilinear_weyl_small_bound d
  set K : ℝ := 2 / ((d : ℝ) - 1) with hK
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨(Cw * (Real.sqrt 2) ^ d * K) + Cm, max (L1 / 4) 2, by positivity, le_max_right _ _, ?_⟩
  intro L hL a b c l u v w lam ν S hc hlu hvw hS hwin hsep
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL1' : L1 ≤ 4 * L := by
    have := (le_max_left _ _).trans hL
    linarith
  have hLp : 0 < L := by linarith
  set L' : ℝ := 4 * L with hL'
  have hL'p : 0 < L' := by positivity
  have hc' : 0 < 16 * c := by positivity
  have hwin' : ∀ t ∈ Icc v w, -(16 * T1 * L' ^ (2 * γ)) ≤ 16 * c * (l - t) ∧
      16 * c * (u - t) ≤ 16 * T1 * L' ^ (2 * γ) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hwin t ht
    have hpow : L ^ (2 * γ) ≤ L' ^ (2 * γ) :=
      Real.rpow_le_rpow hLp.le (by rw [hL']; linarith) (by linarith [hγ.1])
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hpow hT1.le]
  -- the pointwise rung function at a fixed outer time
  set ξ : ℝ → Mom d := fun t => (4 : ℝ) • repVec L (Pt.left (t • lam + ν)) with hξ
  set ζ : ℝ → Mom d := fun t => (4 : ℝ) • repVec L (Pt.right (t • lam + ν)) with hζ
  set a' : Mom d := (1 / 4 : ℝ) • WithLp.toLp 2 a
  set b' : Mom d := (1 / 4 : ℝ) • WithLp.toLp 2 b
  have hrew : ∀ t s : ℝ, ‖rungSum L c (cutW L a b) S lam ν (s, t)‖ =
      ‖bilinearLatticeSum L' ((16 * c) * (s - t)) a' b' (-ξ t) (-ζ t)‖ := by
    intro t s
    rw [rungSum_cutW_eq hLp a b c S hS lam ν (s, t)]
    have : 16 * (c * (t - s)) = -((16 * c) * (s - t)) := by ring
    simp only
    rw [this, norm_bilinearLatticeSum_time_neg]
  -- inner bound
  set Wd : ℝ := 16 * T1 * L' ^ (2 * γ)
  set A2 : ℝ := Cw * (Real.sqrt 2) ^ d * L' ^ (2 * d)
  set Al : ℝ := Cm * L' ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)
  have hinner : ∀ t ∈ Icc v w, (∫ s in Icc l u, ‖rungSum L c (cutW L a b) S lam ν (s, t)‖) ≤
      (16 * c)⁻¹ * (A2 * (K * (1 + (if u ≤ v then 16 * c * (t - v) else 16 * c * (w - t))) ^
        (-((d : ℝ) - 1))) + Al) := by
    intro t ht
    have hL'1 : 1 ≤ L' := by rw [hL']; linarith
    have hL'1' : L1 ≤ L' := hL1'
    set m : ℝ := (if u ≤ v then 16 * c * (t - v) else 16 * c * (w - t)) with hm
    have hm0 : 0 ≤ m := by
      rw [hm]
      split_ifs
      · exact mul_nonneg hc'.le (by linarith [ht.1])
      · exact mul_nonneg hc'.le (by linarith [ht.2])
    have hdist : ∀ s ∈ Icc l u, m ≤ |16 * c * (s - t)| := by
      intro s hs
      rw [hm]
      split_ifs with huv
      · have h1 : s - t ≤ -(t - v) := by linarith [hs.2, ht.1]
        rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc'.le (by linarith [hs.2, ht.1]))]
        nlinarith
      · have hwl : w ≤ l := by rcases hsep with h | h; exact absurd h huv; exact h
        rw [abs_of_nonneg (mul_nonneg hc'.le (by linarith [hs.1, ht.2]))]
        nlinarith [hs.1, ht.2]
    have hfc : Continuous (fun σ : ℝ => ‖bilinearLatticeSum L' σ a' b' (-ξ t) (-ζ t)‖) :=
      (continuous_bilinearLatticeSum hL'p a' b' (-ξ t) (-ζ t)).norm
    have hpt : ∀ σ : ℝ, |σ| ≤ L' → ‖bilinearLatticeSum L' σ a' b' (-ξ t) (-ζ t)‖ ≤
        0 + A2 * ((1 + |σ|) ^ d)⁻¹ := by
      intro σ hσ
      have h1 := hweyl hL'1 σ hσ a' b' (-ξ t) (-ζ t)
      refine h1.trans ?_
      rw [div_eq_mul_inv, zero_add]
      calc Cw * L' ^ (2 * d) * (scalarBracket σ ^ d)⁻¹
          ≤ Cw * L' ^ (2 * d) * ((Real.sqrt 2) ^ d * ((1 + |σ|) ^ d)⁻¹) :=
            mul_le_mul_of_nonneg_left (scalarBracket_pow_inv_le σ) (by positivity)
        _ = _ := by simp only [A2]; ring
    have hlarge := (hsplit L' hL'1' a' b' (-ξ t) (-ζ t)).2
    have hmain := inner_window_bound hd hfc (fun σ => norm_nonneg _) (c := 16 * c) (l := l) (u := u)
      (t := t) (W := Wd) (Ls := L') (A1 := 0) (A2 := A2) (Al := Al) (m := m) hc' hlu
      (hwin' t ht).1 (hwin' t ht).2 hm0 hdist le_rfl (by positivity) hpt hlarge
    have heq : (∫ s in Icc l u, ‖rungSum L c (cutW L a b) S lam ν (s, t)‖) =
        ∫ s in Icc l u, ‖bilinearLatticeSum L' ((16 * c) * (s - t)) a' b' (-ξ t) (-ζ t)‖ :=
      setIntegral_congr_fun measurableSet_Icc (fun s _ => hrew t s)
    rw [heq]
    refine hmain.trans (le_of_eq ?_)
    simp only [mul_zero, zero_add, hK]
  -- outer integration
  set mfun : ℝ → ℝ := fun t => if u ≤ v then 16 * c * (t - v) else 16 * c * (w - t) with hmfun
  have hcont : ContinuousOn (fun t : ℝ => (16 * c)⁻¹ * (A2 * (K * (1 + mfun t) ^ (-((d : ℝ) - 1))) + Al))
      (Icc v w) := by
    have hpos : ∀ t ∈ Icc v w, 0 < 1 + mfun t := by
      intro t ht
      have : 0 ≤ mfun t := by
        rw [hmfun]; dsimp only
        split_ifs
        · exact mul_nonneg hc'.le (by linarith [ht.1])
        · exact mul_nonneg hc'.le (by linarith [ht.2])
      linarith
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.add (ContinuousOn.mul continuousOn_const
      (ContinuousOn.mul continuousOn_const (ContinuousOn.rpow_const ?_ (fun t ht => Or.inl (hpos t ht).ne')))) continuousOn_const)
    rw [hmfun]
    by_cases huv : u ≤ v
    · simp only [huv, if_true]; fun_prop
    · simp only [huv, if_false]; fun_prop
  have houter : (∫ t in Icc v w, ∫ s in Icc l u, ‖rungSum L c (cutW L a b) S lam ν (s, t)‖) ≤
      ∫ t in Icc v w, (16 * c)⁻¹ * (A2 * (K * (1 + mfun t) ^ (-((d : ℝ) - 1))) + Al) := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun t => integral_nonneg (fun s => norm_nonneg _)))
      (hcont.integrableOn_Icc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hinner t ht
  have hA2 : 0 ≤ A2 := by positivity
  have hAl : 0 ≤ Al := by positivity
  have hdecay : (∫ t in Icc v w, (1 + mfun t) ^ (-((d : ℝ) - 1))) ≤ (16 * c)⁻¹ := by
    by_cases huv : u ≤ v
    · have := outer_decay hd hc' hvw
      simpa only [hmfun, huv, if_true] using this
    · have := outer_decay_rev hd hc' hvw
      simpa only [hmfun, huv, if_false] using this
  have hgcont : ContinuousOn (fun t : ℝ => (1 + mfun t) ^ (-((d : ℝ) - 1))) (Icc v w) := by
    have hpos : ∀ t ∈ Icc v w, 0 < 1 + mfun t := by
      intro t ht
      have : 0 ≤ mfun t := by
        rw [hmfun]; dsimp only
        split_ifs
        · exact mul_nonneg hc'.le (by linarith [ht.1])
        · exact mul_nonneg hc'.le (by linarith [ht.2])
      linarith
    refine ContinuousOn.rpow_const ?_ (fun t ht => Or.inl (hpos t ht).ne')
    rw [hmfun]
    by_cases huv : u ≤ v
    · simp only [huv, if_true]; fun_prop
    · simp only [huv, if_false]; fun_prop
  have hgint : IntegrableOn (fun t : ℝ => (1 + mfun t) ^ (-((d : ℝ) - 1))) (Icc v w) :=
    hgcont.integrableOn_Icc
  have hvol : (∫ _t in Icc v w, (1 : ℝ)) = w - v := by
    simp [Real.volume_Icc, Measure.real, ENNReal.toReal_ofReal (sub_nonneg.mpr hvw)]
  have hRHS : (∫ t in Icc v w, (16 * c)⁻¹ * (A2 * (K * (1 + mfun t) ^ (-((d : ℝ) - 1))) + Al)) =
      (16 * c)⁻¹ * (A2 * K * (∫ t in Icc v w, (1 + mfun t) ^ (-((d : ℝ) - 1))) + Al * (w - v)) := by
    rw [integral_const_mul, integral_add (hgint.const_mul K |>.const_mul A2) (integrableOn_const (μ := volume) (s := Icc v w) (by simp [Real.volume_Icc])),
      integral_const_mul, integral_const_mul]
    simp [Real.volume_Icc, Measure.real, ENNReal.toReal_ofReal (sub_nonneg.mpr hvw), mul_assoc]
    left; ring
  have hK0 : 0 ≤ K := by positivity
  have hmain : (∫ t in Icc v w, (16 * c)⁻¹ * (A2 * (K * (1 + mfun t) ^ (-((d : ℝ) - 1))) + Al)) ≤
      (16 * c)⁻¹ * (A2 * K * (16 * c)⁻¹ + Al * (w - v)) := by
    rw [hRHS]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA2 hK0)
    linarith
  refine houter.trans (hmain.trans ?_)
  have hrp : L' ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η) =
      L' ^ (2 * d) * L' ^ (-2 * ((d : ℝ) - 1) * (1 - γ) + η) := by
    rw [show 2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η =
      ((2 * d : ℕ) : ℝ) + (-2 * ((d : ℝ) - 1) * (1 - γ) + η) by push_cast; ring,
      Real.rpow_add hL'p, Real.rpow_natCast]
  simp only [A2, Al, hrp]
  have hX : 0 ≤ L' ^ (2 * d) := by positivity
  have hY : 0 ≤ (16 * c)⁻¹ := by positivity
  have hZ : 0 ≤ L' ^ (-2 * ((d : ℝ) - 1) * (1 - γ) + η) := Real.rpow_nonneg hL'p.le _
  have hw0 : 0 ≤ w - v := sub_nonneg.mpr hvw
  have hCw0 : 0 ≤ Cw * (Real.sqrt 2) ^ d * K := by positivity
  nlinarith [mul_nonneg (mul_nonneg hX hY) hY, mul_nonneg (mul_nonneg (mul_nonneg hX hY) hZ) hw0,
    mul_nonneg hCw0 (mul_nonneg (mul_nonneg hX hY) hY), mul_nonneg hCm (mul_nonneg (mul_nonneg (mul_nonneg hX hY) hZ) hw0)]

end WaveTurbulence.LadderDecay
