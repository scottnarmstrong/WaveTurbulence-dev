/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FiltLink.Present
public import WaveTurbulence.Foundations.Incoh.LinkMassBounds
public import WaveTurbulence.Foundations.Incoh.ShortTimeBox
public import WaveTurbulence.Foundations.Incoh.LongTimeBox
/-! # D5a FILT-LINK: time-shifted literal pair masses (o82 Lemma 14.1, proof)

For a time shift `c` (`r = μ(u − v) + c`, o82's `r = μz + τ`), the literal link mass on its layer box is bounded by
`(1 + L|c|)²` times main's factored one-link bounds (`Incoh.exists_linkMass_bounds`), with a new base constant
`C₀ + 5^{2d}`:
- `|c| ≤ Dμ`: main's short/long split on the window `2Dμ`. The short and long profiles are transported to the
  shifted box with unchanged masses (translation invariance); in the incoherent case the first moment of the shifted
  short profile is `∫ |r − c| short ≤ (1 + |c|) C L^{2d}` (o82: "`ℓ(z) ≤ |z|` … `∫ (1 + |τ|) d|ω_M|`").
- `|c| > Dμ`: the trivial supremum `(5L)^{2d}` on the unit box, paid by `(1 + L|c|)² ≥ (Lμ)²` (o82's moment
  tail), for `L ≥ δ⁻¹`.

The scalar layer separation is main's private `Incoh.ShortTimeBox.scalar_layer_separation`, copied by source
(COPIED-SHA256SUMS). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Flower.FiltLink
open WaveTurbulence.Incoh

variable {d : ℕ}

/-- Main's `Incoh.ShortTimeBox.scalar_layer_separation` (private there), copied by source. -/
theorem scalar_layer_separation {a b : ℤ} (hab : a ≠ b) :
    ∃ q : ℝ,
      ((∀ x ∈ Icc (a : ℝ) (a + 1), x ≤ q) ∧ (∀ y ∈ Icc (b : ℝ) (b + 1), q ≤ y)) ∨
      ((∀ x ∈ Icc (a : ℝ) (a + 1), q ≤ x) ∧ (∀ y ∈ Icc (b : ℝ) (b + 1), y ≤ q)) := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hc : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    exact ⟨b, Or.inl ⟨fun _ hx => hx.2.trans hc, fun _ hy => hy.1⟩⟩
  · have hc : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    exact ⟨a, Or.inr ⟨fun _ hx => hx.1, fun _ hy => hy.2.trans hc⟩⟩

/-- Main's box transport `lintegral_layerBox_profile_le` at a shifted frequency (translation invariance). -/
theorem lintegral_layerBox_shift_le (Q : LayerLink d) {lam : ℝ} (hlam : 0 < lam) (c : ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t in linkBox Q, f (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c)) ≤
      ENNReal.ofReal lam⁻¹ * ∫⁻ r, f r := by
  have h := lintegral_layerBox_profile_le Q hlam (f := fun r => f (r + c)) (hf.comp (measurable_id.add_const c))
  rwa [lintegral_add_right_eq_self] at h

/-- The shifted incoherent short-time box bound: first moment `∫ |r − c| short ≤ (1 + |c|) C L^{2d}`. -/
theorem exists_shortTime_shift_incoherent (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ lam : ℝ, 0 < lam → ∀ Q : LayerLink d, Q.IsIncoherent →
      ∀ c : ℝ, (∫⁻ t in linkBox Q,
          shortLinkProfile L Q.toLinkParameters (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c)) ≤
        (ENNReal.ofReal lam⁻¹) ^ 2 * ENNReal.ofReal (C * L ^ (2 * d) * (1 + |c|)) := by
  obtain ⟨C, hC, hb⟩ := exists_shortLinkProfile_moments_bound d hd
  refine ⟨C, hC, ?_⟩
  intro L hL lam hlam Q hQ c
  have hLp := zero_lt_one.trans_le hL
  let I := Icc (Q.leftLayer : ℝ) ((Q.leftLayer : ℝ) + 1)
  let J := Icc (Q.rightLayer : ℝ) ((Q.rightLayer : ℝ) + 1)
  let sp : ℝ → ℝ≥0∞ := shortLinkProfile L Q.toLinkParameters
  have hsp : Measurable sp := measurable_shortLinkProfile hLp _
  let g : ℝ → ℝ≥0∞ := fun r => sp (r + c)
  have hg : Measurable g := hsp.comp (measurable_id.add_const c)
  let f : ℝ → ℝ≥0∞ := fun r => g ((((-Q.orientation) : ℤ) : ℝ) * r)
  have hf : Measurable f := hg.comp (measurable_const.mul measurable_id)
  have hcoord : (∫⁻ t in linkBox Q, sp (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c)) =
      ∫⁻ z : ℝ × ℝ, (I ×ˢ J).indicator (fun z => f (lam * (z.2 - z.1))) z := by
    rw [lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)]
    calc
      _ = ∫⁻ t in linkBox Q, f (lam * (t 1 - t 0)) := by
        apply lintegral_congr
        intro t
        simp only [f, g, Int.cast_neg]
        congr 1
        ring
      _ = _ := setLIntegral_twoTimeBox _ _ _ _ (fun z => f (lam * (z.2 - z.1)))
  have hmom : (∫⁻ r, f r * ENNReal.ofReal |r|) ≤ ENNReal.ofReal (C * L ^ (2 * d) * (1 + |c|)) := by
    have h1 : (∫⁻ r, f r * ENNReal.ofReal |r|) = ∫⁻ r, g r * ENNReal.ofReal |r| :=
      lintegral_firstMoment_intUnit_mul (-Q.orientation) g
    have h2 : (∫⁻ r, g r * ENNReal.ofReal |r|) = ∫⁻ r, sp r * ENNReal.ofReal |r - c| := by
      have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun r => sp r * ENNReal.ofReal |r - c|) c
      simpa only [add_sub_cancel_right] using h
    have hCL : 0 ≤ C * L ^ (2 * d) := by positivity
    rw [h1, h2]
    calc
      _ ≤ ∫⁻ r, (sp r * ENNReal.ofReal |r| + sp r * ENNReal.ofReal |c|) := by
        apply lintegral_mono
        intro r
        dsimp only
        rw [← mul_add, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        gcongr
        have h := abs_add_le r (-c)
        rwa [abs_neg, ← sub_eq_add_neg] at h
      _ = (∫⁻ r, sp r * ENNReal.ofReal |r|) + (∫⁻ r, sp r) * ENNReal.ofReal |c| := by
        rw [lintegral_add_left (f := fun r => sp r * ENNReal.ofReal |r|)
            (hsp.mul (ENNReal.measurable_ofReal.comp continuous_abs.measurable)),
          lintegral_mul_const _ hsp]
      _ ≤ ENNReal.ofReal (C * L ^ (2 * d)) + ENNReal.ofReal (C * L ^ (2 * d)) * ENNReal.ofReal |c| :=
        add_le_add (hb L hL _).2 (mul_le_mul' (hb L hL _).1 le_rfl)
      _ = _ := by
        rw [← ENNReal.ofReal_mul hCL, ← ENNReal.ofReal_add hCL (mul_nonneg hCL (abs_nonneg c))]
        congr 1
        ring
  obtain ⟨q, hsep⟩ := scalar_layer_separation (show Q.leftLayer ≠ Q.rightLayer from hQ)
  change (∫⁻ t in linkBox Q, sp (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c)) ≤ _
  rw [hcoord]
  exact (lintegral_scaled_difference_box_le_firstMoment measurableSet_Icc measurableSet_Icc hsep hlam hf).trans
    (mul_le_mul' le_rfl hmom)

/-- The trivial bound on a unit layer box. -/
theorem lintegral_shift_trivial {L : ℝ} (hL : 1 ≤ L) (lam : ℝ) (Q : LayerLink d) (c : ℝ) :
    (∫⁻ t in linkBox Q,
        ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c) Q.toLinkParameters‖ₑ) ≤
      ENNReal.ofReal ((5 * L) ^ (2 * d)) := by
  calc
    _ ≤ ∫⁻ _t in linkBox Q, ENNReal.ofReal ((5 * L) ^ (2 * d)) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_linkLatticeSum_le hL _ _)
    _ = _ := by rw [setLIntegral_const, volume_linkBox, mul_one]

/-- **Shifted one-link bounds**: main's `exists_linkMass_bounds` at every time shift `c`, times `(1 + L|c|)²`. -/
theorem exists_shift_linkMass_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₁ L₀ : ℝ, 0 < C₁ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ Q : LayerLink d,
        |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ D → ∀ c : ℝ,
        ((∫⁻ t in linkBox Q, ‖linkLatticeSum L
            (((Q.orientation : ℤ) : ℝ) * (δ * L ^ (2 * γ)) * (t 0 - t 1) + c) Q.toLinkParameters‖ₑ) ≤
          ENNReal.ofReal ((1 + L * |c|) ^ 2) * ENNReal.ofReal ((δ * L ^ (2 * γ))⁻¹ *
            (C₀ * L ^ (2 * d) + C₁ * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)))) ∧
        (Q.IsIncoherent → (∫⁻ t in linkBox Q, ‖linkLatticeSum L
            (((Q.orientation : ℤ) : ℝ) * (δ * L ^ (2 * γ)) * (t 0 - t 1) + c) Q.toLinkParameters‖ₑ) ≤
          ENNReal.ofReal ((1 + L * |c|) ^ 2) * ENNReal.ofReal (((δ * L ^ (2 * γ))⁻¹) ^ 2 * (C₀ * L ^ (2 * d)) +
            (δ * L ^ (2 * γ))⁻¹ * (C₁ * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)))) := by
  obtain ⟨Cs, hCs, hmom⟩ := exists_shortLinkProfile_moments_bound d hd
  obtain ⟨Ci, hCi, hinc⟩ := exists_shortTime_shift_incoherent d hd
  set C₀ : ℝ := Cs + Ci + 5 ^ (2 * d) with hC₀def
  refine ⟨C₀, by positivity, ?_⟩
  intro γ hγ η hη δ hδ D hD
  obtain ⟨C₁, L₁, hC₁, hL₁, hlong⟩ :=
    exists_longLinkProfile_mass_bound d hd γ hγ η hη (2 * D * δ) (by positivity)
  refine ⟨C₁, max L₁ δ⁻¹, hC₁, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL Q hspan c
  have hLa : L₁ ≤ L := (le_max_left _ _).trans hL
  have hLδ : δ⁻¹ ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := hL₁.trans hLa
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  set lam : ℝ := δ * L ^ (2 * γ) with hlamdef
  have hlam : 0 < lam := by positivity
  have hD1 : 1 ≤ D := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hspan
  set e : ℝ := 2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η
  have hLe : 0 ≤ C₁ * L ^ e := by positivity
  have hL2d : 0 ≤ L ^ (2 * d) := by positivity
  have hw1 : 1 ≤ (1 + L * |c|) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  have hw2 : 1 + |c| ≤ (1 + L * |c|) ^ 2 := by
    have h : 1 + |c| ≤ 1 + L * |c| := by nlinarith [abs_nonneg c]
    nlinarith [abs_nonneg c, mul_nonneg hLp.le (abs_nonneg c)]
  have hlaminv : 0 ≤ lam⁻¹ := (inv_pos.mpr hlam).le
  -- the window and the trivial region
  by_cases hc : |c| ≤ D * lam
  · set R : ℝ := (2 * D * δ) * L ^ (2 * γ)
    have hRw : ∀ t ∈ linkBox Q, |((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c| ≤ R := by
      intro t ht
      have h := abs_layerFrequency_le Q hlam.le hspan ht
      calc
        _ ≤ |((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1)| + |c| := abs_add_le _ _
        _ ≤ D * lam + D * lam := add_le_add h hc
        _ = R := by simp only [R, hlamdef]; ring
    have hshortM : Measurable fun t : Fin 2 → ℝ =>
        shortLinkProfile L Q.toLinkParameters (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c) :=
      (measurable_shortLinkProfile hLp _).comp (by fun_prop)
    have hsplit : (∫⁻ t in linkBox Q,
          ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c) Q.toLinkParameters‖ₑ) ≤
        (∫⁻ t in linkBox Q, shortLinkProfile L Q.toLinkParameters
            (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c)) +
          ∫⁻ t in linkBox Q, longLinkProfile L R Q.toLinkParameters
            (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c) := by
      calc
        _ ≤ ∫⁻ t in linkBox Q, (shortLinkProfile L Q.toLinkParameters
              (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c) +
            longLinkProfile L R Q.toLinkParameters (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c)) :=
          setLIntegral_mono' measurableSet_Icc fun t ht =>
            enorm_link_le_short_add_long L R _ _ (hRw t ht)
        _ = _ := lintegral_add_left hshortM _
    have hlongB : (∫⁻ t in linkBox Q, longLinkProfile L R Q.toLinkParameters
          (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c)) ≤
        ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (C₁ * L ^ e) :=
      (lintegral_layerBox_shift_le Q hlam c (measurable_longLinkProfile hLp _ _)).trans
        (mul_le_mul' le_rfl (hlong L hLa Q.toLinkParameters))
    constructor
    · have hshortB : (∫⁻ t in linkBox Q, shortLinkProfile L Q.toLinkParameters
            (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c)) ≤
          ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (Cs * L ^ (2 * d)) :=
        (lintegral_layerBox_shift_le Q hlam c (measurable_shortLinkProfile hLp _)).trans
          (mul_le_mul' le_rfl (hmom L hL1 Q.toLinkParameters).1)
      refine hsplit.trans ((add_le_add hshortB hlongB).trans ?_)
      rw [← ENNReal.ofReal_mul hlaminv, ← ENNReal.ofReal_mul hlaminv,
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hCs : Cs ≤ C₀ := by simp only [hC₀def]; linarith [hCi.le, show (0 : ℝ) ≤ 5 ^ (2 * d) by positivity]
      calc
        _ ≤ lam⁻¹ * (C₀ * L ^ (2 * d) + C₁ * L ^ e) := by
          rw [← mul_add]; gcongr
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hw1
    · intro hQ
      have hshortB := hinc L hL1 lam hlam Q hQ c
      refine hsplit.trans ((add_le_add hshortB hlongB).trans ?_)
      rw [← ENNReal.ofReal_pow hlaminv, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hlaminv, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hCi' : Ci ≤ C₀ := by simp only [hC₀def]; linarith [hCs.le, show (0 : ℝ) ≤ 5 ^ (2 * d) by positivity]
      have ha : 0 ≤ lam⁻¹ ^ 2 * L ^ (2 * d) := by positivity
      have hb : 0 ≤ lam⁻¹ * (C₁ * L ^ e) := by positivity
      calc
        lam⁻¹ ^ 2 * (Ci * L ^ (2 * d) * (1 + |c|)) + lam⁻¹ * (C₁ * L ^ e)
            = Ci * (lam⁻¹ ^ 2 * L ^ (2 * d)) * (1 + |c|) + lam⁻¹ * (C₁ * L ^ e) := by ring
        _ ≤ C₀ * (lam⁻¹ ^ 2 * L ^ (2 * d)) * (1 + L * |c|) ^ 2 +
              lam⁻¹ * (C₁ * L ^ e) * (1 + L * |c|) ^ 2 :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right hCi' ha) hw2 (by positivity) (by positivity))
            (le_mul_of_one_le_right hb hw1)
        _ = _ := by ring
  · -- the trivial region `|c| > Dμ`
    have hcl : L * lam ≤ 1 + L * |c| := by
      have h1 : lam ≤ D * lam := le_mul_of_one_le_left hlam.le hD1
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans (le_of_lt (not_le.mp hc))) hLp.le]
    have hsq : (L * lam) ^ 2 ≤ (1 + L * |c|) ^ 2 := pow_le_pow_left₀ (by positivity) hcl 2
    have h5 : (5 * L) ^ (2 * d) = 5 ^ (2 * d) * L ^ (2 * d) := mul_pow _ _ _
    have h5n : (0 : ℝ) ≤ 5 ^ (2 * d) := by positivity
    have h5C : 5 ^ (2 * d) ≤ C₀ := by simp only [hC₀def]; linarith [hCs.le, hCi.le]
    refine ⟨(lintegral_shift_trivial hL1 lam Q c).trans ?_, fun _ => (lintegral_shift_trivial hL1 lam Q c).trans ?_⟩
    · rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      -- `L² μ ≥ 1` from `L ≥ δ⁻¹`, `L ≥ 1`
      have hL2lam : 1 ≤ L ^ 2 * lam := by
        have hLg : 1 ≤ L ^ (2 * γ) := Real.one_le_rpow hL1 (by linarith [hγ.1])
        have hδL : 1 ≤ δ * L := by
          have := mul_le_mul_of_nonneg_left hLδ hδ.le
          rwa [mul_inv_cancel₀ hδ.ne'] at this
        have hLL : L ≤ L ^ 2 := by nlinarith
        calc
          (1 : ℝ) ≤ δ * L := hδL
          _ ≤ δ * L ^ 2 := by gcongr
          _ ≤ δ * L ^ 2 * L ^ (2 * γ) := le_mul_of_one_le_right (by positivity) hLg
          _ = L ^ 2 * lam := by simp only [hlamdef]; ring
      have hlamle : lam ≤ (L * lam) ^ 2 := by
        calc
          lam = lam * 1 := (mul_one _).symm
          _ ≤ lam * (L ^ 2 * lam) := mul_le_mul_of_nonneg_left hL2lam hlam.le
          _ = (L * lam) ^ 2 := by ring
      calc
        (5 * L) ^ (2 * d) = lam * lam⁻¹ * (5 ^ (2 * d) * L ^ (2 * d)) := by
          rw [mul_inv_cancel₀ hlam.ne', one_mul, h5]
        _ ≤ (1 + L * |c|) ^ 2 * (lam⁻¹ * (C₀ * L ^ (2 * d) + C₁ * L ^ e)) := by
          rw [mul_assoc]
          apply mul_le_mul (hlamle.trans hsq) _ (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ hlaminv
          nlinarith
    · rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hlam2 : lam ^ 2 ≤ (L * lam) ^ 2 := by
        have : lam ≤ L * lam := le_mul_of_one_le_left hlam.le hL1
        exact pow_le_pow_left₀ hlam.le this 2
      calc
        (5 * L) ^ (2 * d) = lam ^ 2 * lam⁻¹ ^ 2 * (5 ^ (2 * d) * L ^ (2 * d)) := by
          rw [← mul_pow, mul_inv_cancel₀ hlam.ne', one_pow, one_mul, h5]
        _ ≤ (1 + L * |c|) ^ 2 * (lam⁻¹ ^ 2 * (C₀ * L ^ (2 * d)) + lam⁻¹ * (C₁ * L ^ e)) := by
          rw [mul_assoc]
          apply mul_le_mul (hlam2.trans hsq) _ (by positivity) (by positivity)
          · have : lam⁻¹ ^ 2 * (5 ^ (2 * d) * L ^ (2 * d)) ≤ lam⁻¹ ^ 2 * (C₀ * L ^ (2 * d)) := by gcongr
            nlinarith [mul_nonneg hlaminv hLe]

end WaveTurbulence.Flower.FiltLink
