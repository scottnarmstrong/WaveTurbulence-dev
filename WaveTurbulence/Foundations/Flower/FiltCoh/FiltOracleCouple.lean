/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltWickCouple
public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleStarBound
public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiGlue

/-! # FILT-COH (d2e): layer-zero couples with star weights and both filter layers

`exists_couple_filt_bound_theta`: for a layer-zero regular couple with separately normalized leaf profiles, ANY star
weights (`StarPresented (30d)`) and two filter layers with scales `M, Mu ≥ L`, the kernel with D5's multiplier
`d5Mult S ω F ann M Fu Mu` has `X^{θ,30d,30d}` norm `≤ Ck (Ck δ)^n ∏ cω`, every `θ ≤ 1 - η/8`, order `n > 0`.

Route (o82 Prop. 15.1 with Thm 10.1 (10.5)): FILT-SRC's `couple_starFiltWeight_eq` writes the multiplier on the
lattice as the star presentation value times the array filter; the presentation integral is swapped with the lattice
sum (`couple_filt_swap`, a bounded coefficient); per presentation point, `couple_filt_global` gives the source profile
of the filtered scalar, bounded uniformly in the modulations and filters (`filt_scalar_envelope`); then FiltCoh's
star leaf engine and budget. Proofs adapted from FiltCoh's `CoupleEnvelopeU`, `CoupleStarMix`, `CoupleStarBound`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure)
open scoped ENNReal

variable {d : ℕ}

attribute [-instance] WaveTurbulence.Mole.instFintypePositionCode

/-- **The whole filtered scalar at weight `θ`, uniformly in the modulations and the filters.** -/
theorem filt_scalar_envelope (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8)
    {Agev Cbase : ℝ} (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) {K : ℝ} (hK : 1 ≤ K) (Nf : ℕ) :
    ∃ Kr Cm : ℝ, 0 < Kr ∧ 1 ≤ Cm ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ Q : RegCpl, 0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*Q.links.length+1)) (C Z)) →
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤ ENNReal.ofReal Cm^Q.links.length ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
          (β γ' : Fin Q.links.length → Mom d) (ψ : Fin Q.links.length → ℝ → ℂ), (∀ j, FiltMul d K Nf (ψ j)) →
          ‖filtScalar L δ γ Q ζ C ψ lam β γ' z‖ ≤
            (2*(Kr*δ)^Q.links.length)*B lam := by
  classical
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨Ks,hKs,hS⟩ := physical_sum_envelope_theta_filt hd hγ hη0 hη hηγ hK Nf
  obtain ⟨Kw,hKw,hW⟩ := wick_correction_envelope_theta_filt hd hγ hη0 hη hηγ hK Nf Agev hAgev
  set Cw : ℝ := 4*(3*(1+2*coefficientGevreyMass (4*Agev)+gaussianWeightedMass θ)*Cbase^5) with hCwdef
  have hU := coefficientGevreyMass_nonneg (by positivity : 0 ≤ 4*Agev)
  have hV := gaussianWeightedMass_nonneg θ
  have hCw : 0 ≤ Cw := by
    rw [hCwdef]
    have := pow_nonneg (zero_le_one.trans hCbase) 5
    have : 0 ≤ 1+2*coefficientGevreyMass (4*Agev)+gaussianWeightedMass θ := by linarith
    positivity
  refine ⟨max Ks Kw, max 1 (4*Cw), lt_of_lt_of_le hKs (le_max_left _ _), le_max_left _ _, ?_⟩
  intro Aorder
  obtain ⟨LS,hS⟩ := hS Aorder
  obtain ⟨LW,hW⟩ := hW Aorder
  refine ⟨max 2 (max LS LW),?_⟩
  intro L hL δ hδ hδ1 Q hn hnlog C hC ζ hζ
  set n := Q.links.length with hndef
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLS : LS ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLW : LW ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < L) (-(η/2))).trans_le hδ
    linarith only [hh]
  have hmainθ (Z : (chosenSet Q.links).powerset) (j : ℕ) :
      ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm j (C Z) α lam ≤ gev (Cbase^(4*n+1)) Agev j := by
    apply le_trans _ ((hC Z).norm j)
    apply lintegral_mono
    intro α
    apply lintegral_mono
    intro lam
    exact mul_le_mul' (temporalWeight_mono hθ lam) le_rfl
  have hwick := wickCoefficientMass_le_geometric hn hθ1 hAgev hCbase
  have hrate : ENNReal.ofReal (L^(-gamma1 d γ)) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_one_of_one_le_of_nonpos hL1
    have : 0 ≤ gamma1 d γ := by
      unfold gamma1
      have h1 : 0 ≤ 2*γ := by linarith [hγ.1]
      have h2 : (0:ℝ) ≤ 2*((d:ℝ)-1)*(1-γ) := by
        have h3 : (0:ℝ) ≤ (d:ℝ)-1 := by
          have : (3:ℝ) ≤ d := by exact_mod_cast hd
          linarith
        have h4 : 0 ≤ 1-γ := by linarith [hγ.2]
        have := mul_nonneg h3 h4
        linarith
      exact le_min h1 (le_min zero_le_one h2)
    linarith
  have hex (Z : (chosenSet Q.links).powerset) :
      ∃ BN BW : (ℝ × ℝ) → ℝ,
        Measurable BN ∧ Measurable BW ∧ (∀ lam, 0 ≤ BN lam) ∧ (∀ lam, 0 ≤ BW lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (BN lam)) ≤ ENNReal.ofReal Cw^n ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (BW lam)) ≤ ENNReal.ofReal Cw^n ∧
        (∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
          (ψ : Fin n → ℝ → ℂ), (∀ j, FiltMul d K Nf (ψ j)) →
          ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
            approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
              (filtRes (RA1Leafwise.markedLinkIndices Q Z.val) (fun Ω => C Z (ofLp Ω) lam) ψ)‖ ≤
            2*(Ks*δ)^n*BN lam) ∧
        (∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
          (ψ : Fin n → ℝ → ℂ), (∀ j, FiltMul d K Nf (ψ j)) →
          ‖filtWickCorrection L (2*δ) γ ψ z β γ' (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam‖ ≤
            2*(Kw*(2*δ))^n*BW lam) := by
    have hSZ := hC Z
    obtain ⟨BN,hmN,hpN,hbN,hgN⟩ := hS L hLS δ hδ hδ1 n hnlog (RA1Leafwise.markedLinkIndices Q Z.val) (C Z)
      hSZ.reg θ _ Agev hθ0 hθ1 hSZ.nonneg hAgev (hmainθ Z)
    obtain ⟨BW,hmW,hpW,hbW,hgW⟩ := hW L hLW (2*δ) hδ hδ1 n hnlog (RA1Leafwise.markedLinkIndices Q Z.val)
      (C Z) hSZ.reg θ _ hθ0 hθ1 hSZ.nonneg (hmainθ Z)
    refine ⟨BN,BW,hmN,hmW,hpN,hpW,?_,?_,hgN,hgW⟩
    · exact hbN.trans ((sum_mass_le_wick_mass n hSZ.nonneg hAgev _).trans hwick)
    · refine hbW.trans (le_trans ?_ hwick)
      calc (4:ℝ≥0∞)^n*ENNReal.ofReal (L^(-gamma1 d γ))*_
          ≤ (4:ℝ≥0∞)^n*1*_ := by gcongr
        _ = _ := by rw [mul_one]
  choose BN BW hmN hmW hpN hpW hbN hbW hgN hgW using hex
  let B := fun lam => ∑ Z : (chosenSet Q.links).powerset, (BN Z lam+BW Z lam)
  have hmB : Measurable B := Finset.measurable_sum _ (fun Z _ => (hmN Z).add (hmW Z))
  have hpB (lam : ℝ × ℝ) : 0 ≤ B lam :=
    Finset.sum_nonneg (fun Z _ => add_nonneg (hpN Z lam) (hpW Z lam))
  have hsize : Q.size = 2*n := by
    rw [hndef]
    have hh := couple_linksAt_length Q ((0:Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  have hcard : Fintype.card ((chosenSet Q.links).powerset) = 2^n := by
    rw [Fintype.card_coe,coefficient_index_card hsize]
  have hbB : (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤ ENNReal.ofReal (max 1 (4*Cw))^n := by
    apply (weighted_scalar_envelope_sum_le θ BN BW hmN hmW hpN hpW hbN hbW).trans
    rw [hcard,Nat.cast_pow,Nat.cast_ofNat]
    have hh := powerset_error_mass_le hn (C := Cw) 1
    simp only [one_mul] at hh
    exact hh.trans (pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (le_max_right _ _)) n)
  refine ⟨B,hmB,hpB,hbB,?_⟩
  have haN := ae_all_iff.mpr hgN
  have haW := ae_all_iff.mpr hgW
  filter_upwards [haN,haW] with lam hN hW
  intro z β γ' ψ hψ
  have hH : (0:ℝ) ≤ 2 := by norm_num
  set K' := max Ks Kw
  have hKs' : (Ks*δ)^n ≤ (K'*δ)^n :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le) n
  have hKw' : ((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n ≤ (K'*δ)^n := by
    rw [← inv_pow, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : Kw ≤ K' := le_max_right _ _
    nlinarith [hKw.le, hδpos.le]
  have hZ (Z : (chosenSet Q.links).powerset) :
      ‖filtCellSymbol L δ γ ψ z β γ' (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam‖ ≤
        2*(K'*δ)^n*(BN Z lam+BW Z lam) := by
    rw [filtCellSymbol_eq_sum_add_wick (by linarith : (0:ℝ) < L)]
    refine (norm_add_le _ _).trans ?_
    have hw' : ∀ w : ℂ, ‖((4:ℂ)^n)⁻¹ * w‖ = ((4:ℝ)^n)⁻¹ * ‖w‖ := fun w => by
      rw [norm_mul, norm_inv, norm_pow]; norm_num
    rw [hw']
    have h1 := hN Z z β γ' ψ hψ
    have h2 := hW Z z β γ' ψ hψ
    have hw : ((4:ℝ)^n)⁻¹*‖filtWickCorrection L (2*δ) γ ψ z β γ'
        (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam‖ ≤ 2*(K'*δ)^n*BW Z lam := by
      calc _ ≤ ((4:ℝ)^n)⁻¹*(2*(Kw*(2*δ))^n*BW Z lam) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2*(((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n)*BW Z lam := by ring
        _ ≤ 2*(K'*δ)^n*BW Z lam :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKw' hH) (hpW Z lam)
    have hs : ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
          (filtRes (RA1Leafwise.markedLinkIndices Q Z.val) (fun Ω => C Z (ofLp Ω) lam) ψ)‖ ≤
        2*(K'*δ)^n*BN Z lam :=
      h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKs' hH) (hpN Z lam))
    calc _ ≤ 2*(K'*δ)^n*BN Z lam + 2*(K'*δ)^n*BW Z lam := add_le_add hs hw
      _ = _ := by ring
  unfold filtScalar
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hζ (norm_nonneg _)).trans
  rw [one_mul]
  apply (norm_sum_le _ _).trans
  have hB : ((2*(K'*δ)^n))*B lam = ∑ Z : (chosenSet Q.links).powerset, 2*(K'*δ)^n*(BN Z lam+BW Z lam) := by
    simp only [B, Finset.mul_sum]
  rw [hB]
  apply Finset.sum_le_sum
  intro Z _
  rw [norm_mul]
  calc _ ≤ 1*‖filtCellSymbol L δ γ ψ z β γ' (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam‖ :=
        mul_le_mul_of_nonneg_right (RA1Leafwise.norm_original_source_weight_le_one Z.val) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hZ Z

/-- **Multiplier = presentation value × filter ↦ presentation mixture of filtered lattice characters.** -/
theorem couple_filt_swap {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden) {α : Type}
    [MeasurableSpace α] (G : RootMeasure d Q.links.length α) (L : ℝ) (k : Mom d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (w : (Fin Q.links.length × Fin 2 → Fin d → ℤ) → ℂ)
    (hm : ∀ p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
      m (cosetDecoration LG.garden L k
        ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) =
        (G.at k).value (pairedLattice L p) * w p)
    (c : (Fin Q.links.length × Fin 2 → Fin d → ℤ) → ℂ) (g : (Fin Q.links.length × Fin 2 → Fin d → ℤ) → ℂ)
    {D : ℝ} (hc : ∀ p, ‖w p * c p‖ ≤ D) (hg : Summable (fun p => ‖g p‖)) (A : ℂ) :
    A * ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
        m (cosetDecoration LG.garden L k
          ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) * (c p * g p) =
      ∫ a, G.base.amplitude a * IncTop.rootChar (G.root a) k *
        (A * ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          (((Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ) * w p) * c p) * g p)
        ∂G.base.μ := by
  classical
  let F : ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → α → ℂ := fun p a =>
    G.base.amplitude a * IncTop.rootChar (G.root a) k *
      (Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ) * ((w p * c p) * g p)
  have hnorm : ∀ p a, ‖F p a‖ ≤ ‖G.base.amplitude a‖ * (D * ‖g p‖) := by
    intro p a
    simp only [F, norm_mul, IncTop.norm_rootChar, Circle.norm_coe, mul_one]
    have h0 := norm_nonneg (G.base.amplitude a)
    have h1 := norm_nonneg (g p)
    have h2 := hc p
    rw [norm_mul] at h2
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 h1) h0
  have hFm : ∀ p, AEStronglyMeasurable (F p) G.base.μ := by
    intro p
    have h1 : Measurable (fun a => IncTop.rootChar (G.root a) k) := IncTop.measurable_rootChar G.root_measurable k
    have h2 : Measurable (fun a => (Real.fourierChar (inner ℝ (G.base.frequency a) (pairedLattice L p)) : ℂ)) := by
      have hc' : Continuous (fun v : PairedMomentum d Q.links.length =>
          (Real.fourierChar (inner ℝ v (pairedLattice L p)) : ℂ)) := by fun_prop
      exact hc'.measurable.comp G.base.frequency_measurable
    exact (((G.amplitude_measurable.mul h1).mul h2).mul measurable_const).aestronglyMeasurable
  have hFi : ∀ p, Integrable (F p) G.base.μ := fun p =>
    (G.base.amplitude_integrable.norm.mul_const (D * ‖g p‖)).mono' (hFm p) (ae_of_all _ (hnorm p))
  have hFs : Summable (fun p => ∫ a, ‖F p a‖ ∂G.base.μ) := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun a => norm_nonneg _) (fun p => ?_)
      ((hg.mul_left D).mul_left (∫ a, ‖G.base.amplitude a‖ ∂G.base.μ))
    rw [← integral_mul_const]
    exact integral_mono (hFi p).norm (G.base.amplitude_integrable.norm.mul_const _) (hnorm p)
  have hval : ∀ p, m (cosetDecoration LG.garden L k
      ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) * (c p * g p) =
      ∫ a, F p a ∂G.base.μ := by
    intro p
    rw [hm p, IncTop.RootMeasure.at_value, ← integral_mul_const, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [F]
    ring
  simp_rw [hval]
  rw [integral_tsum_of_summable_integral_norm hFi hFs, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [F]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  ring

/-- Integrability of a shifted filtered cell symbol density from its uniform envelope. -/
theorem filt_shifted_symbol_integrable {Q : RegCpl} {LG : LayeredGarden 2} (hQ : Q.Decodes LG.garden)
    (H : LGSpine.LeafProfiles 2 d) {Binput Ccover : ℝ} (hBi : 0 ≤ Binput)
    (hF' : ∀ a, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {L δ γ θ : ℝ} (hLpos : 0 < L) (hθ0 : 0 ≤ θ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (hCm : StronglyMeasurable (Function.uncurry C)) (ψ : Fin Q.links.length → ℝ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    {BZ : (ℝ × ℝ) → ℝ}
    (hm : Measurable BZ) (hp : ∀ lam, 0 ≤ BZ lam) (hfin : (∫⁻ lam, wL θ lam*ENNReal.ofReal (BZ lam)) < ⊤)
    (hg : ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin Q.links.length → Mom d), ‖filtCellSymbol L δ γ ψ z β γ' J C lam‖ ≤ r*BZ lam)
    (ν : PairedMomentum d Q.links.length) (k : Mom d) (hd : 1 ≤ d) :
    Integrable (fun q => RA1Leafwise.maskedLeafScalarDensity hQ hQ.1
        (fun lam β γ' z => filtCellSymbol L δ γ ψ z (shiftL β ν 0) (shiftL γ' ν 1) J C lam)
        (RA1Leafwise.leafFam hQ hQ.1 H) S q k)
      (volume.prod (RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
  have hmZ : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
      filtCellSymbol L δ γ ψ z (shiftL p.2.1 ν 0) (shiftL p.2.2 ν 1) J C p.1) := fun z =>
    stronglyMeasurable_shift_fixed (fun lam β γ' z => filtCellSymbol L δ γ ψ z β γ' J C lam) z
      (stronglyMeasurable_filtCellSymbol_joint hLpos δ γ ψ J hCm z) ν
  refine integrable_density_of_env hQ hQ.1
    (fun lam β γ' z => filtCellSymbol L δ γ ψ z (shiftL β ν 0) (shiftL γ' ν 1) J C lam) hmZ
    (K := 40*d) (M := 40*d) (by omega) (by omega) hBi hF' S hcard hθ0 hr hm hp hfin ?_ k
  filter_upwards [hg] with lam h z β γ'
  exact h z _ _

/-- **The exact star-and-filter identity of a layer-zero couple.** -/
theorem couple_filt_kernel_eq {Q : RegCpl} {LG : LayeredGarden 2} (hQ : Q.Decodes LG.garden)
    (h0 : ∀ a, LG.layer a = 0) (H : LGSpine.LeafProfiles 2 d) {Binput Ccover : ℝ} (hBi : 0 ≤ Binput)
    (hF' : ∀ a, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal Binput)
    {L : ℝ} (hL1 : 1 ≤ L) (γ δ : ℝ) (hd : 1 ≤ d)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    (hcover : ∀ c k x, (coupleMomentumData hQ hQ.1).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {α : Type} [MeasurableSpace α] (Gm : RootMeasure d Q.links.length α) (R : α → SymFam Q d)
    (φ : Fin Q.links.length → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ j u, ‖φ j u‖ ≤ Bφ)
    (hD : ∀ (a : α) (t : Fin 2 → ℝ), (∀ i, t i ∈ Icc (0:ℝ) 1) → ∀ k : Mom d,
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          (((Real.fourierChar (inner ℝ (Gm.base.frequency a) (pairedLattice L p)) : ℂ) *
            FiltSrc.arrayFiltWeight L φ p) *
            RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ (t 0) (t 1) k p) *
          (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
            (fun i j => latticePoint L (p (i,j))) =
        RA1Leafwise.sourceScalarProfile hQ hQ.1 (R a) (RA1Leafwise.leafFam hQ hQ.1 H) S ![t 0, t 1] k)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (hm : ∀ k (p : (Fin Q.links.length × Fin 2) → Fin d → ℤ),
      m (cosetDecoration LG.garden L k
        ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) =
        (Gm.at k).value (pairedLattice L p) * FiltSrc.arrayFiltWeight L φ p)
    (hint : ∀ k : Mom d, Integrable (fun q => starDensity hQ hQ.1 R (RA1Leafwise.leafFam hQ hQ.1 H) S
      Gm.base.amplitude Gm.root q k)
      (volume.prod ((RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod Gm.base.μ)))
    (t : Fin 2 → ℝ) (ht : ∀ i, t i ∈ Icc (0:ℝ) 1) (k : Mom d) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t 0 else t 1) 0 k
        (fun _ => 0) 0 m =
      pairedInverseProfile (fun lam => ∫ u, starDensity hQ hQ.1 R (RA1Leafwise.leafFam hQ hQ.1 H) S
          Gm.base.amplitude Gm.root (lam, u) k
          ∂(RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod Gm.base.μ) t := by
  rw [kernelLeavesW_couple_lattice L γ δ H LG hQ (t 0) (t 1) k m]
  have hc : ∀ p, ‖FiltSrc.arrayFiltWeight L φ p *
      RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ (t 0) (t 1) k p‖ ≤ Bφ^Q.links.length := by
    intro p
    rw [norm_mul]
    have h1 := FiltSrc.norm_arrayFiltWeight_le L φ hφ p
    have h2 := RA1Leafwise.norm_coupleLatticeTimeCoefficient_le_one L γ δ LG h0 hQ (ht 0).2 (ht 1).2 k p
    calc _ ≤ Bφ^Q.links.length * 1 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := mul_one _
  rw [couple_filt_swap hQ Gm L k m (FiltSrc.arrayFiltWeight L φ) (hm k)
    (fun p => RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ (t 0) (t 1) k p)
    (fun p => (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
      (fun i j => latticePoint L (p (i,j)))) hc
    ((coupleMomentumData hQ hQ.1).summable_norm_sourceLeafWeight_lattice
      (RA1Leafwise.leafFam hQ hQ.1 H) S hcover hcard hL1 (by omega) (by omega) hBi hF' k)]
  simp_rw [hD _ t ht k]
  rw [star_profile_fubini hQ hQ.1 R (RA1Leafwise.leafFam hQ hQ.1 H) S Gm.base.amplitude Gm.root
    Gm.base.μ k ![t 0, t 1] (hint k)]
  have ht' : ![t 0, t 1] = t := by
    funext i
    fin_cases i <;> rfl
  rw [ht']

/-- The filter scales in energy coordinates are at least one. -/
theorem filt_scale_ge_one {L δ γ η M : ℝ} (hL : 4 ≤ L) (hγ : 0 ≤ γ) (hη : η ≤ 1/20)
    (hδ : L^(-(η/2)) ≤ 2*δ) (hM : L ≤ M) : 1 ≤ L^(2*γ)*(2*δ) * M / 2 := by
  have hL0 : 0 < L := by linarith
  have hδ0 : 0 < δ := by
    have := Real.rpow_pos_of_pos hL0 (-(η/2))
    linarith
  have h1 : 1 ≤ L^(2*γ) := Real.one_le_rpow (by linarith) (by linarith)
  have h2 : L^(1-η/2) ≤ 2*δ*L := by
    have he : L^(1-η/2) = L^(-(η/2)) * L := by
      rw [show (1:ℝ)-η/2 = -(η/2) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    rw [he]
    exact mul_le_mul_of_nonneg_right hδ hL0.le
  have h3 : 2 ≤ L^(1-η/2) := by
    have h4 : L^((1:ℝ)/2) ≤ L^(1-η/2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h5 : (2:ℝ) ≤ L^((1:ℝ)/2) := by
      rw [← Real.sqrt_eq_rpow]
      calc (2:ℝ) = Real.sqrt 4 := by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
    linarith
  have h6 : 2 ≤ 2*δ*M := by nlinarith
  have h7 : 2*δ*M ≤ L^(2*γ)*(2*δ)*M := by
    have : 0 ≤ 2*δ*M := by nlinarith
    nlinarith
  linarith

/-- The D5 filter on a couple link is a product of at most four good factors in energy coordinates. -/
theorem couple_linkFilt_filtMul {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) {μ : ℝ}
    (hμ : 0 < μ) (hM : ∀ b ∈ F, 1 ≤ μ * M b / 2) (hMu : ∀ b ∈ Fu, 1 ≤ μ * Mu b / 2)
    (j : Fin Q.links.length) :
    FiltMul d (Kfilt d) 4 (profFilt μ (FiltSrc.coupleLinkFilt hQ F Fu ann M Mu) j) := by
  have h := filtMul_linkFiltWeight (d := d) (FiltSrc.coupleLinkBlock hQ j) F Fu ann M Mu hμ hM hMu
  refine h.mono ?_
  have h1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := F) (s₂ := FiltSrc.coupleLinkBlock hQ j))
  have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := Fu) (s₂ := FiltSrc.coupleLinkBlock hQ j))
  have h3 := FiltSrc.card_coupleLinkBlock_le hQ j
  omega

/-- **Layer-zero couples with star weights and both filter layers in `X^{θ,30d,30d}`.** -/
theorem exists_couple_filt_bound_theta (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8) {Binput : ℝ} (hBi : 0 ≤ Binput) :
    ∃ Ck : ℝ, 1 ≤ Ck ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ Q : RegCpl, Q.wf = true → Q.size = 2*n →
      ∀ (LG : LayeredGarden 2) (_hQ : Q.Decodes LG.garden), (∀ a, LG.layer a = 0) →
      ∀ H : LGSpine.LeafProfiles 2 d,
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.addrFam H z) ≤ ENNReal.ofReal Binput) →
      ∀ T : Set (Fin 2 → ℝ), (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, L ≤ Mu b) →
      Fourier.mixedRestrictionNorm θ (30*d) (30*d) T Set.univ
        (fun t k => Flower.Stage1W.kernelLeavesW L γ δ LG H
          (fun b => if b.1.1 = 0 then t.val 0 else t.val 1) 0 k.val (fun _ => 0) 0
          (d5Mult Sset ω F ann M Fu Mu)) ≤
        ENNReal.ofReal (Ck*(Ck*δ)^n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
  classical
  obtain ⟨Bfl, hBfl1, hBflC, -⟩ := FiltSrc.exists_linkFilt_bound
  obtain ⟨Ccover,hCc,hCover⟩ := actual_couple_uniform_cell_cover d (by omega)
  obtain ⟨Kr,Cm,hKr,hCm,henv⟩ := filt_scalar_envelope hd hγ hη0 hη hηγ hθ0 hθ
    A1_nonneg (one_le_C0 (1-η/8) (η/4) (1-η/2)) (one_le_Kfilt d) 4
  obtain ⟨Ks,Cs,hKs,hCs,hsym⟩ := filt_symbol_envelope hd hγ hη0 hη hηγ hθ0 hθ
    A1_nonneg (one_le_C0 (1-η/8) (η/4) (1-η/2)) (one_le_Kfilt d) 4
  obtain ⟨Ck,hCk,hbudget⟩ := RA1Leafwise.exists_common_physical_error_constant d (30*d) (30*d) (40*d) θ
    hKr.le (zero_le_one.trans hCm) hCc.le hBi
  refine ⟨Ck,hCk,fun Aorder => ?_⟩
  obtain ⟨Le,henv⟩ := henv Aorder
  obtain ⟨Ls,hsym⟩ := hsym Aorder
  refine ⟨max 4 (max Le Ls),?_⟩
  intro L hL δ hδ hδ1 n hn hnlog Q hwf hsize LG hQ h0 H hF T hT Sset ω cω hpres F ann M hM Fu Mu hMu
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hL
  have hLe : Le ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLs : Ls ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos hLpos (-(η/2))).trans_le hδ
    linarith only [hh]
  have hlinks : Q.links.length = n := links_length_eq_half hsize
  have hlinkspos : 0 < Q.links.length := by omega
  have hlinkslog : (Q.links.length:ℝ) ≤ Real.log L^Aorder := by simpa only [hlinks] using hnlog
  -- the filters
  set φ := FiltSrc.coupleLinkFilt hQ F Fu ann M Mu with hφdef
  have hφ : ∀ j u, ‖φ j u‖ ≤ Bfl := fun j u => hBflC hQ F Fu ann M Mu j u
  set μ' : ℝ := L^(2*γ)*(2*δ) with hμ'
  have hμ'0 : 0 < μ' := mul_pos (Real.rpow_pos_of_pos hLpos _) (by linarith)
  set ψ := profFilt μ' φ with hψdef
  have hψ : ∀ j, FiltMul d (Kfilt d) 4 (ψ j) := fun j =>
    couple_linkFilt_filtMul hQ F Fu ann M Mu hμ'0
      (fun b hb => filt_scale_ge_one hL4 hγ.1.le hη hδ (hM b hb))
      (fun b hb => filt_scale_ge_one hL4 hγ.1.le hη hδ (hMu b hb)) j
  obtain ⟨C,hC,hglob⟩ := couple_filt_global (A := A1) hη0 (by linarith) le_rfl Q hwf
  choose S hcard hcover using hCover LG.garden Q hQ hQ.1
  have hC' (Z : (chosenSet Q.links).powerset) :
      SRep (1-η/8) (η/4) (1-η/2) A1
        (C0 (1-η/8) (η/4) (1-η/2)^(4*Q.links.length+1)) (C Z) := by
    have he : 2*Q.size+1 = 4*Q.links.length+1 := by omega
    simpa only [he] using hC Z
  obtain ⟨B,hmB,hpB,hbB,hgood⟩ := henv L hLe δ hδ hδ1 Q hlinkspos hlinkslog C hC' LG.garden.zeta
    (RA1Leafwise.norm_garden_zeta LG.garden).le
  have hF' : ∀ a, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.leafFam hQ hQ.1 H a) ≤
      ENNReal.ofReal Binput := fun a => hF _
  set Gm := IncTop.starRootMeasure (30*d) Sset ω cω hpres (IncTop.coupleRow hQ) with hGm
  let R : _ → SymFam Q d := fun a => filtScalarν L δ γ Q LG.garden.zeta C ψ (Gm.base.frequency a)
  have hR : ∀ z, StronglyMeasurable (fun p : _ × ((ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) => R p.1 p.2.1 p.2.2.1 p.2.2.2 z) :=
    fun z => stronglyMeasurable_shifted (filtScalar L δ γ Q LG.garden.zeta C ψ) z
      (stronglyMeasurable_filtScalar_joint Q hLpos δ γ LG.garden.zeta C (fun Z => (hC' Z).reg.meas) ψ z)
      Gm.base.frequency_measurable
  have hb : ∀ᵐ lam : ℝ × ℝ, ∀ a z β γ', ‖R a lam β γ' z‖ ≤ (2*(Kr*δ)^Q.links.length) * B lam := by
    filter_upwards [hgood] with lam h a z β γ'
    exact h z _ _ ψ hψ
  have hBfin : (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) < ⊤ :=
    hbB.trans_lt (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  have hmom : (∫⁻ a, ENNReal.ofReal ((1+‖Gm.root a‖)^(30*d)) * ‖Gm.base.amplitude a‖ₑ ∂Gm.base.μ) ≤
      ∏ a ∈ Sset, ENNReal.ofReal (cω a) :=
    IncTop.starRootMeasure_momentMass_le (30*d) Sset ω cω hpres (IncTop.coupleRow hQ)
  have hMm : (∏ a ∈ Sset, ENNReal.ofReal (cω a)) < ⊤ :=
    ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)
  have hr : (0:ℝ) ≤ 2*(Kr*δ)^Q.links.length := by positivity
  have hi : ∀ (ν : PairedMomentum d Q.links.length) (k : Mom d) (Z : (chosenSet Q.links).powerset),
      Integrable (fun q => RA1Leafwise.maskedLeafScalarDensity hQ hQ.1
        (fun lam β γ' z => filtCellSymbol L δ γ ψ z (shiftL β ν 0) (shiftL γ' ν 1)
          (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam) (RA1Leafwise.leafFam hQ hQ.1 H) S q k)
        (volume.prod (RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
    intro ν k Z
    obtain ⟨BZ,hmBZ,hpBZ,hbBZ,hgBZ⟩ := hsym L hLs δ hδ hδ1 Q.links.length hlinkspos hlinkslog
      (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) (hC' Z)
    refine filt_shifted_symbol_integrable hQ H hBi hF' S hcard hLpos hθ0 _ (C Z) (hC' Z).reg.meas ψ
      (r := 2*(Ks*δ)^Q.links.length) (by positivity) hmBZ hpBZ
      (hbBZ.trans_lt (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) ?_ ν k (by omega)
    filter_upwards [hgBZ] with lam h z β γ'
    exact h z β γ' ψ hψ
  have hint : ∀ k : Mom d, Integrable (fun q => starDensity hQ hQ.1 R (RA1Leafwise.leafFam hQ hQ.1 H) S
      Gm.base.amplitude Gm.root q k)
      (volume.prod ((RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod Gm.base.μ)) :=
    fun k => integrable_starDensity hQ hQ.1 (N := 30*d) (W := 30*d) (K := 40*d) (M := 40*d) R hR
      (by omega) (by omega) hBi hF' S hcard hθ0 Gm.base.μ Gm.amplitude_measurable Gm.root_measurable
      hmom hMm hr hmB hpB hBfin hb k
  have hD : ∀ (a : _) (t : Fin 2 → ℝ), (∀ i, t i ∈ Icc (0:ℝ) 1) → ∀ k : Mom d,
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          (((Real.fourierChar (inner ℝ (Gm.base.frequency a) (pairedLattice L p)) : ℂ) *
            FiltSrc.arrayFiltWeight L φ p) *
            RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ (t 0) (t 1) k p) *
          (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
            (fun i j => latticePoint L (p (i,j))) =
        RA1Leafwise.sourceScalarProfile hQ hQ.1 (R a) (RA1Leafwise.leafFam hQ hQ.1 H) S ![t 0, t 1] k :=
    fun a t ht k => hglob d (40*d) (40*d) H Binput Ccover L γ δ LG h0 hQ (by omega) (by omega) hBi hF' hL1
      hδpos S hcard hcover (t 0) (ht 0) (t 1) (ht 1) k (Gm.base.frequency a) φ Bfl hφ (fun Z => hi _ _ Z)
  have hm : ∀ k (p : (Fin Q.links.length × Fin 2) → Fin d → ℤ),
      d5Mult Sset ω F ann M Fu Mu (cosetDecoration LG.garden L k
        ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) =
        (Gm.at k).value (pairedLattice L p) * FiltSrc.arrayFiltWeight L φ p :=
    fun k p => FiltSrc.couple_starFiltWeight_eq hQ (30*d) Sset ω cω hpres L k F Fu ann M Mu p
  have hfun : (fun t : T => fun k : (Set.univ : Set (Mom d)) =>
      Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t.val 0 else t.val 1) 0 k.val
        (fun _ => 0) 0 (d5Mult Sset ω F ann M Fu Mu)) =
      (fun t : T => fun k : (Set.univ : Set (Mom d)) =>
        pairedInverseProfile (fun lam => ∫ u, starDensity hQ hQ.1 R (RA1Leafwise.leafFam hQ hQ.1 H) S
          Gm.base.amplitude Gm.root (lam, u) k.val
          ∂(RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod Gm.base.μ) t.val) := by
    funext t k
    exact couple_filt_kernel_eq hQ h0 H hBi hF' hL1 γ δ (by omega) S hcard hcover Gm R φ hφ hD
      (d5Mult Sset ω F ann M Fu Mu) hm hint t.val (hT t.val t.property) k.val
  rw [hfun]
  have hmain := star_leaf_profile_le hQ hQ.1 (N := 30*d) (W := 30*d) (K := 40*d) (M := 40*d) R hR
    (by omega) (by omega) hBi hF' S hcard hθ0 hT Gm.base.μ Gm.amplitude_measurable Gm.root_measurable
    hmom hMm hr hmB hpB hBfin hb
  refine hmain.trans ?_
  have hbud := hbudget Q δ 1 hδpos.le zero_le_one
  rw [← hlinks]
  exact star_budget_le hKr.le hδpos.le hbB _ hbud

end WaveTurbulence.Flower.FiltCoh
