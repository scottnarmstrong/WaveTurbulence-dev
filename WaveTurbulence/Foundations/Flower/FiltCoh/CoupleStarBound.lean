/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleStarMix

/-! # FILT-COH (b): star-weighted layer-zero couples at weight `θ ≤ 1 - η/8`

`exists_couple_star_bound_theta`: for a layer-zero regular couple, separately normalized leaf profiles and ANY star
weights `ω` presented with `30d`-th total-frequency moments `cω` (INC-TOP's `StarPresented`), the star-weighted
kernel has `X^{θ,30d,30d}` norm `≤ Ck (Ck δ)^n ∏ cω`. This is o82 Thm 10.1 (10.5) (uniform in the lattice
modulations) through main's RA1LW cell pipeline: star weight = presentation mixture of root × lattice characters
(`couple_star_swap`), lattice character = modulation shift of the cell symbols (`couple_char_global`), Fubini
(`star_profile_fubini`) and the star leaf engine (`star_leaf_profile_le`), constants by main's
`RA1Leafwise.exists_common_physical_error_constant`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh Set
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure)
open scoped ENNReal

variable {d : ℕ}

/-- A fixed link-frequency shift preserves joint measurability. -/
theorem stronglyMeasurable_shift_fixed {n : ℕ} {Z : Type*}
    (R : (ℝ × ℝ) → (Fin n → Mom d) → (Fin n → Mom d) → Z → ℂ) (z : Z)
    (hR : StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) => R p.1 p.2.1 p.2.2 z))
    (ν : PairedMomentum d n) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      R p.1 (shiftL p.2.1 ν 0) (shiftL p.2.2 ν 1) z) := by
  have hmap : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      (p.1, (shiftL p.2.1 ν 0, shiftL p.2.2 ν 1))) :=
    measurable_fst.prodMk
      (((continuous_shiftL 0).measurable.comp (measurable_snd.fst.prodMk measurable_const)).prodMk
        ((continuous_shiftL 1).measurable.comp (measurable_snd.snd.prodMk measurable_const)))
  exact hR.comp_measurable hmap

/-- Integrability of a shifted cell symbol density from its uniform envelope. -/
theorem shifted_symbol_integrable {Q : RegCpl} {LG : LayeredGarden 2} (hQ : Q.Decodes LG.garden)
    (H : LGSpine.LeafProfiles 2 d) {Binput Ccover : ℝ} (hBi : 0 ≤ Binput)
    (hF' : ∀ a, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {L δ γ θ : ℝ} (hLpos : 0 < L) (hθ0 : 0 ≤ θ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (hCm : StronglyMeasurable (Function.uncurry C)) {r : ℝ} (hr : 0 ≤ r) {BZ : (ℝ × ℝ) → ℝ}
    (hm : Measurable BZ) (hp : ∀ lam, 0 ≤ BZ lam) (hfin : (∫⁻ lam, wL θ lam*ENNReal.ofReal (BZ lam)) < ⊤)
    (hg : ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin Q.links.length → Mom d), ‖physicalWeightedCellSymbol L δ γ z β γ' J C lam‖ ≤ r*BZ lam)
    (ν : PairedMomentum d Q.links.length) (k : Mom d) (hd : 1 ≤ d) :
    Integrable (fun q => RA1Leafwise.maskedLeafScalarDensity hQ hQ.1
        (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z (shiftL β ν 0) (shiftL γ' ν 1) J C lam)
        (RA1Leafwise.leafFam hQ hQ.1 H) S q k)
      (volume.prod (RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
  have hmZ : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
      physicalWeightedCellSymbol L δ γ z (shiftL p.2.1 ν 0) (shiftL p.2.2 ν 1) J C p.1) := fun z =>
    stronglyMeasurable_shift_fixed (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' J C lam) z
      (stronglyMeasurable_physicalWeightedCellSymbol_joint hLpos δ γ J hCm z) ν
  refine integrable_density_of_env hQ hQ.1
    (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z (shiftL β ν 0) (shiftL γ' ν 1) J C lam) hmZ
    (K := 40*d) (M := 40*d) (by omega) (by omega) hBi hF' S hcard hθ0 hr hm hp hfin ?_ k
  filter_upwards [hg] with lam h z β γ'
  exact h z _ _

/-- **The exact star identity of a layer-zero couple.** -/
theorem couple_star_kernel_eq {Q : RegCpl} {LG : LayeredGarden 2} (hQ : Q.Decodes LG.garden)
    (h0 : ∀ a, LG.layer a = 0) (H : LGSpine.LeafProfiles 2 d) {Binput Ccover : ℝ} (hBi : 0 ≤ Binput)
    (hF' : ∀ a, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal Binput)
    {L : ℝ} (hL1 : 1 ≤ L) (γ δ : ℝ) (hd : 1 ≤ d)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    (hcover : ∀ c k x, (coupleMomentumData hQ hQ.1).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {α : Type} [MeasurableSpace α] (Gm : RootMeasure d Q.links.length α) (R : α → SymFam Q d)
    (hD : ∀ (a : α) (t : Fin 2 → ℝ), (∀ i, t i ∈ Icc (0:ℝ) 1) → ∀ k : Mom d,
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          ((Real.fourierChar (inner ℝ (Gm.base.frequency a) (pairedLattice L p)) : ℂ) *
            RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ (t 0) (t 1) k p) *
          (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
            (fun i j => latticePoint L (p (i,j))) =
        RA1Leafwise.sourceScalarProfile hQ hQ.1 (R a) (RA1Leafwise.leafFam hQ hQ.1 H) S ![t 0, t 1] k)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (hm : ∀ k (p : (Fin Q.links.length × Fin 2) → Fin d → ℤ),
      m (cosetDecoration LG.garden L k
        ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0), p (j,1)))).val) =
        (Gm.at k).value (pairedLattice L p))
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
  rw [couple_star_swap hQ Gm L k m (hm k)
    (fun p => RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ (t 0) (t 1) k p)
    (fun p => (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
      (fun i j => latticePoint L (p (i,j))))
    (fun p => RA1Leafwise.norm_coupleLatticeTimeCoefficient_le_one L γ δ LG h0 hQ (ht 0).2 (ht 1).2 k p)
    ((coupleMomentumData hQ hQ.1).summable_norm_sourceLeafWeight_lattice
      (RA1Leafwise.leafFam hQ hQ.1 H) S hcover hcard hL1 (by omega) (by omega) hBi hF' k)]
  simp_rw [hD _ t ht k]
  rw [star_profile_fubini hQ hQ.1 R (RA1Leafwise.leafFam hQ hQ.1 H) S Gm.base.amplitude Gm.root
    Gm.base.μ k ![t 0, t 1] (hint k)]
  have ht' : ![t 0, t 1] = t := by
    funext i
    fin_cases i <;> rfl
  rw [ht']

/-- The budget comparison with main's common constant. -/
theorem star_budget_le {θ Kr Ccover Binput δ : ℝ} (hKr : 0 ≤ Kr) (hδ : 0 ≤ δ) {Q : RegCpl} {Cm Ck : ℝ}
    {B : (ℝ × ℝ) → ℝ} (hbB : (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤ ENNReal.ofReal Cm^Q.links.length)
    (P : ℝ≥0∞)
    (hbud : ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff *
        (ENNReal.ofReal (Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) (30*d) (30*d) *
          ((1+2*Real.pi)*(Kr*δ)^Q.links.length*spectralFrequencyLoss Q)) *
          (ENNReal.ofReal 1*ENNReal.ofReal Cm^Q.links.length) *
          (ENNReal.ofReal (Ccover^Q.links.length)*
            ENNReal.ofReal (Incoh.leafWeightedMomentLocalizationConstant d (30*d+1) (40*d) (30*d)*Binput)^
              (2*Q.links.length+1))) ≤
      ENNReal.ofReal (Ck*(Ck*δ)^Q.links.length*1)) :
    ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff *
        (ENNReal.ofReal (Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) (30*d) (30*d) *
          (2*(Kr*δ)^Q.links.length)) *
          (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) *
          (ENNReal.ofReal (Ccover^Q.links.length)*
            ENNReal.ofReal (Incoh.leafWeightedMomentLocalizationConstant d (30*d+1) (40*d) (30*d)*Binput)^
              (2*Q.links.length+1)) * P) ≤
      ENNReal.ofReal (Ck*(Ck*δ)^Q.links.length) * P := by
  have hsfl : (2:ℝ) ≤ (1+2*Real.pi)*spectralFrequencyLoss Q := by
    have h1 : 1 ≤ spectralFrequencyLoss Q := by
      unfold spectralFrequencyLoss
      have : 0 ≤ 4*Real.pi*(Q.links.length:ℝ)*(1+(Q.size:ℝ)) := by positivity
      linarith
    nlinarith [Real.pi_gt_three]
  have hκ : 0 ≤ Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) (30*d) (30*d) := by
    have := zero_le_one.trans (Incoh.one_le_rootMaskDerivativeConstant d (30*d))
    unfold Incoh.maskedSourceSpatialConstant
    positivity
  have hX : ENNReal.ofReal (Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) (30*d) (30*d) *
      (2*(Kr*δ)^Q.links.length)) ≤
      ENNReal.ofReal (Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) (30*d) (30*d) *
        ((1+2*Real.pi)*(Kr*δ)^Q.links.length*spectralFrequencyLoss Q)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hκ
    have hp : 0 ≤ (Kr*δ)^Q.links.length := by positivity
    nlinarith
  have hY : (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤
      ENNReal.ofReal 1 * ENNReal.ofReal Cm^Q.links.length := by
    rw [ENNReal.ofReal_one, one_mul]; exact hbB
  rw [mul_one] at hbud
  calc _ = (ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff *
          (ENNReal.ofReal (Incoh.maskedSourceSpatialConstant d (2*Q.links.length+1) (30*d) (30*d) *
            (2*(Kr*δ)^Q.links.length)) *
            (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) *
            (ENNReal.ofReal (Ccover^Q.links.length)*
              ENNReal.ofReal (Incoh.leafWeightedMomentLocalizationConstant d (30*d+1) (40*d) (30*d)*Binput)^
                (2*Q.links.length+1)))) * P := by ring
    _ ≤ _ := by
        refine mul_le_mul' (le_trans ?_ hbud) le_rfl
        gcongr

/-- **Star-weighted layer-zero couples in `X^{θ,30d,30d}`.** -/
theorem exists_couple_star_bound_theta (hd : 3 ≤ d) {γ η : ℝ}
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
      Fourier.mixedRestrictionNorm θ (30*d) (30*d) T Set.univ
        (fun t k => Flower.Stage1W.kernelLeavesW L γ δ LG H
          (fun b => if b.1.1 = 0 then t.val 0 else t.val 1) 0 k.val (fun _ => 0) 0
          (IncTop.starWeight Sset ω)) ≤
        ENNReal.ofReal (Ck*(Ck*δ)^n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
  classical
  obtain ⟨Ccover,hCc,hCover⟩ := actual_couple_uniform_cell_cover d (by omega)
  obtain ⟨Kr,Cm,hKr,hCm,henv⟩ := physical_scalar_envelope_theta_u hd hγ hη0 hη hηγ hθ0 hθ
    A1_nonneg (one_le_C0 (1-η/8) (η/4) (1-η/2))
  obtain ⟨Ks,Cs,hKs,hCs,hsym⟩ := physical_symbol_envelope_u hd hγ hη0 hη hηγ hθ0 hθ
    A1_nonneg (one_le_C0 (1-η/8) (η/4) (1-η/2))
  obtain ⟨Ck,hCk,hbudget⟩ := RA1Leafwise.exists_common_physical_error_constant d (30*d) (30*d) (40*d) θ
    hKr.le (zero_le_one.trans hCm) hCc.le hBi
  refine ⟨Ck,hCk,fun Aorder => ?_⟩
  obtain ⟨Le,henv⟩ := henv Aorder
  obtain ⟨Ls,hsym⟩ := hsym Aorder
  refine ⟨max 2 (max Le Ls),?_⟩
  intro L hL δ hδ hδ1 n hn hnlog Q hwf hsize LG hQ h0 H hF T hT Sset ω cω hpres
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
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
  obtain ⟨C,hC,hglob⟩ := couple_char_global (A := A1) hη0 (by linarith) le_rfl Q hwf
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
  let R : _ → SymFam Q d := fun a => physicalScalarν L δ γ Q LG.garden.zeta C (Gm.base.frequency a)
  have hR : ∀ z, StronglyMeasurable (fun p : _ × ((ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) => R p.1 p.2.1 p.2.2.1 p.2.2.2 z) :=
    fun z => stronglyMeasurable_shifted (physicalScalar L δ γ Q LG.garden.zeta C) z
      (stronglyMeasurable_physicalScalar_joint Q hLpos δ γ LG.garden.zeta C (fun Z => (hC' Z).reg.meas) z)
      Gm.base.frequency_measurable
  have hb : ∀ᵐ lam : ℝ × ℝ, ∀ a z β γ', ‖R a lam β γ' z‖ ≤ (2*(Kr*δ)^Q.links.length) * B lam := by
    filter_upwards [hgood] with lam h a z β γ'
    exact h z _ _
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
        (fun lam β γ' z => physicalWeightedCellSymbol L δ γ z (shiftL β ν 0) (shiftL γ' ν 1)
          (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam) (RA1Leafwise.leafFam hQ hQ.1 H) S q k)
        (volume.prod (RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
    intro ν k Z
    obtain ⟨BZ,hmBZ,hpBZ,hbBZ,hgBZ⟩ := hsym L hLs δ hδ hδ1 Q.links.length hlinkspos hlinkslog
      (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) (hC' Z)
    exact shifted_symbol_integrable hQ H hBi hF' S hcard hLpos hθ0 _ (C Z) (hC' Z).reg.meas
      (r := 2*(Ks*δ)^Q.links.length) (by positivity) hmBZ hpBZ
      (hbBZ.trans_lt (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) hgBZ ν k (by omega)
  have hint : ∀ k : Mom d, Integrable (fun q => starDensity hQ hQ.1 R (RA1Leafwise.leafFam hQ hQ.1 H) S
      Gm.base.amplitude Gm.root q k)
      (volume.prod ((RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod Gm.base.μ)) :=
    fun k => integrable_starDensity hQ hQ.1 (N := 30*d) (W := 30*d) (K := 40*d) (M := 40*d) R hR
      (by omega) (by omega) hBi hF' S hcard hθ0 Gm.base.μ Gm.amplitude_measurable Gm.root_measurable
      hmom hMm hr hmB hpB hBfin hb k
  have hD : ∀ (a : _) (t : Fin 2 → ℝ), (∀ i, t i ∈ Icc (0:ℝ) 1) → ∀ k : Mom d,
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
          ((Real.fourierChar (inner ℝ (Gm.base.frequency a) (pairedLattice L p)) : ℂ) *
            RA1Leafwise.coupleLatticeTimeCoefficient L γ δ LG hQ (t 0) (t 1) k p) *
          (coupleMomentumData hQ hQ.1).sourceLeafWeight (RA1Leafwise.leafFam hQ hQ.1 H) k
            (fun i j => latticePoint L (p (i,j))) =
        RA1Leafwise.sourceScalarProfile hQ hQ.1 (R a) (RA1Leafwise.leafFam hQ hQ.1 H) S ![t 0, t 1] k :=
    fun a t ht k => hglob d (40*d) (40*d) H Binput Ccover L γ δ LG h0 hQ (by omega) (by omega) hBi hF' hL1 S
      hcard hcover (t 0) (ht 0) (t 1) (ht 1) k (Gm.base.frequency a) (fun Z => hi _ _ Z)
  have hfun : (fun t : T => fun k : (Set.univ : Set (Mom d)) =>
      Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t.val 0 else t.val 1) 0 k.val
        (fun _ => 0) 0 (IncTop.starWeight Sset ω)) =
      (fun t : T => fun k : (Set.univ : Set (Mom d)) =>
        pairedInverseProfile (fun lam => ∫ u, starDensity hQ hQ.1 R (RA1Leafwise.leafFam hQ hQ.1 H) S
          Gm.base.amplitude Gm.root (lam, u) k.val
          ∂(RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)).prod Gm.base.μ) t.val) := by
    funext t k
    exact couple_star_kernel_eq hQ h0 H hBi hF' hL1 γ δ (by omega) S hcard hcover Gm R hD
      (IncTop.starWeight Sset ω) (fun k p => IncTop.couple_starWeight_eq_value hQ (30*d) Sset ω cω hpres L k p)
      hint t.val (hT t.val t.property) k.val
  rw [hfun]
  have hmain := star_leaf_profile_le hQ hQ.1 (N := 30*d) (W := 30*d) (K := 40*d) (M := 40*d) R hR
    (by omega) (by omega) hBi hF' S hcard hθ0 hT Gm.base.μ Gm.amplitude_measurable Gm.root_measurable
    hmom hMm hr hmB hpB hBfin hb
  refine hmain.trans ?_
  have hbud := hbudget Q δ 1 hδpos.le zero_le_one
  rw [← hlinks]
  exact star_budget_le hKr.le hδpos.le hbB _ hbud

end WaveTurbulence.Flower.FiltCoh
