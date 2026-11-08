/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.ZeroOrder

/-! # FILT-COH: the single-layer `X^{1/4}` bounds (bound-only oracle)

Every single-layer regular couple (all nodes in layer `r`) and every regular tree in layer `r` whose lone leaf lies
in a layer `q'' ≤ r`, with individually controlled leaf profiles, has
`‖K‖_{X^{1/4}} ≤ C (C δ)^n ∏ B_ℓ` (no `L` power). This is the bound-only counterpart of main's
`LeafwiseRegularAsymptoticsGate` (whose error clause is only in `X^η`), at the weight `1/4` that main lacks
(F-D0-5). -/

public section
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory Set TTree WaveTurbulence.Fourier WaveTurbulence.Regref
open WaveTurbulence.RA1Leafwise LGSpine
open scoped ENNReal

/-- **Single-layer bound oracle at weight `1/4`.** -/
theorem single_layer_bounds :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0:ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, δ ∈ Ioc (0:ℝ) (1/2) → ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A →
      (∀ (r : ℕ) (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) → ∀ (H : LeafProfiles 2 d) (B : (Fin 2 × Path) → NNReal),
        LeafwiseControlled LG H B →
        XNormRestr (1/4) (30 * d) (30 * d) (timeBox r r) Set.univ
          (fun ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k) ≤
          ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B)) ∧
      (∀ (r q'' : ℕ) (X : RegChain), q'' ≤ r → X.wf = true → X.size = 2 * n →
        ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
        (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
        ∀ (H : LeafProfiles 1 d) (B : (Fin 1 × Path) → NNReal), LeafwiseControlled LG H B →
        XNormRestr (1/4) (30 * d) 0 (timeBoxGt r q'') Set.univ
          (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤
          ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B)) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hrange⟩ := exists_couple_eta_range hd hγ
  refine ⟨η₀, hη₀, fun η hη => ?_⟩
  obtain ⟨hη20, hηγ, hηγ', -⟩ := hrange η hη
  have hθ0 : (0:ℝ) ≤ 1/4 := by norm_num
  have hθ : (1/4 : ℝ) ≤ 1 - η/8 := by linarith
  obtain ⟨Cc, hCc, Hc⟩ := exists_couple_kernel_bound_theta hd hγ hη.1 hη20 hηγ hηγ' hθ0 hθ zero_le_one
  obtain ⟨Ct, hCt, Ht⟩ := exists_tree_kernel_bound_theta hd hγ hη.1 hη20 hηγ hηγ' hθ0 hθ zero_le_one
  set τ : ℝ := (timeFourierNorm (1/4) unitSquareCutoff).toReal with hτ
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hLc0 : 0 ≤ PL2330.cLeib d (30*d) := PL2330.cLeib_nonneg _ _
  set K := Ktr' (1/4) with hKdef
  have hK1 : 1 ≤ K := one_le_Ktr' hθ0
  set Cm : ℝ := max (max Cc Ct) (max (PL2330.cLeib d (30*d) * τ) τ) with hCmdef
  have hCm1 : 1 ≤ Cm := hCc.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hCm0 : 0 ≤ Cm := zero_le_one.trans hCm1
  refine ⟨K * Cm, one_le_mul_of_one_le_of_one_le hK1 hCm1, fun δ hδ A => ?_⟩
  obtain ⟨Lc, Hc⟩ := Hc A
  obtain ⟨Lt, Ht⟩ := Ht A
  obtain ⟨Ld, hLd⟩ := exists_physical_delta_threshold hη.1 hδ.1
  refine ⟨max (max Lc Lt) (max Ld 2), fun L hL n hn => ?_⟩
  have hLc : Lc ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLt : Lt ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLd' : Ld ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL2 : 2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith
  have hδ2 : L ^ (-(η/2)) ≤ 2 * δ := hLd L hLd'
  have hδ1 : 2 * δ ≤ 1 := by linarith [hδ.2]
  have hd1 : 1 ≤ d := by omega
  have hδ0 : 0 ≤ δ := hδ.1.le
  have hfin : ∀ x : ℝ, ENNReal.ofReal x ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  -- the unit bound for every order (positive: the pipeline; zero: time independent)
  have hunitC : ∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2,
      Q.Decodes LG.garden → (∀ a, LG.layer a = 0) → ∀ H' : LeafProfiles 2 d,
      (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      mixedRestrictionNorm (1/4) (30 * d) (30 * d) (timeBox 0 0) Set.univ
        (fun ts k => coupleLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1) ≤ ENNReal.ofReal (Cm * (Cm * δ) ^ n) := by
    intro Q hwf hsz LG hdec h0 H' hH'
    have hF : ∀ z, spatialNorm (40*d) (40*d) (addrFam H' z) ≤ ENNReal.ofReal 1 := fun z => by
      have := hH' z
      rwa [NormBridgeScratch.SNormR_eq_spatialNorm] at this
    have hT : ∀ t ∈ timeBox (0:ℝ) 0, ∀ i, t i ∈ Icc (0:ℝ) 1 := by
      intro t ht i
      have hh : t 0 ∈ Icc (0:ℝ) 1 ∧ t 1 ∈ Icc (0:ℝ) 1 := by
        simpa only [timeBox,Set.mem_ofPred_eq,zero_add] using ht
      fin_cases i
      · exact hh.1
      · exact hh.2
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine (couple_zero_bound L γ δ (1/4) hd1 hwf (by omega) LG h0 hdec zero_le_one H' hF _ hT).trans ?_
      apply ENNReal.ofReal_le_ofReal
      simp only [pow_zero, mul_one]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · refine (Hc L hLc δ hδ2 hδ1 n hnpos hn Q hwf hsz LG hdec h0 H' hF _ hT).trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hcc : Cc ≤ Cm := (le_max_left _ _).trans (le_max_left _ _)
      exact mul_le_mul hcc (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcc hδ0) n)
        (by positivity) hCm0
  have hunitT : ∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
      X.DecodesTree LG.garden → (∀ a, LG.layer a = 0) → ∀ H' : LeafProfiles 1 d,
      (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      mixedRestrictionNorm (1/4) (30 * d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => treeLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1) ≤ ENNReal.ofReal (Cm * (Cm * δ) ^ n) := by
    intro X hwf hsz LG hdec h0 H' hH'
    have hF : ∀ z, spatialNorm (40*d) (40*d) (addrFam H' z) ≤ ENNReal.ofReal 1 := fun z => by
      have := hH' z
      rwa [NormBridgeScratch.SNormR_eq_spatialNorm] at this
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine (tree_zero_bound L γ δ (1/4) hd hwf (by omega) LG hdec h0 hL1 hδ.1.ne' zero_le_one H' hF).trans ?_
      rw [← ENNReal.ofReal_toReal (timeFourierNorm_unitSquareCutoff_lt_top (1/4)).ne]
      apply ENNReal.ofReal_le_ofReal
      simp only [pow_zero, mul_one]
      exact (le_max_right _ _).trans (le_max_right _ _)
    · refine (Ht L hLt δ hδ2 hδ1 n hnpos hn X hwf hsz LG hdec h0 H' hF).trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hct : Ct ≤ Cm := (le_max_right _ _).trans (le_max_left _ _)
      exact mul_le_mul hct (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hct hδ0) n)
        (by positivity) hCm0
  refine ⟨?_, ?_⟩
  · intro r Q hwf hsz LG hdec hlay H B hctl
    have hctl0 : LeafwiseControlled (layer0 LG) H B := hctl
    have hdec0 : Q.Decodes (layer0 LG).garden := hdec
    have hsc := couple_kernel_scaled L γ δ (1/4) hd1 Q (layer0 LG) hdec0 (timeBox 0 0) _ (hfin _)
      (fun H' hH' => hunitC Q hwf hsz (layer0 LG) hdec0 (fun _ => rfl) H' hH') H B hctl0
    refine (couple_kernel_item_le L γ δ H hdec hlay hsc).trans ?_
    have e0 : leafSizeProduct (layer0 LG) B = leafSizeProduct LG B := rfl
    have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    rw [e0, ← ENNReal.ofReal_mul hβ0]
    apply ENNReal.ofReal_le_ofReal
    have hb := bound_mono_K'' n hK1 hCm0 le_rfl hδ0
      (Finset.prod_nonneg fun ℓ _ => NNReal.coe_nonneg (B ℓ.1) : 0 ≤ leafSizeProduct LG B)
    calc leafSizeProduct LG B * (Cm * (Cm * δ) ^ n)
        = 1 * (Cm * (Cm * δ) ^ n * leafSizeProduct LG B) := by ring
      _ ≤ K * (Cm * (Cm * δ) ^ n * leafSizeProduct LG B) :=
          mul_le_mul_of_nonneg_right hK1 (by
            have := Finset.prod_nonneg fun ℓ (_ : ℓ ∈ inputLeaves LG.garden) => NNReal.coe_nonneg (B ℓ.1)
            positivity)
      _ ≤ _ := hb
  · intro r q'' X hq hwf hsz LG hdec hlay H B hctl
    have hctl0 : LeafwiseControlled (layer0 LG) H B := hctl
    have hdec0 : X.DecodesTree (layer0 LG).garden := hdec
    have hsc := tree_kernel_scaled L γ δ (1/4) hd1 X (layer0 LG) (timeBoxGt 0 0) _ (hfin _)
      (fun H' hH' => hunitT X hwf hsz (layer0 LG) hdec0 (fun _ => rfl) H' hH') H B hctl0
    have hFs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k : Mom d,
        Summable fun m : Fin d → ℤ => |H ℓ.1 (k + latticePoint L m)| := fun ℓ hℓ k =>
      summable_abs_coset_of_SNormR (by linarith) (by omega : d + 1 ≤ 40 * d)
        (B ℓ.1).2 (H ℓ.1) (hctl ℓ hℓ) k
    refine (tree_kernel_item_le L γ δ H hdec hFs hq hlay hθ0 (Λ := 30 * d) (by omega) hsc).trans ?_
    have e0 : leafSizeProduct (layer0 LG) B = leafSizeProduct LG B := rfl
    have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    rw [e0, ← ENNReal.ofReal_mul hβ0, traceConst_mul_ofReal']
    apply ENNReal.ofReal_le_ofReal
    have hb := bound_mono_K'' n hK1 hCm0 le_rfl hδ0
      (Finset.prod_nonneg fun ℓ _ => NNReal.coe_nonneg (B ℓ.1) : 0 ≤ leafSizeProduct LG B)
    calc Ktr' (1/4) * (leafSizeProduct LG B * (Cm * (Cm * δ) ^ n))
        = K * (Cm * (Cm * δ) ^ n * leafSizeProduct LG B) := by rw [hKdef]; ring
      _ ≤ _ := hb

end WaveTurbulence.Flower.FiltCoh
