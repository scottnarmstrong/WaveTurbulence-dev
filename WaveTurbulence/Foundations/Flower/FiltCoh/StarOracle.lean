/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarLayer

/-! # FILT-COH (c3): the single-layer `X^{1/4}` bounds with star weights (bound-only oracle)

Every single-layer regular couple (all nodes in layer `r`) and every regular tree in layer `r` whose lone leaf lies
in a layer `q'' ≤ r`, with individually controlled leaf profiles and ANY star weights presented with `30d`-th
total-frequency moments `cω`, has `‖K‖_{X^{1/4}} ≤ C (C δ)^n ∏ B_ℓ · ∏ cω`, all orders `n ≤ (log L)^A` (order zero:
`ZeroStar`; positive order: `exists_couple_star_bound_theta`, `exists_tree_star_bound_theta`). -/

public section
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory Set TTree WaveTurbulence.Fourier WaveTurbulence.Regref
open WaveTurbulence.RA1Leafwise LGSpine
open scoped ENNReal

variable {d : ℕ}

theorem star_bound_absorb {Kt Cm C δ x : ℝ} (n : ℕ) (hKt : 1 ≤ Kt) (hCm : 0 ≤ Cm) (hC : C = Kt * Cm)
    (hδ : 0 ≤ δ) (hx : 0 ≤ x) (P : ℝ≥0∞) :
    ENNReal.ofReal Kt * (ENNReal.ofReal x * (ENNReal.ofReal (Cm * (Cm * δ) ^ n) * P)) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * x) * P := by
  have h0 : 0 ≤ Cm * (Cm * δ) ^ n := by positivity
  have hb := bound_mono_K'' n hKt hCm (le_of_eq hC.symm) hδ hx
  calc ENNReal.ofReal Kt * (ENNReal.ofReal x * (ENNReal.ofReal (Cm * (Cm * δ) ^ n) * P))
      = ENNReal.ofReal (Kt * (Cm * (Cm * δ) ^ n * x)) * P := by
        rw [ENNReal.ofReal_mul (zero_le_one.trans hKt), ENNReal.ofReal_mul h0]
        ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hb) le_rfl

/-- **Single-layer bound oracle at weight `1/4` with star weights.** -/
theorem single_layer_star_bounds :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0:ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, δ ∈ Ioc (0:ℝ) (1/2) → ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A →
      (∀ (r : ℕ) (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) → ∀ (H : LeafProfiles 2 d) (B : (Fin 2 × Path) → NNReal),
        LeafwiseControlled LG H B →
        ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
          (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
        XNormRestr (1/4) (30 * d) (30 * d) (timeBox r r) Set.univ
          (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
            (fun _ => 0) 0 (IncTop.starWeight Sset ω)) ≤
          ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B) * ∏ a ∈ Sset, ENNReal.ofReal (cω a)) ∧
      (∀ (r q'' : ℕ) (X : RegChain), q'' ≤ r → X.wf = true → X.size = 2 * n →
        ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
        (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
        ∀ (H : LeafProfiles 1 d) (B : (Fin 1 × Path) → NNReal), LeafwiseControlled LG H B →
        ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
          (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
        XNormRestr (1/4) (30 * d) 0 (timeBoxGt r q'') Set.univ
          (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
            (IncTop.starWeight Sset ω)) ≤
          ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B) * ∏ a ∈ Sset, ENNReal.ofReal (cω a)) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hrange⟩ := exists_couple_eta_range hd hγ
  refine ⟨η₀, hη₀, fun η hη => ?_⟩
  obtain ⟨hη20, hηγ, -, -⟩ := hrange η hη
  have hθ0 : (0:ℝ) ≤ 1/4 := by norm_num
  have hθ : (1/4 : ℝ) ≤ 1 - η/8 := by linarith
  obtain ⟨Cc, hCc, Hc⟩ := exists_couple_star_bound_theta hd hγ hη.1 hη20 hηγ hθ0 hθ zero_le_one
  obtain ⟨Ct, hCt, Ht⟩ := exists_tree_star_bound_theta hd hγ hη.1 hη20 hηγ hθ0 hθ zero_le_one
  set z := zeroStarConst d (1/4) with hz
  have hz0 : 0 ≤ z := zeroStarConst_nonneg _ _
  set K := Ktr' (1/4) with hKdef
  have hK1 : 1 ≤ K := one_le_Ktr' hθ0
  set Cm : ℝ := max (max Cc Ct) z with hCmdef
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
  have hmono : ∀ c : ℝ, 0 ≤ c → c ≤ Cm →
      ENNReal.ofReal (c * (c * δ) ^ n) ≤ ENNReal.ofReal (Cm * (Cm * δ) ^ n) := fun c h0 hc =>
    ENNReal.ofReal_le_ofReal (mul_le_mul hc (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hc hδ0) n) (by positivity) hCm0)
  have hT : ∀ t ∈ timeBox (0:ℝ) 0, ∀ i, t i ∈ Icc (0:ℝ) 1 := by
    intro t ht i
    have hh : t 0 ∈ Icc (0:ℝ) 1 ∧ t 1 ∈ Icc (0:ℝ) 1 := by
      simpa only [timeBox,Set.mem_ofPred_eq,zero_add] using ht
    fin_cases i
    · exact hh.1
    · exact hh.2
  -- unit layer-zero bounds, all orders
  have hunitC : ∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2,
      Q.Decodes LG.garden → (∀ a, LG.layer a = 0) → ∀ H' : LeafProfiles 2 d,
      (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
      mixedRestrictionNorm (1/4) (30 * d) (30 * d) (timeBox 0 0) Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H' (fun b => if b.1.1 = 0 then ts.1 0 else ts.1 1)
          0 k.1 (fun _ => 0) 0 (IncTop.starWeight Sset ω)) ≤
        ENNReal.ofReal (Cm * (Cm * δ) ^ n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
    intro Q hwf hsz LG hdec h0 H' hH' Sset ω cω hpres
    have hF : ∀ z, spatialNorm (40*d) (40*d) (addrFam H' z) ≤ ENNReal.ofReal 1 := fun z => by
      have := hH' z
      rwa [NormBridgeScratch.SNormR_eq_spatialNorm] at this
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine (couple_zero_star_bound L γ δ (1/4) hd1 hwf (by omega) LG h0 hdec zero_le_one H' hF _ hT
        Sset ω cω hpres).trans (mul_le_mul' ?_ le_rfl)
      simp only [pow_zero, mul_one]
      exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    · refine (Hc L hLc δ hδ2 hδ1 n hnpos hn Q hwf hsz LG hdec h0 H' hF _ hT Sset ω cω hpres).trans
        (mul_le_mul' (hmono Cc (zero_le_one.trans hCc) ((le_max_left _ _).trans (le_max_left _ _))) le_rfl)
  have hunitT : ∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
      X.DecodesTree LG.garden → (∀ a, LG.layer a = 0) → ∀ H' : LeafProfiles 1 d,
      (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
      mixedRestrictionNorm (1/4) (30 * d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H' (fun _ => ts.1 0) (ts.1 1) k.1
          (fun _ => 0) 0 (IncTop.starWeight Sset ω)) ≤
        ENNReal.ofReal (Cm * (Cm * δ) ^ n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
    intro X hwf hsz LG hdec h0 H' hH' Sset ω cω hpres
    have hF : ∀ z, spatialNorm (40*d) (40*d) (addrFam H' z) ≤ ENNReal.ofReal 1 := fun z => by
      have := hH' z
      rwa [NormBridgeScratch.SNormR_eq_spatialNorm] at this
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine (tree_zero_star_bound L γ δ (1/4) hd hwf (by omega) LG hdec h0 hL1 hδ.1.ne' zero_le_one H' hF
        Sset ω cω hpres).trans (mul_le_mul' ?_ le_rfl)
      simp only [pow_zero, mul_one]
      exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    · refine (Ht L hLt δ hδ2 hδ1 n hnpos hn X hwf hsz LG hdec h0 H' hF Sset ω cω hpres).trans
        (mul_le_mul' (hmono Ct (zero_le_one.trans hCt) ((le_max_right _ _).trans (le_max_left _ _))) le_rfl)
  refine ⟨?_, ?_⟩
  · intro r Q hwf hsz LG hdec hlay H B hctl Sset ω cω hpres
    have hctl0 : LeafwiseControlled (layer0 LG) H B := hctl
    have hdec0 : Q.Decodes (layer0 LG).garden := hdec
    have hfin : ENNReal.ofReal (Cm * (Cm * δ) ^ n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
    have hsc := coupleW_kernel_scaled L γ δ (1/4) hd1 (layer0 LG) (IncTop.starWeight Sset ω) (timeBox 0 0) _
      hfin (fun H' hH' => hunitC Q hwf hsz (layer0 LG) hdec0 (fun _ => rfl) H' hH' Sset ω cω hpres) H B hctl0
    refine (coupleW_kernel_item_le L γ δ H hdec hlay (IncTop.starWeight Sset ω) hsc).trans ?_
    have e0 : leafSizeProduct (layer0 LG) B = leafSizeProduct LG B := rfl
    have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    rw [e0]
    refine le_trans ?_ (star_bound_absorb n hK1 hCm0 rfl hδ0 hβ0 _)
    exact le_mul_of_one_le_left bot_le (by simpa using ENNReal.ofReal_le_ofReal hK1)
  · intro r q'' X hq hwf hsz LG hdec hlay H B hctl Sset ω cω hpres
    have hctl0 : LeafwiseControlled (layer0 LG) H B := hctl
    have hdec0 : X.DecodesTree (layer0 LG).garden := hdec
    have hfin : ENNReal.ofReal (Cm * (Cm * δ) ^ n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
    have hsc := treeW_kernel_scaled L γ δ (1/4) hd1 (layer0 LG) (IncTop.starWeight Sset ω) (timeBoxGt 0 0) _
      hfin (fun H' hH' => hunitT X hwf hsz (layer0 LG) hdec0 (fun _ => rfl) H' hH' Sset ω cω hpres) H B hctl0
    have hFs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k : Mom d,
        Summable fun m : Fin d → ℤ => |H ℓ.1 (k + latticePoint L m)| := fun ℓ hℓ k =>
      summable_abs_coset_of_SNormR (by linarith) (by omega : d + 1 ≤ 40 * d)
        (B ℓ.1).2 (H ℓ.1) (hctl ℓ hℓ) k
    refine (treeW_kernel_item_le L γ δ H hdec hFs hq hlay (IncTop.starWeight Sset ω) _
      (norm_starWeight_le Sset ω cω hpres) hθ0 (Λ := 30 * d) (by omega) hsc).trans ?_
    have e0 : leafSizeProduct (layer0 LG) B = leafSizeProduct LG B := rfl
    have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    rw [e0]
    have htr : traceConst (r := 2) (1/4 : ℝ) chiUnit = ENNReal.ofReal K := by
      rw [hKdef, Ktr', ENNReal.ofReal_toReal (traceConst_ne_top' _)]
    rw [htr]
    exact star_bound_absorb n hK1 hCm0 rfl hδ0 hβ0 _

end WaveTurbulence.Flower.FiltCoh
