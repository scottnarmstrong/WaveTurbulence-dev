/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleStarBound
public import WaveTurbulence.Foundations.Flower.FiltCoh.SingleLayer

/-! # FILT-COH (b): multiplied couple kernels — leafwise scaling and layer translation

`kernelLeavesW_scale'` (homogeneity in each leaf), `kernelLeavesW_couple_shift` (main's `KQstarLeaf_shift` with a
decoration multiplier: the multiplier does not see times), and the multiplied versions of milestone (a)'s
`couple_kernel_scaled` / `couple_kernel_item_le`. With `exists_couple_star_bound_theta` they give
`couple_star_layer_bound`: a single-layer couple in layer `r` with individual leaf bounds and star weights. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.Induct WaveTurbulence.RegAsymp MeasureTheory Finset Links Incoh IncohInst WaveTurbulence.Fourier WaveTurbulence.Regref
open WaveTurbulence.RA1Leafwise LGSpine TTree
open scoped ENNReal

variable {d : ℕ}

/-- Homogeneity of the multiplied kernel in each input leaf. -/
theorem kernelLeavesW_scale' {w : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H H' : LeafProfiles w d)
    (β : Fin w × Path → ℝ) (h : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = fun k => β ℓ.1 * H' ℓ.1 k)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m =
      ((∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 : ℝ) : ℂ) *
        Flower.Stage1W.kernelLeavesW L γ δ LG H' up s k₀ nroot nfl m := by
  unfold Flower.Stage1W.kernelLeavesW
  rw [← tsum_mul_left, ← tsum_mul_left]
  conv_rhs => rw [← tsum_mul_left]
  refine tsum_congr fun κ => ?_
  have hprod : ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) =
      ((∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 : ℝ) : ℂ) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H' ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) := by
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    rw [h ℓ hℓ]
    push_cast
    ring
  rw [hprod]
  ring

/-- Main's `KQstarLeaf_shift` for the multiplied couple kernel. -/
theorem kernelLeavesW_couple_shift (L γ δ : ℝ) (LG : LayeredGarden 2) (hG : IsCouple LG.garden)
    (H : LeafProfiles 2 d) (r : ℕ) (hr : ∀ a, LG.layer a = r) (t s : ℝ) (k : Mom d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 m =
      Flower.Stage1W.kernelLeavesW L γ δ (layer0 LG) H
        (fun b => if b.1.1 = 0 then t - r else s - r) 0 k (fun _ => 0) 0 m := by
  unfold Flower.Stage1W.kernelLeavesW
  congr 1
  refine tsum_congr fun κ => ?_
  have hpair : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    simp only [cosetDecoration, κ.2.1.2 ℓ]
  have hroot : cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 0) =
      cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 1) := by
    simp only [cosetDecoration, κ.2.2.1 0, κ.2.2.1 1]
  rw [phaseIntegral_shift L γ δ LG hG.1 r hr _ _ (sum_sign_omega_couple LG.garden hG _ hpair hroot)]
  have hup : (fun b : GBranch LG.garden.tree => (if b.1.1 = 0 then t else s) - (r : ℝ)) =
      (fun b => if b.1.1 = 0 then t - r else s - r) := by
    funext b
    split_ifs <;> rfl
  rw [hup]

/-- Leafwise scaling of a multiplied couple-kernel bound. -/
theorem coupleW_kernel_scaled (L γ δ θ : ℝ) (hd : 1 ≤ d) (LG : LayeredGarden 2)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (T : Set (Fin 2 → ℝ)) (X : ℝ≥0∞) (hX : X ≠ ⊤)
    (hRA : ∀ H' : LeafProfiles 2 d, (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      mixedRestrictionNorm θ (30 * d) (30 * d) T Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H'
          (fun b => if b.1.1 = 0 then ts.1 0 else ts.1 1) 0 k.1 (fun _ => 0) 0 m) ≤ X)
    (H : LeafProfiles 2 d) (B : Fin 2 × Path → NNReal) (hH : LeafwiseControlled LG H B) :
    mixedRestrictionNorm θ (30 * d) (30 * d) T Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H
          (fun b => if b.1.1 = 0 then ts.1 0 else ts.1 1) 0 k.1 (fun _ => 0) 0 m) ≤
      ENNReal.ofReal (leafSizeProduct LG B) * X := by
  classical
  unfold leafSizeProduct
  refine le_of_forall_eps (inputLeaves LG.garden) (fun ℓ => (B ℓ.1 : ℝ)) _ X hX ?_
  intro ε hε
  let S : Finset (Fin 2 × Path) := (inputLeaves LG.garden).image (fun ℓ => ℓ.1)
  let β : Fin 2 × Path → ℝ := fun z => (B z : ℝ) + ε
  have hβ0 : ∀ z, 0 < β z := fun z => by have := (B z).2; simp only [β]; positivity
  have hβne : ∀ z, β z ≠ 0 := fun z => (hβ0 z).ne'
  let H' := normProfile S β H
  have hnorm : ∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1 := by
    refine normProfile_norm_le (S := S) (B := fun z => (B z : ℝ)) hd (fun z => (B z).2) (fun z => ?_)
      hβ0 ?_
    · simp only [β]; linarith
    · intro z hz
      obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hz
      exact hH ℓ hℓ
  have hscale : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = fun k => β ℓ.1 * H' ℓ.1 k := fun ℓ hℓ =>
    normProfile_scale hβne (Finset.mem_image_of_mem _ hℓ)
  set P : ℝ := ∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 with hP
  have hPpos : 0 < P := Finset.prod_pos fun ℓ _ => hβ0 _
  have hD : (fun (ts : T) (k : (Set.univ : Set (Mom d))) =>
        Flower.Stage1W.kernelLeavesW L γ δ LG H
          (fun b => if b.1.1 = 0 then ts.1 0 else ts.1 1) 0 k.1 (fun _ => 0) 0 m) =
      fun ts k => (P : ℂ) • Flower.Stage1W.kernelLeavesW L γ δ LG H'
          (fun b => if b.1.1 = 0 then ts.1 0 else ts.1 1) 0 k.1 (fun _ => 0) 0 m := by
    funext ts k
    rw [kernelLeavesW_scale' L γ δ LG H H' β hscale]
    simp only [smul_eq_mul, hP]
  rw [hD]
  have hc : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  refine (mixedRestrictionNorm_smul_le hc θ _ _ _ _ _).trans ?_
  rw [show ‖(P : ℂ)‖ₑ = ENNReal.ofReal P by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos]]
  exact mul_le_mul' le_rfl (hRA H' hnorm)

/-- Translation of a multiplied couple-kernel bound from layer `0` to layer `r`. -/
theorem coupleW_kernel_item_le (L γ δ : ℝ) (H : LeafProfiles 2 d) {Q : RegCpl} {LG : LayeredGarden 2}
    (hdec : Q.Decodes LG.garden) {r : ℕ} (hlay : ∀ a, LG.layer a = r)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) {θ : ℝ} {Λ : ℕ} {M : ℝ≥0∞}
    (hM : mixedRestrictionNorm θ Λ Λ (timeBox 0 0) Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ (layer0 LG) H
          (fun b => if b.1.1 = 0 then ts.1 0 else ts.1 1) 0 k.1 (fun _ => 0) 0 m) ≤ M) :
    XNormRestr θ Λ Λ (timeBox r r) Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H
          (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 m) ≤ M := by
  refine le_trans ?_ ((XNormRestr_eq_mixedRestrictionNorm θ Λ Λ (timeBox 0 0)
    (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ (layer0 LG) H
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 m)).le.trans hM)
  refine XNormRestr_shift_le θ Λ Λ (fun _ => (r : ℝ)) (fun ts hts => sub_mem_timeBox_self' hts)
    fun ts _ k _ => ?_
  exact kernelLeavesW_couple_shift L γ δ LG hdec.1 H r hlay (ts 0) (ts 1) k m

/-- **Single-layer star-weighted couples in layer `r`**, individual leaf bounds, positive order: the
`X^{θ,30d,30d}` bound `Ck (Ck δ)^n ∏ cω ∏ B_ℓ` for every `0 ≤ θ ≤ 1 - η/8`. -/
theorem couple_star_layer_bound (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8) :
    ∃ Ck : ℝ, 1 ≤ Ck ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ Q : RegCpl, Q.wf = true → Q.size = 2*n →
      ∀ (LG : LayeredGarden 2), Q.Decodes LG.garden → ∀ r : ℕ, (∀ a, LG.layer a = r) →
      ∀ (H : LeafProfiles 2 d) (B : Fin 2 × Path → NNReal), LeafwiseControlled LG H B →
      ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
      XNormRestr θ (30*d) (30*d) (timeBox r r) Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H
          (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 (IncTop.starWeight Sset ω)) ≤
        ENNReal.ofReal (Ck*(Ck*δ)^n) * (∏ a ∈ Sset, ENNReal.ofReal (cω a)) *
          ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨Ck, hCk, hst⟩ := exists_couple_star_bound_theta hd hγ hη0 hη hηγ hθ0 hθ zero_le_one
  refine ⟨Ck, hCk, fun Aorder => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hst Aorder
  refine ⟨L₀, fun L hL δ hδ hδ1 n hn hnlog Q hwf hsz LG hdec r hlay H B hctl Sset ω cω hpres => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hT : ∀ t ∈ timeBox (0:ℝ) 0, ∀ i, t i ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht i
    have hh : t 0 ∈ Set.Icc (0:ℝ) 1 ∧ t 1 ∈ Set.Icc (0:ℝ) 1 := by
      simpa only [timeBox,Set.mem_ofPred_eq,zero_add] using ht
    fin_cases i
    · exact hh.1
    · exact hh.2
  have hctl0 : LeafwiseControlled (layer0 LG) H B := hctl
  have hdec0 : Q.Decodes (layer0 LG).garden := hdec
  have hfin : ENNReal.ofReal (Ck*(Ck*δ)^n) * (∏ a ∈ Sset, ENNReal.ofReal (cω a)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  have hsc := coupleW_kernel_scaled L γ δ θ hd1 (layer0 LG) (IncTop.starWeight Sset ω) (timeBox 0 0) _ hfin
    (fun H' hH' => by
      have hF : ∀ z, spatialNorm (40*d) (40*d) (addrFam H' z) ≤ ENNReal.ofReal 1 := fun z => by
        have := hH' z
        rwa [NormBridgeScratch.SNormR_eq_spatialNorm] at this
      exact hL₀ L hL δ hδ hδ1 n hn hnlog Q hwf hsz (layer0 LG) hdec0 (fun _ => rfl) H' hF
        (timeBox 0 0) hT Sset ω cω hpres) H B hctl0
  refine (coupleW_kernel_item_le L γ δ H hdec hlay (IncTop.starWeight Sset ω) hsc).trans ?_
  have e0 : leafSizeProduct (layer0 LG) B = leafSizeProduct LG B := rfl
  rw [e0, mul_comm]

end WaveTurbulence.Flower.FiltCoh
