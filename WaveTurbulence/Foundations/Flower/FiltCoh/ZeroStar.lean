/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.ZeroOrder
public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleStarLayer
public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Top.GardenPresentation
public import WaveTurbulence.Foundations.Incoh.SpatialInputBounds

/-! # FILT-COH (c1): star-weighted objects of order zero

At order zero every node of a layer-zero couple or paired tree is a root, so every decoration is the constant `k`
and the star weight is the diagonal value `V(k) = ∏_{a ∈ S} ω_a(k, k, k, k)`. This is the value at the zero internal
momentum of INC-TOP's star root measure with zero rows, i.e. a root-character mixture `∫ amp · e(⟨Ξ, k⟩)`. Its
`k`-derivatives cost the total-frequency moment (`IncTop.mixedFourierNorm_rootProductMixture_le` with the trivial
source space `Unit`), so the kernel `V(k) · H(k)` (couples) or `V(k)` (trees) has the order-zero bound times
`∏ c_ω`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory Set WaveTurbulence.Fourier
open WaveTurbulence.Flower.IncTop
open scoped ENNReal

variable {d : ℕ}

/-- Jets of a root-modulated `C^N` function are continuous in the root frequency. -/
theorem continuous_jet_rootChar_mul {N j : ℕ} {F : Mom d → ℂ} (hF : ContDiff ℝ N F) (hj : j ≤ N)
    (k : Mom d) : Continuous (fun Ξ : Mom d => iteratedFDeriv ℝ j (fun k => rootChar Ξ k * F k) k) := by
  let Φ : Mom d × Mom d → ℂ := fun p => rootChar p.1 p.2 * F p.2
  have hc := Cut2A.character_smooth.comp
    ((contDiff_fst (𝕜 := ℝ) (E := Mom d) (F := Mom d)).inner ℝ contDiff_snd)
  have hΦ : ContDiff ℝ N Φ := (hc.of_le (by exact_mod_cast le_top)).mul (hF.comp contDiff_snd)
  have he (Ξ : Mom d) : iteratedFDeriv ℝ j (fun k => rootChar Ξ k * F k) k =
      (iteratedFDeriv ℝ j Φ (Ξ, k)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (Mom d) (Mom d)) := by
    have h1 : (fun k => rootChar Ξ k * F k) =
        (fun z : Mom d × Mom d => Φ (z + (Ξ, 0))) ∘ ContinuousLinearMap.inr ℝ (Mom d) (Mom d) := by
      funext k
      simp [Φ]
    have hΨ : ContDiff ℝ N (fun z : Mom d × Mom d => Φ (z + (Ξ, 0))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hΨ _ (by exact_mod_cast hj),
      iteratedFDeriv_comp_add_right]
    simp
  simp_rw [he]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp
    ((hΦ.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp (continuous_id.prodMk continuous_const))

/-- **The root-character mixture at zero internal momentum, times a weighted `C^J` function, on a subset of the
unit square**: `‖V(k) F(k)‖ ≤ (2(2π))^J v · momentMass_J · ‖χ_□‖_{X^θ}`. -/
theorem rootValue_restriction_le {n : ℕ} {α : Type} [MeasurableSpace α] (G : RootMeasure d n α)
    {J W : ℕ} (θ : ℝ) {F : Mom d → ℂ} (hF : ContDiff ℝ J F) {v : ℝ} (hv : 0 ≤ v)
    (hb : ∀ j ≤ J, ∀ k, momentumBracket k ^ W * ‖iteratedFDeriv ℝ j F k‖ ≤ v)
    (hfin : G.momentMass J < ⊤) (T : Set (Fin 2 → ℝ)) (hT : ∀ t ∈ T, ∀ i, t i ∈ Icc (0:ℝ) 1) :
    mixedRestrictionNorm θ J W T Set.univ (fun _ k => (G.at k.val).value 0 * F k.val) ≤
      ENNReal.ofReal (rootJetConstant J) * (ENNReal.ofReal v * G.momentMass J) *
        timeFourierNorm θ unitSquareCutoff := by
  have hH : eLpNorm unitSquareCutoff 1 < ⊤ :=
    (memLp_one_iff_integrable.mpr integrable_unitSquareCutoff).eLpNorm_lt_top
  have hm : ∀ j ≤ J, ∀ k, StronglyMeasurable (fun u : Unit × α =>
      iteratedFDeriv ℝ j (fun k => rootChar (G.root u.2) k * F k) k) := fun j hj k =>
    (continuous_jet_rootChar_mul hF hj k).comp_stronglyMeasurable
      (G.root_measurable.comp measurable_snd).stronglyMeasurable
  have hK : StronglyMeasurable (fun z : (Fin 2 → ℝ) × (Unit × α) => unitSquareCutoff z.1) :=
    (contDiff_unitSquareCutoff.continuous.measurable.comp measurable_fst).stronglyMeasurable
  have hfull := mixedFourierNorm_rootProductMixture_le (N := J) (M := W) (Measure.dirac ()) G θ
    (fun k (_ : Unit) => F k) (fun _ => v) (fun t (_ : Unit × α) => unitSquareCutoff t)
    (fun _ => hF) hm (integrable_const v) measurable_const (fun _ => hv) (fun j hj k _ => hb j hj k)
    hK (fun _ => integrable_unitSquareCutoff) hH (fun _ => le_rfl) (fun _ => le_rfl) hfin
  refine (mixedRestrictionNorm_le_extension _ ?_).trans (hfull.trans ?_)
  · intro t k
    have hmeas : Measurable (fun a : α => (G.at k.val).amplitude a) :=
      G.amplitude_measurable.mul (measurable_rootChar G.root_measurable k.val)
    have hae : AEStronglyMeasurable (fun u : Unit × α =>
        (G.at k.val).amplitude u.2 * F k.val * unitSquareCutoff t.val) (Measure.map (Prod.mk ()) G.base.μ) :=
      (((hmeas.comp measurable_snd).mul_const _).mul_const _).aestronglyMeasurable
    rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable hae]
    rw [unitSquareCutoff_eq_one (hT t.val t.property)]
    simp only [mul_one]
    rw [integral_mul_const, RootMeasure.at_value]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
    rfl
  · rw [lintegral_dirac]

/-- The diagonal star value is the zero-row star root measure at zero internal momentum. -/
theorem starWeight_const_eq_value (J : ℕ) {w : ℕ} {T : Fin w → TTree} (S : Finset (GNode T))
    (ω : GNode T → Star d → ℂ) (c : GNode T → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a)) (k : Mom d) :
    starWeight S ω (fun _ => k) =
      ((starRootMeasure J S ω c h (n := 0) (fun _ _ => 0)).at k).value 0 := by
  rw [starRootMeasure_value]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  unfold starMomenta rowStar rowLinear
  simp

/-- An integer decoration with zero roots of a garden of leaves vanishes. -/
theorem genDec_zero_of_leaves {w : ℕ} {G : Garden w} (hl : ∀ j, G.tree j = TTree.leaf)
    (κ : GenDecoration G d (fun _ => 0) 0) (a : GNode G.tree) : κ.1 a = 0 := by
  have h2 : a.1.2 = [] := by
    have hm := a.2
    rw [hl a.1.1] at hm
    simpa [TTree.nodes] using hm
  have ha : a = GNode.root G.tree a.1.1 := Subtype.ext (Prod.ext rfl h2)
  rw [ha, κ.2.2.1]

/-- On a garden of leaves the star-weighted kernel is the diagonal star value times the plain kernel. -/
theorem kernelLeavesW_star_leaves {w : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (hl : ∀ j, LG.garden.tree j = TTree.leaf) (H : LGSpine.LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : Mom d) (J : ℕ) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (c : GNode LG.garden.tree → ℝ)
    (h : ∀ a ∈ S, StarPresented J (ω a) (c a)) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k (fun _ => 0) 0 (starWeight S ω) =
      ((starRootMeasure J S ω c h (n := 0) (fun _ _ => 0)).at k).value 0 *
        LGSpine.kernelLeaves L γ δ LG H up s k (fun _ => 0) 0 := by
  unfold Flower.Stage1W.kernelLeavesW LGSpine.kernelLeaves
  have hc (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
      starWeight S ω (cosetDecoration LG.garden L k κ.1) =
        ((starRootMeasure J S ω c h (n := 0) (fun _ _ => 0)).at k).value 0 := by
    have he : cosetDecoration LG.garden L k κ.1 = fun _ => k := by
      funext a
      simp only [cosetDecoration, genDec_zero_of_leaves hl κ a]
      have : latticePoint L (0 : Fin d → ℤ) = 0 := by
        ext j
        simp [latticePoint]
      rw [this, add_zero]
    rw [he, starWeight_const_eq_value J S ω c h k]
  simp_rw [hc]
  rw [tsum_mul_left]
  ring

/-- `⟨k⟩^{30d}`-weighted jets of a `𝔖^{40d,40d}` profile. -/
theorem weighted_jet_le {f : Mom d → ℂ} {B : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B)
    (h : spatialNorm (40*d) (40*d) f ≤ ENNReal.ofReal B) :
    ∀ j ≤ 30*d, ∀ k, momentumBracket k ^ (30*d) * ‖iteratedFDeriv ℝ j f k‖ ≤ (d:ℝ)^(30*d) * B := by
  intro j hj k
  have hb := Incoh.norm_iteratedFDeriv_le_of_spatialNorm hB h (by omega) k (j := j)
  have h1 : 1 ≤ momentumBracket k := Incoh.one_le_momentumBracket k
  have hw : 0 < momentumBracket k ^ (40*d) := pow_pos (by linarith) _
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdj : (d:ℝ)^j ≤ (d:ℝ)^(30*d) := pow_le_pow_right₀ hd1 hj
  have hpow : momentumBracket k ^ (30*d) ≤ momentumBracket k ^ (40*d) :=
    pow_le_pow_right₀ h1 (by omega)
  calc momentumBracket k ^ (30*d) * ‖iteratedFDeriv ℝ j f k‖
      ≤ momentumBracket k ^ (30*d) * ((d:ℝ)^j * (B / momentumBracket k ^ (40*d))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (d:ℝ)^j * B * (momentumBracket k ^ (30*d) / momentumBracket k ^ (40*d)) := by ring
    _ ≤ (d:ℝ)^j * B * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one hw).mpr hpow) (by positivity)
    _ ≤ (d:ℝ)^(30*d) * B := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hdj hB

/-- The order-zero constant `(2(2π))^{30d} d^{30d} ‖χ_□‖_{X^θ}`. -/
@[expose] def zeroStarConst (d : ℕ) (θ : ℝ) : ℝ :=
  rootJetConstant (30*d) * (d:ℝ)^(30*d) * (timeFourierNorm θ unitSquareCutoff).toReal

theorem zeroStarConst_nonneg (d : ℕ) (θ : ℝ) : 0 ≤ zeroStarConst d θ := by
  unfold zeroStarConst
  have := rootJetConstant_pos (30*d)
  positivity

/-- **Order-zero couples with star weights, layer zero.** -/
theorem couple_zero_star_bound (L γ δ θ : ℝ) (hd : 1 ≤ d) {Q : RegCpl} (hwf : Q.wf = true)
    (hsize : Q.size = 0) (LG : LayeredGarden 2) (h0 : ∀ a, LG.layer a = 0) (hQ : Q.Decodes LG.garden)
    {Binput : ℝ} (hBi : 0 ≤ Binput) (H : LGSpine.LeafProfiles 2 d)
    (hF : ∀ z, spatialNorm (40*d) (40*d) (RA1Leafwise.addrFam H z) ≤ ENNReal.ofReal Binput)
    (T : Set (Fin 2 → ℝ)) (hT : ∀ t ∈ T, ∀ i, t i ∈ Icc (0:ℝ) 1)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, StarPresented (30*d) (ω a) (cω a)) :
    mixedRestrictionNorm θ (30*d) (30*d) T Set.univ
        (fun t k => Flower.Stage1W.kernelLeavesW L γ δ LG H
          (fun b => if b.1.1 = 0 then t.val 0 else t.val 1) 0 k.val (fun _ => 0) 0 (starWeight S ω)) ≤
      ENNReal.ofReal (zeroStarConst d θ * Binput) * ∏ a ∈ S, ENNReal.ofReal (cω a) := by
  obtain rfl := RA1Leafwise.regCpl_eq_triv_of_wf_size_zero Q hwf hsize
  have hl : ∀ j, LG.garden.tree j = TTree.leaf := by
    intro j
    fin_cases j
    · exact hQ.2.1
    · exact hQ.2.2.1
  set G := starRootMeasure (30*d) S ω cω hpres (n := 0) (fun _ _ => 0) with hG
  have hfun : (fun (t : T) (k : (Set.univ : Set (Mom d))) => Flower.Stage1W.kernelLeavesW L γ δ LG H
      (fun b => if b.1.1 = 0 then t.val 0 else t.val 1) 0 k.val (fun _ => 0) 0 (starWeight S ω)) =
      fun t k => (G.at k.val).value 0 * RA1Leafwise.addrFam H (0,[]) k.val := by
    funext t k
    rw [kernelLeavesW_star_leaves L γ δ LG hl H _ 0 k.val (30*d) S ω cω hpres]
    have hc := RA1Leafwise.coupleLeaves_triv L γ δ H LG h0 hQ (hT t.val t.property 0)
      (hT t.val t.property 1) k.val
    unfold LGSpine.coupleLeaves at hc
    rw [hc]
    rfl
  rw [hfun]
  have hF0 := hF (0,[])
  have hcd : ContDiff ℝ (30*d) (RA1Leafwise.addrFam H (0,[])) :=
    (Incoh.contDiff_of_spatialNorm_le (by omega) hF0).of_le (by exact_mod_cast (by omega : 30*d ≤ 40*d))
  have hmom := starRootMeasure_momentMass_le (30*d) S ω cω hpres (n := 0) (fun _ _ => 0)
  have hfin : G.momentMass (30*d) < ⊤ :=
    hmom.trans_lt (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top)
  refine (rootValue_restriction_le G θ hcd (by positivity) (weighted_jet_le hd hBi hF0) hfin T hT).trans ?_
  have hτ := timeFourierNorm_unitSquareCutoff_lt_top θ
  rw [← ENNReal.ofReal_toReal hτ.ne]
  calc ENNReal.ofReal (rootJetConstant (30*d)) * (ENNReal.ofReal ((d:ℝ)^(30*d) * Binput) *
        G.momentMass (30*d)) * ENNReal.ofReal (timeFourierNorm θ unitSquareCutoff).toReal
      ≤ ENNReal.ofReal (rootJetConstant (30*d)) * (ENNReal.ofReal ((d:ℝ)^(30*d) * Binput) *
        ∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (timeFourierNorm θ unitSquareCutoff).toReal := by
        gcongr
    _ = ENNReal.ofReal (zeroStarConst d θ * Binput) * ∏ a ∈ S, ENNReal.ofReal (cω a) := by
        have h1 := (rootJetConstant_pos (30*d)).le
        have h2 : (0:ℝ) ≤ (d:ℝ)^(30*d) * Binput := by positivity
        rw [zeroStarConst, show rootJetConstant (30*d) * (d:ℝ)^(30*d) *
            (timeFourierNorm θ unitSquareCutoff).toReal * Binput =
            rootJetConstant (30*d) * ((d:ℝ)^(30*d) * Binput) *
            (timeFourierNorm θ unitSquareCutoff).toReal by ring,
          ENNReal.ofReal_mul (mul_nonneg h1 h2), ENNReal.ofReal_mul h1]
        ring

/-- **Order-zero paired trees with star weights, layer zero.** -/
theorem tree_zero_star_bound (L γ δ θ : ℝ) (hd : 3 ≤ d) {X : RegChain} (hwf : X.wf = true)
    (hsize : X.size = 0) (LG : LayeredGarden 1) (hX : X.DecodesTree LG.garden) (h0 : ∀ a, LG.layer a = 0)
    (hL : 1 ≤ L) (hδ : δ ≠ 0) {Binput : ℝ} (hBi : 0 ≤ Binput) (H : LGSpine.LeafProfiles 1 d)
    (hF : ∀ z, spatialNorm (40*d) (40*d) (RA1Leafwise.addrFam H z) ≤ ENNReal.ofReal Binput)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, StarPresented (30*d) (ω a) (cω a)) :
    mixedRestrictionNorm θ (30*d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts.val 0) (ts.val 1) k.val
          (fun _ => 0) 0 (starWeight S ω)) ≤
      ENNReal.ofReal (zeroStarConst d θ) * ∏ a ∈ S, ENNReal.ofReal (cω a) := by
  have hnil : X = RegChain.nil := by
    cases X with
    | nil => rfl
    | pair m Qr Qg inner rest => simp only [RegChain.size] at hsize; omega
  have hl : ∀ j, LG.garden.tree j = TTree.leaf := by
    intro j
    fin_cases j
    have h1 := hX.1
    rw [hnil] at h1
    exact h1
  set G := starRootMeasure (30*d) S ω cω hpres (n := 0) (fun _ _ => 0) with hG
  have hbox (t : timeBoxGt 0 0) :
      ((t.val 0∈Icc (0:ℝ) 1) ∧ (t.val 1∈Icc (0:ℝ) 1)) ∧ t.val 1<t.val 0 := by
    simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using t.property
  have hfun : (fun (t : timeBoxGt 0 0) (k : (Set.univ : Set (Mom d))) =>
      Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t.val 0) (t.val 1) k.val
        (fun _ => 0) 0 (starWeight S ω)) =
      fun t k => (G.at k.val).value 0 * (fun _ => (1:ℂ)) k.val := by
    funext t k
    rw [kernelLeavesW_star_leaves L γ δ LG hl H _ _ k.val (30*d) S ω cω hpres]
    have hk := RA1Leafwise.KTstar_eq_app_of_tree_size_zero hd hwf hsize LG hX h0 hL δ γ hδ hBi hF
      (hbox t).1.2.1 (hbox t).2 (hbox t).1.1.2 k.val
    unfold LGSpine.treeLeaves at hk
    rw [hk]
    subst hnil
    rw [PL234.LeafApp.tree_nil]
  rw [hfun]
  have hb : ∀ j ≤ 30*d, ∀ k : Mom d, momentumBracket k ^ 0 *
      ‖iteratedFDeriv ℝ j (fun _ : Mom d => (1:ℂ)) k‖ ≤ 1 := by
    intro j _ k
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [iteratedFDeriv_const_of_ne hj.ne' (1:ℂ)]
      simp
  have hmom := starRootMeasure_momentMass_le (30*d) S ω cω hpres (n := 0) (fun _ _ => 0)
  have hfin : G.momentMass (30*d) < ⊤ :=
    hmom.trans_lt (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top)
  refine (rootValue_restriction_le G θ contDiff_const zero_le_one hb hfin _ (fun t ht i => by
    have hh : ((t 0∈Icc (0:ℝ) 1) ∧ (t 1∈Icc (0:ℝ) 1)) ∧ t 1<t 0 := by
      simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using ht
    fin_cases i
    · exact hh.1.1
    · exact hh.1.2)).trans ?_
  have hτ := timeFourierNorm_unitSquareCutoff_lt_top θ
  rw [← ENNReal.ofReal_toReal hτ.ne]
  have h1 := (rootJetConstant_pos (30*d)).le
  have hd1 : (1:ℝ) ≤ (d:ℝ)^(30*d) := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ d))
  calc ENNReal.ofReal (rootJetConstant (30*d)) * (ENNReal.ofReal 1 * G.momentMass (30*d)) *
        ENNReal.ofReal (timeFourierNorm θ unitSquareCutoff).toReal
      ≤ ENNReal.ofReal (rootJetConstant (30*d)) * (ENNReal.ofReal ((d:ℝ)^(30*d)) *
        ∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (timeFourierNorm θ unitSquareCutoff).toReal := by
        gcongr
    _ = ENNReal.ofReal (zeroStarConst d θ) * ∏ a ∈ S, ENNReal.ofReal (cω a) := by
        rw [zeroStarConst, ENNReal.ofReal_mul (mul_nonneg h1 (by positivity)), ENNReal.ofReal_mul h1]
        ring

end WaveTurbulence.Flower.FiltCoh
