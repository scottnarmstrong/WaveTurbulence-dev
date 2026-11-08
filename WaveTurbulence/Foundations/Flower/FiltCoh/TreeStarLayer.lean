/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarFinal
public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleStarLayer
public import WaveTurbulence.Foundations.Flower.FiltCoh.ZeroStar
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotKer

/-! # FILT-COH (c3): multiplied tree kernels — layer shift, relayering, freezing, trace

Main's `KTstarLeaf_shift`, `KTstarLeaf_relayer`, `KTstarLeaf_indep_of_le` for `kernelLeavesW` with a decoration
multiplier (the multiplier sees neither times nor layers), the multiplied versions of milestone (a)'s
`tree_kernel_scaled` / `tree_kernel_item_le`, and `tree_star_layer_bound`: a single-layer paired tree in layer `r`
whose lone leaf lies in a layer `q'' ≤ r`, individual leaf bounds, any star weights. Also the uniform bound
`norm_starWeight_le` of a presented star weight (continuity of the multiplied kernels in time). -/

public section
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory Set Filter TTree WaveTurbulence.Fourier WaveTurbulence.Regref
open WaveTurbulence.RA1Leafwise LGSpine
open scoped ENNReal Topology

variable {d : ℕ}

/-- A presented star weight is bounded by its constant. -/
theorem norm_star_le {J : ℕ} {ω : IncTop.Star d → ℂ} {c : ℝ} (h : IncTop.StarPresented J ω c)
    (y : IncTop.Star d) : ‖ω y‖ ≤ max c 0 := by
  obtain ⟨α, _, M, hmom, hval⟩ := h
  rw [← hval y]
  refine (M.norm_value_le y).trans ?_
  have hmass : ENNReal.ofReal M.mass ≤ ENNReal.ofReal c := by
    refine le_trans ?_ hmom
    unfold Cut2A.SpatialMeasure.mass IncTop.starMoment
    rw [ofReal_integral_norm_eq_lintegral_enorm M.amplitude_integrable]
    refine lintegral_mono fun a => le_mul_of_one_le_left bot_le ?_
    exact ENNReal.one_le_ofReal.mpr (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))
  have hm0 : 0 ≤ M.mass := integral_nonneg fun _ => norm_nonneg _
  rcases le_total 0 c with hc | hc
  · exact ((ENNReal.ofReal_le_ofReal_iff hc).mp hmass).trans (le_max_left _ _)
  · rw [ENNReal.ofReal_of_nonpos hc, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hmass
    exact hmass.trans (le_max_right _ _)

/-- **A presented star weight is uniformly bounded.** -/
theorem norm_starWeight_le {J w : ℕ} {T : Fin w → TTree} (S : Finset (GNode T))
    (ω : GNode T → IncTop.Star d → ℂ) (c : GNode T → ℝ) (h : ∀ a ∈ S, IncTop.StarPresented J (ω a) (c a))
    (κ : GNode T → Mom d) : ‖IncTop.starWeight S ω κ‖ ≤ ∏ a ∈ S, max (c a) 0 := by
  unfold IncTop.starWeight
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun a ha => norm_star_le (h a ha) _

/-- Main's `KTstarLeaf_shift` for the multiplied tree kernel. -/
theorem kernelLeavesW_tree_shift (L γ δ : ℝ) (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (H : LeafProfiles 1 d) (r : ℕ) (hr : ∀ a, LG.layer a = r) (t s : ℝ)
    (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 m =
      Flower.Stage1W.kernelLeavesW L γ δ (layer0 LG) H (fun _ => t - r) (s - r) k (fun _ => 0) 0 m := by
  have hT := LGSpine.no_flowerParent_of_pairedTree LG.garden (isPairedTree_of_decodesTree hX)
  unfold Flower.Stage1W.kernelLeavesW
  congr 1
  refine tsum_congr fun κ => ?_
  have hpair : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    simp only [cosetDecoration, κ.2.1.2 ℓ]
  have hlone : cosetDecoration LG.garden L k κ.1 (Links.loneLeaf hX).toNode =
      cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 0) := by
    simp only [cosetDecoration, Links.tree_root_eq_lone hX κ.2.1]
  rw [phaseIntegral_shift' L γ δ LG hT r hr _ s _ (sum_sign_omega_tree hX _ hpair hlone)]

/-- The multiplied tree kernel depends on the layering only through the branching nodes. -/
theorem kernelLeavesW_tree_relayer (L γ δ : ℝ) (LG : LayeredGarden 1) (layer' : GNode LG.garden.tree → ℕ)
    (h' : IsLayering LG.garden layer') (hb : ∀ b : GBranch LG.garden.tree, layer' b.toNode = LG.layer b.toNode)
    (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ ⟨LG.garden, layer', h'⟩ H (fun _ => t) s k (fun _ => 0) 0 m =
      Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 m := by
  have hD : kDomain (⟨LG.garden, layer', h'⟩ : LayeredGarden 1) (fun _ => t) s =
      kDomain LG (fun _ => t) s := by
    ext τ
    simp only [kDomain, Set.mem_ofPred_eq, hb]
  unfold Flower.Stage1W.kernelLeavesW phaseIntegral
  rw [hD]

/-- For `s, s'` below every lone parent the multiplied tree kernel does not depend on `s`. -/
theorem kernelLeavesW_tree_indep_of_le (L γ δ : ℝ) (LG : LayeredGarden 1) (hP : IsPairedTree LG.garden)
    (H : LeafProfiles 1 d) (t s s' : ℝ) (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (hs : ∀ b, LG.garden.IsLoneParent b → s ≤ LG.layer b.toNode ∧ s' ≤ LG.layer b.toNode) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 m =
      Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s' k (fun _ => 0) 0 m := by
  have hfl := LGSpine.no_flowerParent_of_pairedTree LG.garden hP
  have hD : kDomain LG (fun _ => t) s = kDomain LG (fun _ => t) s' := by
    ext τ
    simp only [kDomain, Set.mem_ofPred_eq]
    constructor
    · intro h b
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := h b
      exact ⟨h1, h2, h3, h4, h5, fun hb => lt_of_le_of_lt (by exact_mod_cast (hs b hb).2) h1⟩
    · intro h b
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := h b
      exact ⟨h1, h2, h3, h4, h5, fun hb => lt_of_le_of_lt (by exact_mod_cast (hs b hb).1) h1⟩
  have hE : ∀ τ, LG.garden.extendTime s τ = LG.garden.extendTime s' τ := fun τ => by
    funext b
    simp only [Garden.extendTime, hfl b, ↓reduceDIte]
  simp only [Flower.Stage1W.kernelLeavesW, phaseIntegral, hD, hE]

/-- Time continuity of a multiplied tree kernel with a bounded multiplier. -/
theorem continuous_kernelLeavesW_tree_time (L γ δ : ℝ) (LG : LayeredGarden 1) (hP : IsPairedTree LG.garden)
    (H : LeafProfiles 1 d) (k : Mom d) (m : (GNode LG.garden.tree → Mom d) → ℂ) (Mb : ℝ)
    (hm : ∀ κ, ‖m κ‖ ≤ Mb)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ =>
      Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 m) := by
  have hc := Flower.Stage1WNoVine.continuous_kernelLeavesW_time L γ δ H LG k (fun _ => 0) 0 m Mb hm
    (LGSpine.no_flowerParent_of_pairedTree LG.garden hP)
    (card_lone_le_one (fun _ _ h h' => hP.eq_of_isLone h h')) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) := fun ts => ((fun _ => ts 0), ts 1)
  have hu : Continuous u := by fun_prop
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    Flower.Stage1W.kernelLeavesW L γ δ LG H x.1 x.2 k (fun _ => 0) 0 m) ∘ u)
  exact hc.comp hu

/-- Leafwise scaling of a multiplied tree-kernel bound. -/
theorem treeW_kernel_scaled (L γ δ θ : ℝ) (hd : 1 ≤ d) (LG : LayeredGarden 1)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (T : Set (Fin 2 → ℝ)) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hRA : ∀ H' : LeafProfiles 1 d, (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      mixedRestrictionNorm θ (30 * d) 0 T Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H' (fun _ => ts.1 0) (ts.1 1) k.1
          (fun _ => 0) 0 m) ≤ M)
    (H : LeafProfiles 1 d) (B : Fin 1 × Path → NNReal) (hH : LeafwiseControlled LG H B) :
    mixedRestrictionNorm θ (30 * d) 0 T Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts.1 0) (ts.1 1) k.1
          (fun _ => 0) 0 m) ≤
      ENNReal.ofReal (leafSizeProduct LG B) * M := by
  classical
  unfold leafSizeProduct
  refine le_of_forall_eps (inputLeaves LG.garden) (fun ℓ => (B ℓ.1 : ℝ)) _ M hM ?_
  intro ε hε
  let S : Finset (Fin 1 × Path) := (inputLeaves LG.garden).image (fun ℓ => ℓ.1)
  let β : Fin 1 × Path → ℝ := fun z => (B z : ℝ) + ε
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
        Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts.1 0) (ts.1 1) k.1 (fun _ => 0) 0 m) =
      fun ts k => (P : ℂ) • Flower.Stage1W.kernelLeavesW L γ δ LG H' (fun _ => ts.1 0) (ts.1 1) k.1
        (fun _ => 0) 0 m := by
    funext ts k
    rw [kernelLeavesW_scale' L γ δ LG H H' β hscale]
    simp only [smul_eq_mul, hP]
  rw [hD]
  have hc : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  refine (mixedRestrictionNorm_smul_le hc θ _ _ _ _ _).trans ?_
  rw [show ‖(P : ℂ)‖ₑ = ENNReal.ofReal P by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos]]
  exact mul_le_mul' le_rfl (hRA H' hnorm)

/-- Layer translation, relayering, freezing `s = r` and the trace for a multiplied tree-kernel bound. -/
theorem treeW_kernel_item_le (L γ δ : ℝ) (H : LeafProfiles 1 d)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hFs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k : Mom d,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|)
    {q' r : ℕ} (hq : q' ≤ r)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Mb : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ Mb)
    {θ : ℝ} (hθ : 0 ≤ θ) {Λ : ℕ} (hΛ : Λ ≠ 0) {M : ℝ≥0∞}
    (hM : mixedRestrictionNorm θ Λ 0 (timeBoxGt 0 0) Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ (layer0 LG) H (fun _ => ts.1 0) (ts.1 1) k.1
        (fun _ => 0) 0 m) ≤ M) :
    XNormRestr θ Λ 0 (timeBoxGt r q') Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 m) ≤
      traceConst (r := 2) θ chiUnit * M := by
  set h₀ : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k =>
    Flower.Stage1W.kernelLeavesW L γ δ (layer0 LG) H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 m with hh₀
  have hP := isPairedTree_of_decodesTree hX
  have hrel : ∀ t s k, Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 m =
      Flower.Stage1W.kernelLeavesW L γ δ (constLayer LG r) H (fun _ => t) s k (fun _ => 0) 0 m :=
    fun t s k => (kernelLeavesW_tree_relayer L γ δ (LG := LG) (fun _ => r) (constLayer LG r).isLayering
      (fun b => by
        rw [hlay b.toNode]
        split_ifs with hc
        · exact absurd hc (branch_ne_lonePath hX b)
        · rfl) H t s k m).symm
  have hshift : ∀ t s k, Flower.Stage1W.kernelLeavesW L γ δ (constLayer LG r) H (fun _ => t) s k
      (fun _ => 0) 0 m = h₀ ![t - r, s - r] k :=
    fun t s k => kernelLeavesW_tree_shift L γ δ (constLayer LG r) hX H r (fun _ => rfl) t s k m
  have hf : ∀ t s k, Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 m =
      h₀ ![t - r, s - r] k := by
    intro t s k
    rw [hrel, hshift]
  have hM' : XNormRestr θ Λ 0 (timeBoxGt 0 0) Set.univ h₀ ≤ M :=
    (XNormRestr_eq_mixedRestrictionNorm θ Λ 0 _ h₀).le.trans hM
  have hK1 : 1 ≤ traceConst (r := 2) θ chiUnit :=
    one_le_traceConst hθ chiUnit_contDiff (coordinateCutoff_chiUnit (t := fun _ => 0)
      ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩)
  rcases hq.lt_or_eq with hlt | heq
  · have hfreeze : ∀ ts ∈ timeBoxGt r q', ∀ k : Mom d,
        Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 m =
          h₀ (Function.update (ts - fun i => ![(r : ℝ), (q' : ℝ)] i) 1 0) k := by
      intro ts hts k
      have hs : ts 1 ≤ r := by
        have := hts.1.2.2
        have hq1 : ((q' : ℝ) + 1) ≤ r := by exact_mod_cast hlt
        linarith
      rw [hrel]
      have hind := kernelLeavesW_tree_indep_of_le L γ δ (constLayer LG r) hP H (ts 0) (ts 1) r k m
        (fun b _ => ⟨by simpa [constLayer] using hs, by simp [constLayer]⟩)
      rw [hind, ← hrel, hf]
      congr 1
      funext i
      fin_cases i <;> simp [Function.update]
    have hcont : ∀ k ∈ (Set.univ : Set (Mom d)), Continuous fun ts => h₀ ts k := by
      intro k _
      exact continuous_kernelLeavesW_tree_time L γ δ (layer0 LG) hP H k m Mb hm (fun ℓ hℓ => hFs ℓ hℓ k)
    calc XNormRestr θ Λ 0 (timeBoxGt r q') Set.univ _
        ≤ XNormRestr θ Λ 0 (timeBox 0 0) Set.univ (fun ts k => h₀ (Function.update ts 1 0) k) := by
          refine XNormRestr_shift_le θ Λ 0 (fun i => ![(r : ℝ), (q' : ℝ)] i) (fun ts hts => ?_)
            (fun ts hts k _ => hfreeze ts hts k)
          obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, -⟩ := hts
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
      _ ≤ mixedRestrictionNorm θ Λ 0 (timeBox 0 0) Set.univ
            (fun ts k => h₀ (Function.update ts.1 1 0) k.1) :=
          (XNormRestr_eq_mixedRestrictionNorm θ Λ 0 _ _).le
      _ ≤ traceConst (r := 2) θ chiUnit * mixedRestrictionNorm θ Λ 0 (timeBoxGt 0 0) Set.univ
            (fun ts k => h₀ ts.1 k.1) :=
          mixedRestrictionNorm_trace_le hΛ hθ chiUnit_contDiff chiUnit_hasCompactSupport h₀ hcont 1 0
            (fun t ht => update_mem_closure_interior ht) (fun t ht => coordinateCutoff_chiUnit ht)
      _ ≤ traceConst (r := 2) θ chiUnit * M := mul_le_mul' le_rfl hM
  · subst heq
    calc XNormRestr θ Λ 0 (timeBoxGt q' q') Set.univ _
        ≤ XNormRestr θ Λ 0 (timeBoxGt 0 0) Set.univ h₀ := by
          refine XNormRestr_shift_le θ Λ 0 (fun _ => (q' : ℝ)) (fun ts hts => ?_)
            (fun ts _ k _ => ?_)
          · obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩ := hts
            refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith
          · rw [hf]
            congr 1
            funext i
            fin_cases i <;> simp
      _ ≤ M := hM'
      _ ≤ traceConst (r := 2) θ chiUnit * M := le_mul_of_one_le_left zero_le hK1

/-- **Single-layer star-weighted paired trees in layer `r`** (lone leaf in a layer `q'' ≤ r), individual leaf
bounds, positive order: `‖K‖_{X^{θ,30d,0}} ≤ K_tr(θ) · Ck (Ck δ)^n ∏ cω ∏ B_ℓ`, every `0 ≤ θ ≤ 1 - η/8`. -/
theorem tree_star_layer_bound (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8) :
    ∃ Ck : ℝ, 1 ≤ Ck ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (r q'' : ℕ) (X : RegChain), q'' ≤ r → X.wf = true → X.size = 2*n →
      ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
      (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
      ∀ (H : LeafProfiles 1 d) (B : (Fin 1 × Path) → NNReal), LeafwiseControlled LG H B →
      ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
      XNormRestr θ (30*d) 0 (timeBoxGt r q'') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
          (IncTop.starWeight Sset ω)) ≤
        traceConst (r := 2) θ chiUnit * (ENNReal.ofReal (Ck*(Ck*δ)^n) * (∏ a ∈ Sset, ENNReal.ofReal (cω a)) *
          ENNReal.ofReal (leafSizeProduct LG B)) := by
  obtain ⟨Ck, hCk, hst⟩ := exists_tree_star_bound_theta hd hγ hη0 hη hηγ hθ0 hθ zero_le_one
  refine ⟨Ck, hCk, fun Aorder => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hst Aorder
  refine ⟨max L₀ 1, fun L hL δ hδ hδ1 n hn hnlog r q'' X hq hwf hsz LG hdec hlay H B hctl Sset ω cω hpres => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hL0 : L₀ ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hctl0 : LeafwiseControlled (layer0 LG) H B := hctl
  have hdec0 : X.DecodesTree (layer0 LG).garden := hdec
  have hfin : ENNReal.ofReal (Ck*(Ck*δ)^n) * (∏ a ∈ Sset, ENNReal.ofReal (cω a)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  have hsc := treeW_kernel_scaled L γ δ θ hd1 (layer0 LG) (IncTop.starWeight Sset ω) (timeBoxGt 0 0) _ hfin
    (fun H' hH' => by
      have hF : ∀ z, spatialNorm (40*d) (40*d) (addrFam H' z) ≤ ENNReal.ofReal 1 := fun z => by
        have := hH' z
        rwa [NormBridgeScratch.SNormR_eq_spatialNorm] at this
      exact hL₀ L hL0 δ hδ hδ1 n hn hnlog X hwf hsz (layer0 LG) hdec0 (fun _ => rfl) H' hF Sset ω cω hpres) H B hctl0
  have hFs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k : Mom d,
      Summable fun m : Fin d → ℤ => |H ℓ.1 (k + latticePoint L m)| := fun ℓ hℓ k =>
    summable_abs_coset_of_SNormR (by linarith) (by omega : d + 1 ≤ 40 * d)
      (B ℓ.1).2 (H ℓ.1) (hctl ℓ hℓ) k
  refine (treeW_kernel_item_le L γ δ H hdec hFs hq hlay (IncTop.starWeight Sset ω) _
    (norm_starWeight_le Sset ω cω hpres) hθ0 (Λ := 30 * d) (by omega) hsc).trans ?_
  have e0 : leafSizeProduct (layer0 LG) B = leafSizeProduct LG B := rfl
  rw [e0, mul_comm (ENNReal.ofReal (leafSizeProduct LG B))]

end WaveTurbulence.Flower.FiltCoh
