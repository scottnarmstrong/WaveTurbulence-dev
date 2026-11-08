/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.PenSub
public import WaveTurbulence.Foundations.Flower.ProtPin.RootPin
public import WaveTurbulence.Foundations.Flower.ProtPin.MirrorAt
public import WaveTurbulence.Foundations.Flower.ProtPin.TraceP8

/-! # D3 PROT-PIN ((P4) with a prefix): a protected tree at a fixed port time, in its upper clock

For a protected paired tree `Y ≠ nil` (all branches free, gate-form multiplier, lone port time `s ∈ (p, p+1)`),
`T ↦ K(T, s)` on the window `[p, p+1]` vanishes for `T ≤ s` and has a kink at `T = s`. Pinning the root
(`kernelProt_root_pin`) writes `K(T, s) = ∫_{Ioo p T} R(u, s) du` with `R` the root trace; the trace identities of
`pair_pack` (one pair) / `root_pack` (with a suffix) give `R(u, s) = Σ'_e c_e ∫_{Ioo s u} e^{πiA_e(u-v)} Ks(v, s) W_e(u, v) dv`
(zero for `u ≤ s`), so `K(T, s) = ∫_{Ioo s T} R`, which is `mirror_int`'s form: `pen_prefix_win`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-! ### Generalities -/

/-- **The kernel vanishes when a free parent of a node pinned at `v` has upper clock `≤ v`.** -/
theorem pen_kernelProt_eq_zero_of_pin {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (a pa : GBranch LG.garden.tree) (hc : a.IsChildOf pa) {v : ℝ} (ha : fix a = some v) (hpa : fix pa = none)
    (hup : up pa ≤ v) : kernelProt L γ δ LG H m up s fix k₀ nroot nfl = 0 := by
  have hz : ∀ (g : (GBranch LG.garden.tree → ℝ) → ℂ) (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ),
      (kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s < τ b}).indicator g
        (LG.garden.extendFix fix τ) = 0 := by
    intro g τ
    refine Set.indicator_of_notMem (fun hmem => ?_) _
    have h1 := (hmem.1 pa).2 a hc (Or.inr hpa)
    have h2 := ((hmem.1 pa).1 hpa).2.2.2
    rw [extendFix_some LG.garden fix τ ha] at h1
    linarith
  unfold kernelProt
  simp only [hz, integral_zero, mul_zero, zero_mul, tsum_zero]

/-- A constant factor costs its modulus. -/
theorem pen_rn_mul_const_le {r : ℕ} (θ : ℝ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → ℂ) (V : ℂ) :
    rn θ B (fun x => f x * V) ≤ ‖V‖ₑ * rn θ B f := by
  have key : ∀ g : (Fin r → ℝ) → ℂ, (∀ x ∈ B, g x = f x) →
      rn θ B (fun x => f x * V) ≤ ‖V‖ₑ * timeFourierNorm θ g := by
    intro g hg
    refine (rn_le θ (g := fun x => V • g x) fun x hx => by rw [smul_eq_mul, hg x hx, mul_comm]).trans ?_
    rw [timeFourierNorm_smul]
  by_cases h0 : ‖V‖ₑ = 0
  · refine (key f fun _ _ => rfl).trans ?_
    rw [h0, zero_mul]
    exact zero_le
  conv_rhs => rw [rn_eq_iInf]
  rw [ENNReal.mul_iInf_of_ne h0 enorm_ne_top]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne h0 enorm_ne_top]
  exact le_iInf fun hg => key g hg

/-- The lone path of a nonempty chain has length at least two. -/
theorem pen_lonePath_two {Y : RegChain} (hY : Y ≠ .nil) : 2 ≤ Y.lonePath.length := by
  cases Y with
  | nil => exact absurd rfl hY
  | pair m r g i s => simp [RegChain.lonePath]; omega

/-- The one-pair budget is below the four-piece budget. -/
theorem pen_pairRb_le {P : WTParams} {c' : ℝ} (hc' : 0 ≤ c') (hL : 1 ≤ P.L) (hC11 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    (n g : ℕ) {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS) :
    pairRb P c' n g leaf CS ≤ termRb P c' n g leaf CS := by
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hr := rb_nonneg (by linarith : (0 : ℝ) ≤ P.C₁) hδ hL0 (n - 1) g
  have hA : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 := by
    have := latC_nonneg P.d
    positivity
  have hL34 : P.L ^ (3 * c') ≤ P.L ^ (4 * c') := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hC23 : P.C₁ ^ 2 ≤ P.C₁ ^ 3 := pow_le_pow_right₀ hC11 (by norm_num)
  have h1 : P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) g) ≤ P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g) :=
    mul_le_mul hL34 (mul_le_mul_of_nonneg_right hC23 hr) (mul_nonneg (by positivity) hr) (Real.rpow_nonneg hL0 _)
  unfold pairRb termRb
  calc coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) g) *
        leaf * CS
      = (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * (leaf * CS)) *
          (P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) g)) := by ring
    _ ≤ (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * (leaf * CS)) *
          (P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hA (mul_nonneg hleaf hCS))
    _ = _ := by ring

/-- The gate-form multiplier is D3's multiplier with the trivial dagger. -/
theorem pen_gateM_eq {d : ℕ} {LGt : LayeredGarden 1} (S : Finset (GNode LGt.garden.tree))
    (ω : GNode LGt.garden.tree → Flower.IncTop.Star d → ℂ) (F : Finset (GBranch LGt.garden.tree))
    (M : GBranch LGt.garden.tree → ℝ) (Fu : Finset (GBranch LGt.garden.tree)) (Mu : GBranch LGt.garden.tree → ℝ) :
    gateM S ω F M Fu Mu = (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
      filtWeight Fu (fun _ => false) Mu κ * (((fun _ : GNode LGt.garden.tree → Mom d => (1 : ℝ)) κ : ℝ) : ℂ)) := by
  funext κ
  simp [gateM]

/-- The root of a nonempty protected tree: in layer `p`, not a lone parent. -/
theorem pen_root_facts {p : ℕ} {Y : RegChain} {LGt : LayeredGarden 1} (hY : Y ≠ .nil) (hsh : ProtShape p Y LGt) :
    ∃ rb : GBranch LGt.garden.tree, rb.1.2 = [] ∧ LGt.layer rb.toNode = p ∧ ¬ LGt.garden.IsLoneParent rb := by
  have hmem : ([] : TTree.Path) ∈ (LGt.garden.tree ((0 : Fin 1), ([] : TTree.Path)).1).branching := by
    show ([] : TTree.Path) ∈ (LGt.garden.tree 0).branching
    rw [hsh.2.1.1]
    exact nil_mem_branching_plug Y hY _ _
  refine ⟨⟨((0 : Fin 1), []), hmem⟩, rfl, ?_, ?_⟩
  · have h2 := pen_lonePath_two hY
    refine hsh.2.2.2 _ rfl List.nil_prefix ?_
    intro h
    rw [← h] at h2
    simp at h2
  · rintro ⟨ℓ, hℓ, -, i, hi⟩
    have hl : ℓ.1.2 = Y.lonePath := (Reg.decodesTree_lone_iff hsh.2.1 ℓ).1 hℓ
    have h2 := pen_lonePath_two hY
    rw [← hl, hi] at h2
    simp at h2

/-! ### The window bound -/

/-- `Σ'_e c_e ∫_{Ioo s u} …` vanishes for `u ≤ s`. -/
theorem pen_G_zero {ι : Type*} (A : ι → ℝ) (c : ι → ℂ) (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ)
    {s u : ℝ} (hu : u ≤ s) :
    ∑' i, c i * ∫ v in Ioo s u, rootPh (A i) u v * (Ks ![v, s] * W i ![u, v]) = 0 := by
  rw [Set.Ioo_eq_empty (by linarith : ¬ s < u)]
  simp

/-- **One window, one pair.** -/
theorem pen_prefix_win_pair {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') (_hC11 : 1 ≤ P.C₁) {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LGt : LayeredGarden 1} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
      (_hsh : ProtShape p (cpair m Qr Qg inner) LGt) (_hsz : (cpair m Qr Qg inner).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg inner) LGt)
      (Ht : LeafProfiles 1 P.d) (Bt : (Fin 1 × TTree.Path) → NNReal) (_hHt : LeafwiseControlled LGt Ht Bt)
      (S : Finset (GNode LGt.garden.tree)) (ω : GNode LGt.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (c : GNode LGt.garden.tree → ℝ) (F : Finset (GBranch LGt.garden.tree)) (M : GBranch LGt.garden.tree → ℝ)
      (Fu : Finset (GBranch LGt.garden.tree)) (Mu : GBranch LGt.garden.tree → ℝ)
      (_hG : GateData P.L S ω c F M Fu Mu) {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1) (k : Mom P.d),
      rn θ (win p) (fun T => kernelProt P.L P.γ P.δ LGt Ht (gateM S ω F M Fu Mu) (fun _ => T 0) s (fun _ => none)
          k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (termRb P c' n (protIncoh (cpair m Qr Qg inner) LGt) (leafSizeProduct LGt Bt)
          (starCost S c)) := by
  obtain ⟨Cm, hCm, hmi⟩ := mirror_int hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨Cm * cutNormR θ 2 * T4, ENNReal.mul_lt_top (ENNReal.mul_lt_top hCm (cutNormR_lt_top θ 2)) hT4f, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc hC11 p hp n hn LGt m Qr Qg inner hsh hsz hamb Ht Bt hHt S ω c F M Fu Mu hG
    s hps hsp k
  have hY : cpair m Qr Qg inner ≠ .nil := by simp [cpair]
  obtain ⟨LGp', LGi', LGr', LGg', C⟩ := CutTermData.exists_of_wf LGt .nil m Qr Qg inner hsh.2.1 hsh.1
  have hind : TermChildIndicator (cpair m Qr Qg inner) (fun _ : GNode LGt.garden.tree → Mom P.d => (1 : ℝ)) :=
    ⟨fun _ => ⟨zero_le_one, le_rfl⟩, fun _ _ _ => rfl⟩
  obtain ⟨cc, A, W, hWc, hWfin, hsum, hroot, -⟩ := pair_pack hθ0 K hθc hp hn C hsh hsz hamb Ht Bt hHt S ω c hG.1
    F M hG.2.1 Fu Mu hG.2.2 _ hind k
  have D : PairOnly LGt m Qr Qg inner LGi' LGr' LGg' := PairOnly.of_cutTerm C
  have hlay := pair_b_layer D hsh.2.2.2
  obtain ⟨rb, hrb, hrbl, hnl⟩ := pen_root_facts hY hsh
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  set G : ℝ → ℂ := fun ρ => ∑' e, cc e * ∫ v in Ioo s ρ,
    rootPh (A e) ρ v * ((fun _ => (1 : ℂ)) ![v, s] * W e ![ρ, v]) with hGdef
  have hBi : ∀ κ, ‖gateM S ω F M Fu Mu κ‖ ≤
      (∏ a ∈ S, max (c a) 0) * FiltCoh.chiDSup ^ F.card * FiltCoh.chiDSup ^ Fu.card :=
    FiltCoh.norm_d5Mult_le S ω c hG.1 F (fun _ => false) M Fu Mu
  have hwin : ∀ T ∈ win (p : ℝ), kernelProt P.L P.γ P.δ LGt Ht (gateM S ω F M Fu Mu) (fun _ => T 0) s
      (fun _ => none) k (fun _ => 0) 0 = ∫ ρ in Ioo s (T 0), G ρ := by
    intro T hT
    rw [kernelProt_root_pin P.L P.γ P.δ Ht _ _ hBi s k (card_lone_le_of_decodesTree hsh.2.1)
      (summable_coset_piece hHt hL1 k) hrb hrbl hnl hT.2]
    have hR : ∀ ρ ∈ Ioo (p : ℝ) (T 0), kernelProt P.L P.γ P.δ LGt Ht (gateM S ω F M Fu Mu) (fun _ => ρ) s
        (rootFix ρ) k (fun _ => 0) 0 = G ρ := by
      intro ρ hρ
      rw [pen_gateM_eq, hroot ρ ρ s le_rfl, rootU0_eq_tr hlay (hρ.2.le.trans hT.2) hps.le]
      simp only [hGdef, one_mul]
    rw [setIntegral_congr_fun measurableSet_Ioo hR]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (Ioo_subset_Ioo_left hps.le) fun ρ hρ => ?_
    have hρs : ρ ≤ s := by
      by_contra h
      exact hρ.2 ⟨lt_of_not_ge h, hρ.1.2⟩
    exact pen_G_zero A cc (fun _ => 1) W hρs
  rw [rn_congr θ hwin]
  refine (hmi (PairE m P.d) p s hps.le hsp A cc (fun _ => 1) W continuous_const hWc (rn_one_lt_top θ p)
    hWfin).trans ?_
  have hleaf : 0 ≤ leafSizeProduct LGt Bt := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hpt := pen_pairRb_le (hθc.nonneg) hL1 hC11 K.hδ n (protIncoh (cpair m Qr Qg inner) LGt) hleaf
    (starCost_nonneg' S c)
  calc Cm * rn θ (timeBoxGt (p : ℝ) p) (fun _ => (1 : ℂ)) * ∑' e, ‖cc e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e)
      ≤ Cm * cutNormR θ 2 * (T4 * ENNReal.ofReal (termRb P c' n (protIncoh (cpair m Qr Qg inner) LGt)
          (leafSizeProduct LGt Bt) (starCost S c))) :=
        mul_le_mul' (mul_le_mul' le_rfl (rn_one_le θ p)) (hsum.trans (mul_le_mul' le_rfl
          (ENNReal.ofReal_le_ofReal hpt)))
    _ = _ := by ring

/-- **One window, with a suffix.** -/
theorem pen_prefix_win_rest {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LGt : LayeredGarden 1} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} (_hrest : rest ≠ .nil)
      (_hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LGt)
      (_hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
      (_hamb : TreeAmb p (RegChain.pair m Qr Qg inner rest) LGt)
      (Ht : LeafProfiles 1 P.d) (Bt : (Fin 1 × TTree.Path) → NNReal) (_hHt : LeafwiseControlled LGt Ht Bt)
      (S : Finset (GNode LGt.garden.tree)) (ω : GNode LGt.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (c : GNode LGt.garden.tree → ℝ) (F : Finset (GBranch LGt.garden.tree)) (M : GBranch LGt.garden.tree → ℝ)
      (Fu : Finset (GBranch LGt.garden.tree)) (Mu : GBranch LGt.garden.tree → ℝ)
      (_hG : GateData P.L S ω c F M Fu Mu) {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1) (k : Mom P.d),
      rn θ (win p) (fun T => kernelProt P.L P.γ P.δ LGt Ht (gateM S ω F M Fu Mu) (fun _ => T 0) s (fun _ => none)
          k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (termRb P c' n (protIncoh (RegChain.pair m Qr Qg inner rest) LGt)
          (leafSizeProduct LGt Bt) (starCost S c)) := by
  obtain ⟨Cm, hCm, hmi⟩ := mirror_int hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨Cm * T4, ENNReal.mul_lt_top hCm hT4f, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LGt m Qr Qg inner rest hrest hsh hsz hamb Ht Bt hHt S ω c F M Fu Mu
    hG s hps hsp k
  have hY : RegChain.pair m Qr Qg inner rest ≠ .nil := by simp
  obtain ⟨LGZ, LGi', LGs, LGr', LGg', D⟩ := RootData.exists_of_wf LGt m Qr Qg inner rest hsh.2.1 hsh.1 hrest
  obtain ⟨cc, A, W, Ks, hWc, hWfin, hKc, hKfin, hvan, -, hsum, hroot⟩ :=
    root_pack hθ0 K hθc hp hn D hsh hsz hamb Ht Bt hHt S ω c hG.1 F M hG.2.1 Fu Mu hG.2.2
      (fun _ : GNode LGt.garden.tree → Mom P.d => (1 : ℝ)) (fun _ => rfl) k
  have hlay : layerAt LGt ((0 : Fin 1), bPath m inner) = p := by
    rw [← D.layer_bR]
    have hbp : D.bR.1.2 = bPath m inner := congrArg Prod.snd D.bR_path
    refine hsh.2.2.2 D.bR (Nat.lt_one_iff.mp D.bR.1.1.isLt) ?_ ?_
    · rw [hbp, root_lonePath]; exact List.prefix_append _ _
    · rw [hbp, root_lonePath]; simp
  obtain ⟨rb, hrb, hrbl, hnl⟩ := pen_root_facts hY hsh
  have hL1 := K.hL
  set G : ℝ → ℂ := fun ρ => ∑' e, cc e * ∫ v in Ioo s ρ, rootPh (A e) ρ v * (Ks ![v, s] * W e ![ρ, v]) with hGdef
  have hBi : ∀ κ, ‖gateM S ω F M Fu Mu κ‖ ≤
      (∏ a ∈ S, max (c a) 0) * FiltCoh.chiDSup ^ F.card * FiltCoh.chiDSup ^ Fu.card :=
    FiltCoh.norm_d5Mult_le S ω c hG.1 F (fun _ => false) M Fu Mu
  have hwin : ∀ T ∈ win (p : ℝ), kernelProt P.L P.γ P.δ LGt Ht (gateM S ω F M Fu Mu) (fun _ => T 0) s
      (fun _ => none) k (fun _ => 0) 0 = ∫ ρ in Ioo s (T 0), G ρ := by
    intro T hT
    rw [kernelProt_root_pin P.L P.γ P.δ Ht _ _ hBi s k (card_lone_le_of_decodesTree hsh.2.1)
      (summable_coset_piece hHt hL1 k) hrb hrbl hnl hT.2]
    have hR : ∀ ρ ∈ Ioo (p : ℝ) (T 0), kernelProt P.L P.γ P.δ LGt Ht (gateM S ω F M Fu Mu) (fun _ => ρ) s
        (rootFix ρ) k (fun _ => 0) 0 = G ρ := by
      intro ρ hρ
      rw [pen_gateM_eq, hroot ρ ρ s le_rfl, rootU_eq_tr hlay (hρ.2.le.trans hT.2)]
      simp only [hGdef]
      refine tsum_congr fun e => ?_
      congr 1
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
        (Ioo_subset_Ioo_left hps.le) fun v hv => ?_
      have hvs : v ≤ s := by
        by_contra h
        exact hv.2 ⟨lt_of_not_ge h, hv.1.2⟩
      rw [hvan ![v, s] (by simpa using hvs)]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioo hR]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (Ioo_subset_Ioo_left hps.le) fun ρ hρ => ?_
    have hρs : ρ ≤ s := by
      by_contra h
      exact hρ.2 ⟨lt_of_not_ge h, hρ.1.2⟩
    exact pen_G_zero A cc Ks W hρs
  rw [rn_congr θ hwin]
  refine (hmi (PairE m P.d) p s hps.le hsp A cc Ks W hKc hWc hKfin hWfin).trans ?_
  rw [mul_assoc]
  exact (mul_le_mul' le_rfl hsum).trans (le_of_eq (by ring))

/-- **The window bound of a protected tree at a fixed port time** (gate-form multiplier). -/
theorem pen_prefix_win {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') (_hC11 : 1 ≤ P.C₁) {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LGt : LayeredGarden 1} {Y : RegChain} (_hY : Y ≠ .nil) (_hsh : ProtShape p Y LGt) (_hsz : Y.size = 2 * n)
      (_hamb : TreeAmb p Y LGt)
      (Ht : LeafProfiles 1 P.d) (Bt : (Fin 1 × TTree.Path) → NNReal) (_hHt : LeafwiseControlled LGt Ht Bt)
      (S : Finset (GNode LGt.garden.tree)) (ω : GNode LGt.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (c : GNode LGt.garden.tree → ℝ) (F : Finset (GBranch LGt.garden.tree)) (M : GBranch LGt.garden.tree → ℝ)
      (Fu : Finset (GBranch LGt.garden.tree)) (Mu : GBranch LGt.garden.tree → ℝ)
      (_hG : GateData P.L S ω c F M Fu Mu) {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1) (k : Mom P.d),
      rn θ (win p) (fun T => kernelProt P.L P.γ P.δ LGt Ht (gateM S ω F M Fu Mu) (fun _ => T 0) s (fun _ => none)
          k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (termRb P c' n (protIncoh Y LGt) (leafSizeProduct LGt Bt) (starCost S c)) := by
  obtain ⟨C₁', hC₁', h1⟩ := pen_prefix_win_pair hθ0 hθ1
  obtain ⟨C₂', hC₂', h2⟩ := pen_prefix_win_rest hθ0 hθ1
  refine ⟨C₁' + C₂', ENNReal.add_lt_top.2 ⟨hC₁', hC₂'⟩, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc hC11 p hp n hn LGt Y hY hsh hsz hamb Ht Bt hHt S ω c F M Fu Mu hG s hps hsp k
  cases Y with
  | nil => exact absurd rfl hY
  | pair m Qr Qg inner rest =>
    by_cases hrest : rest = .nil
    · subst hrest
      exact (h1 K hθc hC11 hp hn hsh hsz hamb Ht Bt hHt S ω c F M Fu Mu hG hps hsp k).trans
        (mul_le_mul' le_self_add le_rfl)
    · exact (h2 K hθc hp hn hrest hsh hsz hamb Ht Bt hHt S ω c F M Fu Mu hG hps hsp k).trans
        (mul_le_mul' le_add_self le_rfl)

end WaveTurbulence.Flower.ProtPin
