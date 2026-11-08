/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.PairPack
public import WaveTurbulence.Foundations.Flower.ProtPin.RootP1
public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarFinal

/-! # D3 PROT-PIN: (P1) for one-pair protected trees, every port layer, in `X^{θ,30d,0}`

On the R176 box (`t ≤ ts 0`) the (P1) kernel of `X = pair m Qr Qg inner nil` is
`σ ↦ Σ'_e c_e ∫_{rootU0 T t σ} e^{πiA_e(t-u)} W_e(t, u) du` in the port clock `σ = ts 1` (`pair_pack`):
* `q' = p`: `rootU0 = Ioo σ t` and `mirror_kink` applies;
* `q' < p`: `σ ≤ p < u`, so `rootU0 = Ioo p t` and the kernel is a constant, bounded pointwise (`enorm_rootInt_le`).
`final_pair` turns a per-output bound `Cr · pairRb` into the frozen norm (`LocalOutputExtension` and the algebra of
`term`); `root_final_pair` is (P1) for one-pair trees in `X^{θ,30d,0}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem norm_rootPh (A t u : ℝ) : ‖rootPh A t u‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- **Pointwise bound of a root integral** by the restricted norms of the integrands. -/
theorem enorm_rootInt_le {θ : ℝ} (hθ0 : 0 ≤ θ) {ι : Type*} {p t a : ℝ} (hpa : p ≤ a) (htp : t ≤ p + 1)
    (A : ι → ℝ) (c : ι → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ) (hWc : ∀ i, Continuous (W i)) :
    ‖∑' i, c i * ∫ u in Ioo a t, rootPh (A i) t u * W i ![t, u]‖ₑ ≤
      ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun i => ?_)
  rw [enorm_mul]
  refine mul_le_mul' le_rfl ?_
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt : ∀ u ∈ Ioo a t, ‖rootPh (A i) t u * W i ![t, u]‖ₑ ≤ rn θ (timeBoxGt p p) (W i) := by
    intro u hu
    rw [enorm_mul, ← ofReal_norm, norm_rootPh, ENNReal.ofReal_one, one_mul]
    have hmem : (![t, u] : Fin 2 → ℝ) ∈ timeBoxGt p p := by
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith [hu.1, hu.2]
    exact enorm_le_rn hθ0 (timeBoxGt_cl p) (hWc i) hmem
  calc ∫⁻ u in Ioo a t, ‖rootPh (A i) t u * W i ![t, u]‖ₑ
      ≤ ∫⁻ _ in Ioo a t, rn θ (timeBoxGt p p) (W i) := setLIntegral_mono' measurableSet_Ioo hpt
    _ = rn θ (timeBoxGt p p) (W i) * volume (Ioo a t) := setLIntegral_const _ _
    _ ≤ rn θ (timeBoxGt p p) (W i) * 1 := by
        refine mul_le_mul' le_rfl ?_
        rw [Real.volume_Ioo, ENNReal.ofReal_le_one]
        linarith
    _ = _ := mul_one _

/-- The time domain of (P1) on the R176 box when the port clock is below the layer. -/
theorem rootU0_eq_low {LG : LayeredGarden 1} {m : MiniTreeCode} {inner : RegChain} {p : ℕ}
    (hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p) {t T σ : ℝ} (htp : t < p + 1)
    (hT : t ≤ T) (hσ : σ ≤ p) : rootU0 LG m inner T t σ = Ioo (p : ℝ) t := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  simp only [rootU0, hlay, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, -, -, -, h5, -⟩
    exact ⟨h1, h5⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith, by linarith, by linarith, h2, by linarith⟩

/-- **(P1), one pair, every port layer, one output.** -/
theorem root_perk_pair {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      {inner : RegChain} (_C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (cpair m Qr Qg inner) LG) (_hsz : (cpair m Qr Qg inner).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg inner) LG) {t : ℝ} (_hpt : (p : ℝ) < t) (_htp : t < p + 1) (s : ℝ)
      (q' : ℕ) (_hq' : q' ≤ p)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator (cpair m Qr Qg inner) ind)
      (k : Mom P.d),
      rn θ (ProtCfg.root.box (cpair m Qr Qg inner) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG) (leafSizeProduct LG B)
          (starCost S cω)) := by
  obtain ⟨Cm, hCm, hmk⟩ := mirror_kink hθ0 (by linarith)
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨(Cm + cutNormR θ 2) * T4, ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨hCm, cutNormR_lt_top θ 2⟩) hT4f, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGp LGi LGr LGg m Qr Qg inner C hsh hsz hamb t hpt htp s q' hq'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  obtain ⟨c, A, W, hWc, hWfin, hsum, hroot, -⟩ := pair_pack hθ0 K hθc hp hn C hsh hsz hamb H B hH S ω cω hpres
    F M hM Fu Mu hMu ind hind k
  have D : PairOnly LG m Qr Qg inner LGi LGr LGg := PairOnly.of_cutTerm C
  have hlay := pair_b_layer D hsh.2.2.2
  set R : ℝ≥0∞ := ENNReal.ofReal (pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG) (leafSizeProduct LG B)
    (starCost S cω)) with hR
  have hcfg : ∀ ts ∈ ProtCfg.root.box (cpair m Qr Qg inner) t p q',
      kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in rootU0 LG m inner (ts 0) t (ts 1), rootPh (A e) t u * W e ![t, u] := by
    intro ts hts
    rw [box_root] at hts
    rw [cfg_root_fix]
    exact hroot (ts 0) t (ts 1) hts.2
  rw [rn_congr θ hcfg]
  rcases Nat.lt_or_ge q' p with hlt | hge
  · -- `q' < p`: a constant
    have hq1 : (q' : ℝ) + 1 ≤ p := by exact_mod_cast hlt
    have hconst : ∀ ts ∈ ProtCfg.root.box (cpair m Qr Qg inner) t p q',
        ∑' e, c e * ∫ u in rootU0 LG m inner (ts 0) t (ts 1), rootPh (A e) t u * W e ![t, u] =
          ∑' e, c e * ∫ u in Ioo (p : ℝ) t, rootPh (A e) t u * W e ![t, u] := by
      intro ts hts
      rw [box_root] at hts
      rw [rootU0_eq_low hlay htp hts.2 (by linarith [hts.1.1.2.2])]
    rw [rn_congr θ hconst, box_root]
    refine (rn_const_le θ ![(p : ℝ), (q' : ℝ)] (rootBox_sub_cell (p : ℝ) q' t) _).trans ?_
    refine (mul_le_mul' (enorm_rootInt_le hθ0 le_rfl htp.le A c W hWc) le_rfl).trans ?_
    calc (∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e)) * cutNormR θ 2 ≤ T4 * R * cutNormR θ 2 :=
          mul_le_mul' hsum le_rfl
      _ ≤ (Cm + cutNormR θ 2) * T4 * R := by
          rw [show T4 * R * cutNormR θ 2 = cutNormR θ 2 * T4 * R by ring]
          exact mul_le_mul' (mul_le_mul' le_add_self le_rfl) le_rfl
  · -- `q' = p`: the mirrored kink
    have hqp : q' = p := le_antisymm hq' hge
    subst hqp
    have hdom : ∀ ts ∈ ProtCfg.root.box (cpair m Qr Qg inner) t q' q',
        ∑' e, c e * ∫ u in rootU0 LG m inner (ts 0) t (ts 1), rootPh (A e) t u * W e ![t, u] =
          ∑' e, c e * ∫ u in Ioo (ts 1) t, rootPh (A e) t u * W e ![t, u] := by
      intro ts hts
      rw [box_root] at hts
      rw [rootU0_eq hlay hpt htp hts.2 hts.1.1.2.1]
    rw [rn_congr θ hdom]
    have hsub : ProtCfg.root.box (cpair m Qr Qg inner) t q' q' ⊆ timeBox (q' : ℝ) q' := by
      rw [box_root]
      exact fun x hx => hx.1.1
    refine (hmk (PairE m P.d) q' t hpt htp A c W hWc hWfin hsub).trans ?_
    calc Cm * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (q' : ℝ) q') (W e) ≤ Cm * (T4 * R) := mul_le_mul' le_rfl hsum
      _ ≤ (Cm + cutNormR θ 2) * T4 * R := by
          rw [mul_assoc (Cm + cutNormR θ 2) T4 R]
          exact mul_le_mul' le_self_add le_rfl

/-- **From a per-output `pairRb` bound to the frozen norm** (`LocalOutputExtension` and `term`'s algebra). -/
theorem final_pair {θ : ℝ} {P : WTParams} {Cr CL c c' : ℝ} (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ) (hC11 : 1 ≤ P.C₁)
    (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL) (hc'0 : 0 ≤ c') (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c)
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {r : ℕ} (Bx : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (Fk : (Fin r → ℝ) → Mom P.d → ℂ) {n g : ℕ} (hn1 : 1 ≤ n)
    {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS)
    (hperk : ∀ k, rn θ Bx (fun ts => Fk ts k) ≤ ENNReal.ofReal (Cr * pairRb P c' n g leaf CS)) :
    XNormRestr θ (30 * P.d) 0 Bx (latticeBall P.L b₀ c₀) Fk ≤
      ENNReal.ofReal CS * ENNReal.ofReal (P.L ^ c) * regBound P n g * ENNReal.ofReal leaf := by
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  have hr := rb_nonneg hC1 hδ hL0 (n - 1) g
  refine (hLOE P.L hL Bx b₀ c₀ Fk _ fun k _ => (XNorm00Restr_single_le_rn θ _ _ k).trans (hperk k)).trans ?_
  have hLc : 0 ≤ P.L ^ c := Real.rpow_nonneg hL0 _
  have hCδr : 0 ≤ P.C₁ * P.δ * rb P (n - 1) g := mul_nonneg (mul_nonneg hC1 hδ) hr
  rw [← ENNReal.ofReal_mul (mul_nonneg hCL (pow_nonneg hL0 _)), regBound_eq_rb, rb_succ P hn1,
    ← ENNReal.ofReal_mul hCS, ← ENNReal.ofReal_mul (mul_nonneg hCS hLc),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCS hLc) hCδr)]
  refine ENNReal.ofReal_le_ofReal ?_
  have halg := term_star_alg (P := P) (Cr := Cr) (CL := CL) (K := termK CL Cr P.d) (β := 1) (CS := CS)
    (leaf := leaf) (r := rb P (n - 1) g) (c := c) (c' := c') hL hδ hC1 hCr hCL zero_le_one hCS hleaf hr rfl hbig hc
  have hA : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 := by positivity
  have hL34 : P.L ^ (3 * c') ≤ P.L ^ (4 * c') := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hC23 : P.C₁ ^ 2 ≤ P.C₁ ^ 3 := pow_le_pow_right₀ hC11 (by norm_num)
  have hmono : pairRb P c' n g leaf CS ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
      P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g) * leaf * CS := by
    unfold pairRb
    have h1 : P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) g) ≤ P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g) :=
      mul_le_mul hL34 (mul_le_mul_of_nonneg_right hC23 hr) (mul_nonneg (by positivity) hr)
        (Real.rpow_nonneg hL0 _)
    calc coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) g) *
          leaf * CS
        = (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * (leaf * CS)) *
            (P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) g)) := by ring
      _ ≤ (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * (leaf * CS)) *
            (P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hA (mul_nonneg hleaf hCS))
      _ = _ := by ring
  calc CL * P.L ^ (31 * P.d) * (Cr * pairRb P c' n g leaf CS)
      ≤ CL * P.L ^ (31 * P.d) * (1 * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g) * leaf * CS))) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hCr)
          (mul_nonneg hCL (pow_nonneg hL0 _))
    _ ≤ CS * P.L ^ c * (P.C₁ * P.δ * rb P (n - 1) g) * (1 * leaf) := halg
    _ = _ := by ring

/-- `C · ofReal x = ofReal (C.toReal · x)` for a finite `C`. -/
theorem mul_ofReal_toReal {C : ℝ≥0∞} (hC : C < ⊤) {x : ℝ} (hx : 0 ≤ x) :
    C * ENNReal.ofReal x = ENNReal.ofReal (C.toReal * x) := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]

/-- **(P1) for one-pair protected trees in `X^{θ,30d,0}`** (R176 box, stars, filters, dagger). -/
theorem root_final_pair {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c CL : ℝ}
      (_hθc : PieceLoss P θ c') (_hc'0 : 0 ≤ c') (_hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) (_hCL : 0 ≤ CL)
      (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      {inner : RegChain} (_C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (cpair m Qr Qg inner) LG) (_hsz : (cpair m Qr Qg inner).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg inner) LG) {t : ℝ} (_hpt : (p : ℝ) < t) (_htp : t < p + 1) (s : ℝ)
      (q' : ℕ) (_hq' : q' ≤ p)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator (cpair m Qr Qg inner) ind)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.root.box (cpair m Qr Qg inner) t p q') (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (protIncoh (cpair m Qr Qg inner) LG) * ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C, hC, hperk⟩ := root_perk_pair hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' c CL hθc hc'0 hc hCL hC11 hLOE hbig p hp n hn LG LGp LGi LGr LGg m Qr Qg inner C' hsh
    hsz hamb t hpt htp s q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hn1 : 1 ≤ n := by
    obtain ⟨_, _, _, _, -, -, -, -, h⟩ := cut_sizes (Xp := .nil) hsz
    omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  rw [prod_ofReal_starCost]
  refine final_pair K.hL K.hδ hC11 ENNReal.toReal_nonneg hCL hc'0 hc hLOE hbig _ b₀ c₀ _ hn1 hleaf
    (starCost_nonneg' S cω) fun k => ?_
  rw [← mul_ofReal_toReal hC (pairRb_nonneg (by linarith) K.hδ hL0 _ _ hleaf (starCost_nonneg' S cω))]
  exact hperk K hθc hp hn C' hsh hsz hamb hpt htp s q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k

end WaveTurbulence.Flower.ProtPin
