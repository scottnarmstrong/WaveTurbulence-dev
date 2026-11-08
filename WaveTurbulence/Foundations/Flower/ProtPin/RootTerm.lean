/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootTermCore
public import WaveTurbulence.Foundations.Flower.ProtPin.TermFinal
public import WaveTurbulence.Foundations.Flower.ProtPin.Statement

/-! # D3 PROT-PIN: (P2) — a one-pair protected tree with its root and its terminal node pinned (R176 box)

On the R176 box `{ts ∈ timeBoxGt p q' | t ≤ ts 0}` the kernel of `ProtCfg.rootTerm` on `X = pair m Qr Qg inner nil`
does not depend on `ts` (`rootTerm_kernel_eq`, D2c's `kernelProt_rootTerm_cfg` read at two upper clocks `≥ t`). A
constant has restricted norm at most its modulus times the norm of the unit cutoff (`rn_const_le`: `cutQ = 1` on
the cell), and the modulus is `rootTerm_value_le`. `rootTerm_final`: the `X^{θ,30d,0}` bound of `ProtBoundAt` for
(P2), through `LocalOutputExtension` and the algebra of `term` (`term_final_alg`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The norm of the unit cutoff in `r` times. -/
def cutNormR (θ : ℝ) (r : ℕ) : ℝ≥0∞ := timeFourierNorm θ (coordinateCutoff (r := r) Layered.chiUnit)

theorem cutNormR_lt_top (θ : ℝ) (r : ℕ) : cutNormR θ r < ⊤ :=
  timeFourierNorm_lt_top_of_smooth_compact θ
    (coordinateCutoff_hasCompactSupport Layered.chiUnit_hasCompactSupport)
    (coordinateCutoff_contDiff Layered.chiUnit_contDiff)

/-- **A constant on a set inside a unit cell** has restricted norm at most its modulus times `cutNormR`. -/
theorem rn_const_le {r : ℕ} (θ : ℝ) (qt : Fin r → ℝ) {B : Set (Fin r → ℝ)}
    (hB : B ⊆ VineEstS3.FS.cell qt) (V : ℂ) :
    rn θ B (fun _ => V) ≤ ‖V‖ₑ * cutNormR θ r := by
  refine (rn_le θ (g := fun t => V • VineEstS3.FS.cutQ qt t) fun t ht => by
    rw [smul_eq_mul, VineEstS3.FS.cutQ_eq_one (hB ht), mul_one]).trans ?_
  rw [timeFourierNorm_smul]
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  have e : VineEstS3.FS.cutQ qt = fun t => coordinateCutoff (r := r) Layered.chiUnit (t + -qt) := by
    funext t
    simp only [VineEstS3.FS.cutQ, sub_eq_add_neg]
  rw [e, timeFourierNorm_translate]
  rfl

/-- The R176 box lies in the unit cell at `(p, q')`. -/
theorem rootBox_sub_cell (p q' t : ℝ) :
    {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p q' ∧ t ≤ ts 0} ⊆ VineEstS3.FS.cell ![p, q'] := by
  intro ts hts i
  fin_cases i
  · simpa using hts.1.1.1
  · simpa using hts.1.1.2

/-- **On the R176 box the (P2) kernel does not depend on the clocks.** -/
theorem rootTerm_kernel_eq {P : WTParams} (hL1 : 1 ≤ P.L) {LG LGp LGi : LayeredGarden 1}
    {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
    (C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg) {s t : ℝ} (hst : s ≤ t) (H : LeafProfiles 1 P.d)
    (B : (Fin 1 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator (cpair m Qr Qg inner) ind)
    {T T' s' s'' : ℝ} (hT : t ≤ T) (hT' : t ≤ T') (k : Mom P.d) :
    kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => T) s' (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t T) k (fun _ => 0) 0 =
      kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => T') s'' (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t T') k (fun _ => 0) 0 := by
  have D : PairOnly LG m Qr Qg inner LGi LGr LGg := PairOnly.of_cutTerm C
  have hMf := star_pair_mult D S ω F M Fu Mu ind hind
  have hMc := star_pair_Mc_le D S ω cω hpres F M Fu Mu ind hind.1
  have hmiB := FiltCoh.norm_d5Mult_le (pullS D.hp.ιi S) (fun z => ω (D.hp.ιi z)) (fun z => cω (D.hp.ιi z))
    (pull_pres (J := 30 * P.d) D.hp.ιi hpres)
    (pullF D.hp.βi F) (fun _ => false) (fun y => M (D.hp.βi y)) (pullF D.hp.βi Fu) (fun y => Mu (D.hp.βi y))
  have hmrB := FiltCoh.norm_d5Mult_le (pullS D.hp.ιr S) (fun z => ω (D.hp.ιr z)) (fun z => cω (D.hp.ιr z))
    (pull_pres (J := 30 * P.d) D.hp.ιr hpres)
    (pullF D.hp.βr F) (fun _ => false) (fun y => M (D.hp.βr y)) (pullF D.hp.βr Fu) (fun y => Mu (D.hp.βr y))
  have hmgB := FiltCoh.norm_d5Mult_le (pullS D.hp.ιg S) (fun z => ω (D.hp.ιg z)) (fun z => cω (D.hp.ιg z))
    (pull_pres (J := 30 * P.d) D.hp.ιg hpres)
    (pullF D.hp.βg F) (fun _ => false) (fun y => M (D.hp.βg y)) (pullF D.hp.βg Fu) (fun y => Mu (D.hp.βg y))
  set CM : ℝ := max (costB S cω D.hp.rootB * costB S cω D.hp.bB)
    (max ((∏ a ∈ pullS D.hp.ιi S, max (cω (D.hp.ιi a)) 0) * FiltCoh.chiDSup ^ (pullF D.hp.βi F).card *
      FiltCoh.chiDSup ^ (pullF D.hp.βi Fu).card)
    (max ((∏ a ∈ pullS D.hp.ιr S, max (cω (D.hp.ιr a)) 0) * FiltCoh.chiDSup ^ (pullF D.hp.βr F).card *
      FiltCoh.chiDSup ^ (pullF D.hp.βr Fu).card)
      ((∏ a ∈ pullS D.hp.ιg S, max (cω (D.hp.ιg a)) 0) * FiltCoh.chiDSup ^ (pullF D.hp.βg F).card *
        FiltCoh.chiDSup ^ (pullF D.hp.βg Fu).card))) with hCM
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  have key := fun (T₀ s₀ : ℝ) (hT₀ : t ≤ T₀) => kernelProt_rootTerm_cfg D P.L P.γ P.δ H hHs _ _ _ _ _ hMf CM
    (fun A B => (hMc A B).trans (le_max_left _ _))
    (fun κ => (hmiB κ).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (fun κ => (hmrB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    (fun κ => (hmgB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    T₀ s₀ s t hT₀ (hst.trans hT₀) k
  rw [key T s' hT, key T' s'' hT']

/-- **(P2) in `X^{θ,30d,0}` on the R176 box** (stars, filters, dagger). -/
theorem rootTerm_final {θ : ℝ} (hθ0 : 0 ≤ θ) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
    (K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c CL : ℝ} (hθc : PieceLoss P θ c') (hc'0 : 0 ≤ c')
    (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) (hCL : 0 ≤ CL) (hC11 : 1 ≤ P.C₁)
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL (cutNormR θ 2).toReal P.d * P.δ * P.C₁ ^ 2 *
      P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {LG LGp LGi : LayeredGarden 1}
    {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
    (C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg)
    (hsh : ProtShape p (cpair m Qr Qg inner) LG) (hsz : (cpair m Qr Qg inner).size = 2 * n)
    (hamb : TreeAmb p (cpair m Qr Qg inner) LG) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
    (q' : ℕ) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator (cpair m Qr Qg inner) ind)
    (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (ProtCfg.rootTerm.box (cpair m Qr Qg inner) t p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
        regBound P n (protIncoh (cpair m Qr Qg inner) LG) * ENNReal.ofReal (leafSizeProduct LG B) := by
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  set Ct : ℝ := (cutNormR θ 2).toReal with hCtdef
  have hCt : cutNormR θ 2 = ENNReal.ofReal Ct := (ENNReal.ofReal_toReal (cutNormR_lt_top θ 2).ne).symm
  have hCt0 : 0 ≤ Ct := ENNReal.toReal_nonneg
  set g := protIncoh (cpair m Qr Qg inner) LG with hg
  set Rb : ℝ := coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (3 * c') *
    (P.C₁ ^ 2 * rb P (n - 1) g) * leafSizeProduct LG B * starCost S cω with hRb
  have hr := rb_nonneg hC1 K.hδ hL0 (n - 1) g
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hsc := starCost_nonneg' S cω
  have hlat0 : 0 ≤ latC P.d * P.L ^ P.d := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
  have hA : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 := by positivity
  have hRb0 : 0 ≤ Rb := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hL0 _))
    (mul_nonneg (by positivity) hr)) hleaf) hsc
  refine (hLOE P.L hL1 (ProtCfg.rootTerm.box (cpair m Qr Qg inner) t p q') b₀ c₀ _ (ENNReal.ofReal (Ct * Rb))
    fun k _ => (XNorm00Restr_single_le_rn θ _ _ k).trans ?_).trans ?_
  · rw [box_rootTerm]
    have hcongr : rn θ {ts : Fin 2 → ℝ | ts ∈ timeBoxGt (p : ℝ) q' ∧ t ≤ ts 0}
        (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) =
        rn θ {ts : Fin 2 → ℝ | ts ∈ timeBoxGt (p : ℝ) q' ∧ t ≤ ts 0}
        (fun _ => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => t) s (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t t) k (fun _ => 0) 0) :=
      rn_congr θ fun ts hts => rootTerm_kernel_eq hL1 C hst.le H B hH S ω cω hpres F M Fu Mu ind hind hts.2 le_rfl k
    rw [hcongr]
    refine (rn_const_le θ ![(p : ℝ), (q' : ℝ)] (rootBox_sub_cell (p : ℝ) q' t) _).trans ?_
    have hV := rootTerm_value_le hθ0 K hθc hp hn C hsh hsz hamb hps hst htp t s le_rfl H B hH S ω cω hpres
      F M hM Fu Mu hMu ind hind k
    rw [hCt]
    calc _ ≤ ENNReal.ofReal Rb * ENNReal.ofReal Ct := mul_le_mul' hV le_rfl
      _ = ENNReal.ofReal (Ct * Rb) := by rw [← ENNReal.ofReal_mul hRb0, mul_comm]
  -- the algebra
  have hn1 : 1 ≤ n := by
    obtain ⟨_, _, _, _, -, -, -, -, h⟩ := cut_sizes (Xp := .nil) hsz
    omega
  rw [prod_ofReal_starCost, regBound_eq_rb, rb_succ P hn1, ← ENNReal.ofReal_mul (mul_nonneg hCL (pow_nonneg hL0 _)),
    ← ENNReal.ofReal_mul hsc, ← ENNReal.ofReal_mul (mul_nonneg hsc (Real.rpow_nonneg hL0 _)),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hsc (Real.rpow_nonneg hL0 _))
      (mul_nonneg (mul_nonneg hC1 K.hδ) hr))]
  refine ENNReal.ofReal_le_ofReal ?_
  have halg := term_final_alg (P := P) (Cr := Ct) (CL := CL) (K := termK CL Ct P.d) (β := starCost S cω)
    (leaf := leafSizeProduct LG B) (r := rb P (n - 1) g) (c := c) (c' := c') hL1 K.hδ hC1 hCt0 hCL hsc hleaf hr
    rfl hbig hc
  have hL34 : P.L ^ (3 * c') ≤ P.L ^ (4 * c') := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hC23 : P.C₁ ^ 2 ≤ P.C₁ ^ 3 := pow_le_pow_right₀ hC11 (by norm_num)
  have hmono : Rb ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
      (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG B * starCost S cω := by
    calc Rb = (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * (leafSizeProduct LG B * starCost S cω)) *
          (P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) g)) := by rw [hRb]; ring
      _ ≤ (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * (leafSizeProduct LG B * starCost S cω)) *
          (P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hL34 (mul_le_mul_of_nonneg_right hC23 hr)
          (mul_nonneg (by positivity) hr) (Real.rpow_nonneg hL0 _)) (mul_nonneg hA (mul_nonneg hleaf hsc))
      _ = _ := by ring
  calc CL * P.L ^ (31 * P.d) * (Ct * Rb)
      ≤ CL * P.L ^ (31 * P.d) * (Ct * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG B * starCost S cω)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hCt0)
          (mul_nonneg hCL (pow_nonneg hL0 _))
    _ = CL * P.L ^ (31 * P.d) * (starCost S cω * (Ct * (coupling P.d P.L P.γ P.δ ^ 2 *
          (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG B))) := by
        ring
    _ ≤ P.L ^ c * (P.C₁ * P.δ * rb P (n - 1) g) * (starCost S cω * leafSizeProduct LG B) := halg
    _ = _ := by ring

end WaveTurbulence.Flower.ProtPin
