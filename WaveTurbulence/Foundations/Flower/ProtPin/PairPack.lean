/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootKink
public import WaveTurbulence.Foundations.Flower.ProtPin.RootTerm

/-! # D3 PROT-PIN: the one-pair package

For a one-pair protected tree `X = pair m Qr Qg inner nil` (pieces `CutTermData LG nil …`), `pair_pack` produces, at one
output `k`, the exceptional coefficients `c e`, the linked frequencies `A e` and the piece products
`W e x = K_int(x₀, x₁) Q_r Q_g(cup x₀ x₁)` (continuous, finite restricted norms on `timeBoxGt p p`) with

* `Σ'_e ‖c e‖ · rn(W e) ≤ 4^θ · pairRb` (the gates on the pieces and the exceptional sum of `term`), and
* D2c's identities in this notation: the root at `σ ≤ T` (`rootFix σ`, used by (P1) and (trace)):
  `Σ'_e c e ∫_{rootU0 T σ s'} e^{πiA_e(σ-u)} W e (σ, u) du`; root at `t` and terminal at `s` ((P2)):
  `Σ'_e c e e^{πiA_e(t-s)} W e (t, s)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The one-pair budget at one output. -/
def pairRb (P : WTParams) (c' : ℝ) (n g : ℕ) (leaf CS : ℝ) : ℝ :=
  coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) g) * leaf * CS

theorem pairRb_nonneg {P : WTParams} {c' : ℝ} (hC1 : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ)
    {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS) : 0 ≤ pairRb P c' n g leaf CS := by
  unfold pairRb
  have := rb_nonneg hC1 hδ hL (n - 1) g
  have := Real.rpow_nonneg hL (3 * c')
  positivity

/-- **The one-pair package** (pieces, coefficients, exceptional sum, identities). -/
theorem pair_pack {θ : ℝ} (hθ0 : 0 ≤ θ) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {c' : ℝ} (hθc : PieceLoss P θ c') {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
    {inner : RegChain} (C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg)
    (hsh : ProtShape p (cpair m Qr Qg inner) LG) (hsz : (cpair m Qr Qg inner).size = 2 * n)
    (hamb : TreeAmb p (cpair m Qr Qg inner) LG)
    (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator (cpair m Qr Qg inner) ind)
    (k : Mom P.d) :
    ∃ (c : PairE m P.d → ℂ) (A : PairE m P.d → ℝ) (W : PairE m P.d → (Fin 2 → ℝ) → ℂ),
      (∀ e, Continuous (W e)) ∧ (∀ e, rn θ (timeBoxGt p p) (W e) < ⊤) ∧
      (∑' e, ‖c e‖ₑ * rn θ (timeBoxGt p p) (W e) ≤
        ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) *
          ENNReal.ofReal (pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG) (leafSizeProduct LG B)
            (starCost S cω))) ∧
      (∀ T σ s' : ℝ, σ ≤ T →
        kernelProt P.L P.γ P.δ LG H
            (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
              filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
            (fun _ => T) s' (rootFix σ) k (fun _ => 0) 0 =
          ∑' e, c e * ∫ u in rootU0 LG m inner T σ s', rootPh (A e) σ u * W e ![σ, u]) ∧
      (∀ T s' s t : ℝ, t ≤ T → s ≤ T →
        kernelProt P.L P.γ P.δ LG H
            (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
              filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
            (fun _ => T) s' (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t T) k (fun _ => 0) 0 =
          ∑' e, c e * (rootPh (A e) t s * W e ![t, s])) := by
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have D : PairOnly LG m Qr Qg inner LGi LGr LGg := PairOnly.of_cutTerm C
  have hsh' := hsh
  obtain ⟨hwf, -, -, hch⟩ := hsh'
  have hshC : ProtShape p (appendChain .nil (cpair m Qr Qg inner)) LG := hsh
  obtain ⟨-, hwfi, hwfr, hwfg⟩ := cut_wf C hwf
  obtain ⟨np, ni, nr, ng, hnp, hni, hnr, hng, hnsum⟩ := cut_sizes (Xp := .nil) hsz
  obtain ⟨-, -, hli, hlonei, hlr, hlg⟩ := cut_layers C hshC
  obtain ⟨-, hHi, hHr, hHg⟩ := cut_leafwise C hH
  obtain ⟨-, fI, fR, fG⟩ := cut_flat C hshC hamb
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hle_n : ∀ j, j ≤ n → j ≤ P.N (p + 1) ^ 4 := fun j hj => hj.trans hn
  set ζ := LG.garden.sig 0 with hζ
  -- the multiplier
  have hMf := star_pair_mult D S ω F M Fu Mu ind hind
  have hMc := star_pair_Mc_le D S ω cω hpres F M Fu Mu ind hind.1
  have hGi := pull_pres (J := 30 * P.d) D.hp.ιi hpres
  have hGr := pull_pres (J := 30 * P.d) D.hp.ιr hpres
  have hGg := pull_pres (J := 30 * P.d) D.hp.ιg hpres
  set mi := pullMult D.hp.ιi D.hp.βi S ω F M Fu Mu with hmi
  set mr := pullMult D.hp.ιr D.hp.βr S ω F M Fu Mu with hmr
  set mg := pullMult D.hp.ιg D.hp.βg S ω F M Fu Mu with hmg
  have hmiB := FiltCoh.norm_d5Mult_le (pullS D.hp.ιi S) (fun z => ω (D.hp.ιi z)) (fun z => cω (D.hp.ιi z)) hGi
    (pullF D.hp.βi F) (fun _ => false) (fun y => M (D.hp.βi y)) (pullF D.hp.βi Fu) (fun y => Mu (D.hp.βi y))
  have hmrB := FiltCoh.norm_d5Mult_le (pullS D.hp.ιr S) (fun z => ω (D.hp.ιr z)) (fun z => cω (D.hp.ιr z)) hGr
    (pullF D.hp.βr F) (fun _ => false) (fun y => M (D.hp.βr y)) (pullF D.hp.βr Fu) (fun y => Mu (D.hp.βr y))
  have hmgB := FiltCoh.norm_d5Mult_le (pullS D.hp.ιg S) (fun z => ω (D.hp.ιg z)) (fun z => cω (D.hp.ιg z)) hGg
    (pullF D.hp.βg F) (fun _ => false) (fun y => M (D.hp.βg y)) (pullF D.hp.βg Fu) (fun y => Mu (D.hp.βg y))
  set Ca : ℝ := costB S cω D.hp.rootB * costB S cω D.hp.bB with hCa
  have hCa0 : 0 ≤ Ca := mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _)
  set Bi : ℝ := (∏ a ∈ pullS D.hp.ιi S, max (cω (D.hp.ιi a)) 0) * FiltCoh.chiDSup ^ (pullF D.hp.βi F).card *
    FiltCoh.chiDSup ^ (pullF D.hp.βi Fu).card with hBi
  set Br : ℝ := (∏ a ∈ pullS D.hp.ιr S, max (cω (D.hp.ιr a)) 0) * FiltCoh.chiDSup ^ (pullF D.hp.βr F).card *
    FiltCoh.chiDSup ^ (pullF D.hp.βr Fu).card with hBr
  set Bg : ℝ := (∏ a ∈ pullS D.hp.ιg S, max (cω (D.hp.ιg a)) 0) * FiltCoh.chiDSup ^ (pullF D.hp.βg F).card *
    FiltCoh.chiDSup ^ (pullF D.hp.βg Fu).card with hBg
  set CM : ℝ := max Ca (max Bi (max Br Bg)) with hCM
  -- the pieces as time functions
  set Ki : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGi
    (cutHi .nil m H) (fun _ => x 0) (x 1) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 mi with hKi
  set fr : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGr
    (cutHr .nil m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 mr
    with hfr
  set fg : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGg
    (cutHg .nil m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 mg
    with hfg
  set Kr : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fr e (cupR m inner ζ (x 0) (x 1) 0) (cupR m inner ζ (x 0) (x 1) 1) with hKr
  set Kg : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fg e (cupG m inner ζ (x 0) (x 1) 0) (cupG m inner ζ (x 0) (x 1) 1) with hKg
  set W : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Ki e x * (Kr e x * Kg e x) with hW
  have hKic : ∀ e, Continuous (Ki e) := fun e =>
    FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGi (cutHi .nil m H) C.decI mi Bi hmiB _
      (summable_coset_piece hHi hL1 _)
  have hor : ∀ {f : ℝ → ℝ → ℂ} (c : ℝ → ℝ → Fin 2 → ℝ),
      ((∀ u v, c u v 0 = u ∧ c u v 1 = v) ∨ (∀ u v, c u v 0 = v ∧ c u v 1 = u)) →
      Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1)) →
      Continuous (fun x : Fin 2 → ℝ => f (c (x 0) (x 1) 0) (c (x 0) (x 1) 1)) := by
    intro f c hc hf
    rcases hc with hc | hc
    · simpa only [(hc _ _).1, (hc _ _).2] using hf
    · simp only [(hc _ _).1, (hc _ _).2]
      exact hf.comp (show Continuous fun x : Fin 2 → ℝ => ![x 1, x 0] by fun_prop)
  have hKrc : ∀ e, Continuous (Kr e) := fun e =>
    hor (f := fr e) (cupR m inner ζ) (cupR_cases m inner ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGr (cutHr .nil m inner ζ H) C.decR.1.1 mr Br hmrB _
        (summable_coset_piece hHr hL1 _))
  have hKgc : ∀ e, Continuous (Kg e) := fun e =>
    hor (f := fg e) (cupG m inner ζ) (cupG_cases m inner ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg (cutHg .nil m inner ζ H) C.decG.1.1 mg Bg hmgB _
        (summable_coset_piece hHg hL1 _))
  have hWc : ∀ e, Continuous (W e) := fun e => (hKic e).mul ((hKrc e).mul (hKgc e))
  -- the gates on the pieces
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
  have hls : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal), 0 ≤ leafSizeProduct LGx Bx :=
    fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  set gi := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) with hgi
  set gr := LGr.incoherency Qr.links with hgr
  set gg := LGg.incoherency Qg.links with hgg
  set bi : ℝ := P.L ^ c' * rb P ni gi * leafSizeProduct LGi (cutBi .nil m B) *
    starCost (pullS D.hp.ιi S) (fun z => cω (D.hp.ιi z)) with hbi
  set br : ℝ := P.L ^ c' * rb P nr gr * leafSizeProduct LGr (cutBr .nil m inner ζ B) *
    starCost (pullS D.hp.ιr S) (fun z => cω (D.hp.ιr z)) with hbr
  set bg : ℝ := P.L ^ c' * rb P ng gg * leafSizeProduct LGg (cutBg .nil m inner ζ B) *
    starCost (pullS D.hp.ιg S) (fun z => cω (D.hp.ιg z)) with hbg
  have hKib : ∀ e, rn θ (timeBoxGt p p) (Ki e) ≤ ENNReal.ofReal bi := fun e => by
    rw [hbi, ← piece_conv hL0 hrb _ _ c' ni gi _]
    exact tree_piece_star K hp (hle_n ni (by omega)) hθc inner LGi hwfi hni C.decI hli hlonei fI _ _ _ hGi
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) (cutHi .nil m H) (cutBi .nil m B) hHi _
  set Jr : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.1) ^ (30 * P.d))⁻¹ with hJr
  set Jg : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.2) ^ (30 * P.d))⁻¹ with hJg
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKrb : ∀ e, rn θ (timeBoxGt p p) (Kr e) ≤ ENNReal.ofReal br * ENNReal.ofReal (Jr e) := fun e => by
    refine (rn_couple_oriented (fr e) (cupR m inner ζ) (cupR_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbr, ← piece_conv hL0 hrb _ _ c' nr gr _]
    exact couple_piece_star K hp (hle_n nr (by omega)) hθc Qr LGr hwfr hnr C.decR hlr fR _ _ _ hGr
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHr _
  have hKgb : ∀ e, rn θ (timeBoxGt p p) (Kg e) ≤ ENNReal.ofReal bg * ENNReal.ofReal (Jg e) := fun e => by
    refine (rn_couple_oriented (fg e) (cupG m inner ζ) (cupG_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbg, ← piece_conv hL0 hrb _ _ c' ng gg _]
    exact couple_piece_star K hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng C.decG hlg fG _ _ _ hGg
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHg _
  have hfinr : ∀ e, rn θ (timeBoxGt p p) (Kr e) < ⊤ := fun e =>
    (hKrb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfing : ∀ e, rn θ (timeBoxGt p p) (Kg e) < ⊤ := fun e =>
    (hKgb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfini : ∀ e, rn θ (timeBoxGt p p) (Ki e) < ⊤ := fun e => (hKib e).trans_lt ENNReal.ofReal_lt_top
  have hRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Kr e) * rn θ (timeBoxGt p p) (Kg e) := fun e =>
    rn_mul_le hθ0 (timeBoxGt_cl p) (Kr e) (Kg e) (hKgc e) (hfinr e) (hfing e)
  have hfinRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) < ⊤ := fun e =>
    (hRG e).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfinr e)) (hfing e))
  have hWb : ∀ e, rn θ (timeBoxGt p p) (W e) ≤
      T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
        (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))) := fun e => by
    refine (rn_mul_le hθ0 (timeBoxGt_cl p) (Ki e) (fun x => Kr e x * Kg e x) ((hKrc e).mul (hKgc e))
      (hfini e) (hfinRG e)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Ki e) * rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x)
        ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal bi *
            (ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
              (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))) :=
          mul_le_mul' (mul_le_mul' le_rfl (hKib e)) ((hRG e).trans (mul_le_mul' (mul_le_mul' le_rfl (hKrb e))
            (hKgb e)))
      _ = _ := by rw [hT4]; ring
  have hWfin : ∀ e, rn θ (timeBoxGt p p) (W e) < ⊤ := fun e =>
    (hWb e).trans_lt (by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ ?_)) <;>
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- the coefficients
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  set c₀ : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
    (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) with hc₀
  set A : PairE m P.d → ℝ := fun e => cutFreq m ζ P.L P.γ P.δ k e with hA
  set c : PairE m P.d → ℂ := fun e => c₀ * ((fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB (starA m P.L k e) *
    fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB (starB m P.L k e) * ((indB ind (starB m P.L k e) : ℝ) : ℂ)) *
      (cutEps m e : ℂ)) with hc
  have hMc' := fun A B => (hMc A B).trans (le_max_left Ca (max Bi (max Br Bg)))
  have hmi' := fun κ => (hmiB κ).trans ((le_max_left _ _).trans (le_max_right Ca (max Bi (max Br Bg))))
  have hmr' := fun κ => (hmrB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_right Ca (max Bi (max Br Bg)))))
  have hmg' := fun κ => (hmgB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right Ca (max Bi (max Br Bg)))))
  refine ⟨c, A, W, hWc, hWfin, ?_, ?_, ?_⟩
  · -- the exceptional sum
    set cc : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hcc
    have hcc0 : 0 ≤ cc := sq_nonneg _
    have hc0n : ‖c₀‖ = cc := norm_cutPrefactor hL0 K.hδ _ _
    have hce : ∀ e, ‖c e‖ₑ ≤ ENNReal.ofReal (cc * Ca) := fun e => by
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hMe : ‖(fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB (starA m P.L k e) *
          fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB (starB m P.L k e) * ((indB ind (starB m P.L k e) : ℝ) : ℂ)) *
            (cutEps m e : ℂ)‖ ≤ Ca := by
        refine (norm_mul_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) hCa0).trans (by rw [mul_one])
      calc ‖c e‖ = ‖c₀‖ * ‖(fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB (starA m P.L k e) *
          fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB (starB m P.L k e) * ((indB ind (starB m P.L k e) : ℝ) : ℂ)) *
            (cutEps m e : ℂ)‖ := norm_mul _ _
        _ ≤ cc * Ca := by rw [hc0n]; exact mul_le_mul_of_nonneg_left hMe hcc0
    set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
    set Z : ℝ≥0∞ := ENNReal.ofReal (cc * Ca) * T4 * (ENNReal.ofReal bi * ENNReal.ofReal br * ENNReal.ofReal bg)
      with hZ
    have hterm : ∀ e, ‖c e‖ₑ * rn θ (timeBoxGt p p) (W e) ≤ Z * (f e.1.2.1 * f e.1.2.2) := fun e => by
      calc ‖c e‖ₑ * rn θ (timeBoxGt p p) (W e)
          ≤ ENNReal.ofReal (cc * Ca) * (T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br *
              ENNReal.ofReal (Jr e)) * (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))))) :=
            mul_le_mul' (hce e) (hWb e)
        _ = Z * (f e.1.2.1 * f e.1.2.2) := by rw [hZ, hf]; ring
    have hsum : ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt p p) (W e) ≤
        Z * (ENNReal.ofReal (latC P.d * P.L ^ P.d) * ENNReal.ofReal (latC P.d * P.L ^ P.d)) := by
      refine (ENNReal.tsum_le_tsum hterm).trans ?_
      rw [ENNReal.tsum_mul_left]
      refine mul_le_mul' le_rfl ((tsum_pairE_le m f).trans (mul_le_mul' ?_ ?_)) <;>
        exact tsum_decay_le hd1 hL1 k
    refine hsum.trans ?_
    have hlat0 : 0 ≤ latC P.d * P.L ^ P.d := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
    have hn1 : ni + nr + ng = n - 1 := by have : RegChain.nil.size = 0 := rfl; omega
    have hg : gi + gr + gg = protIncoh (cpair m Qr Qg inner) LG := (PairOnly.incoherency_of_chainIn C hch).symm
    have hleaf : leafSizeProduct LG B = leafSizeProduct LGi (cutBi .nil m B) *
        leafSizeProduct LGr (cutBr .nil m inner ζ B) * leafSizeProduct LGg (cutBg .nil m inner ζ B) := by
      rw [cut_leafSize C B, leafSize_nil_prefix C, one_mul]
    have hcost : starCost S cω = Ca * (starCost (pullS D.hp.ιi S) (fun z => cω (D.hp.ιi z)) *
        (starCost (pullS D.hp.ιr S) (fun z => cω (D.hp.ιr z)) *
          starCost (pullS D.hp.ιg S) (fun z => cω (D.hp.ιg z)))) :=
      star_pair_cost D S cω
    have hprod : bi * br * bg = P.L ^ (3 * c') * (P.C₁ ^ 2 * rb P (n - 1) (protIncoh (cpair m Qr Qg inner) LG)) *
        leafSizeProduct LG B * (starCost (pullS D.hp.ιi S) (fun z => cω (D.hp.ιi z)) *
          (starCost (pullS D.hp.ιr S) (fun z => cω (D.hp.ιr z)) *
            starCost (pullS D.hp.ιg S) (fun z => cω (D.hp.ιg z)))) := by
      rw [hbi, hbr, hbg, hleaf, ← hn1, ← hg]
      have h3 : P.L ^ (3 * c') = P.L ^ c' * P.L ^ c' * P.L ^ c' := by
        rw [show 3 * c' = c' + c' + c' by ring, Real.rpow_add (by linarith), Real.rpow_add (by linarith)]
      rw [h3, ← rb_three (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := ni) (n₂ := nr) (n₃ := ng) (g₁ := gi)
        (g₂ := gr) (g₃ := gg)]
      ring
    have hi0 : 0 ≤ bi := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
    have hr0 : 0 ≤ br := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
    have hg0 : 0 ≤ bg := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
    have hccCa : 0 ≤ cc * Ca := mul_nonneg hcc0 hCa0
    rw [hZ, ← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul (mul_nonneg hi0 hr0), ← ENNReal.ofReal_mul hlat0]
    have hval : cc * Ca * (bi * br * bg) * (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d)) =
        pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG) (leafSizeProduct LG B) (starCost S cω) := by
      rw [pairRb, hcost]
      linear_combination (cc * Ca * (latC P.d * P.L ^ P.d) ^ 2) * hprod
    calc ENNReal.ofReal (cc * Ca) * T4 * ENNReal.ofReal (bi * br * bg) *
          ENNReal.ofReal (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d))
        = T4 * (ENNReal.ofReal (cc * Ca) * ENNReal.ofReal (bi * br * bg) *
            ENNReal.ofReal (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d))) := by ring
      _ = T4 * ENNReal.ofReal (cc * Ca * (bi * br * bg) * (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d))) := by
          rw [← ENNReal.ofReal_mul hccCa,
            ← ENNReal.ofReal_mul (mul_nonneg hccCa (mul_nonneg (mul_nonneg hi0 hr0) hg0))]
      _ ≤ _ := le_of_eq (by rw [hval])
  · -- the root at `σ`
    intro T σ s' hσT
    have hid := D.kernelProt_root0 P.L P.γ P.δ H hHs _ _ _ _ _ hMf CM hMc' hmi' hmr' hmg' T s' σ hσT k
    refine hid.trans ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun e => ?_
    rw [show c e = c₀ * ((fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB (starA m P.L k e) *
      fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB (starB m P.L k e) * ((indB ind (starB m P.L k e) : ℝ) : ℂ)) *
        (cutEps m e : ℂ)) from rfl, mul_assoc c₀]
    congr 1
    congr 1
    refine setIntegral_congr_fun (measurableSet_rootU0 _ _ _ _ _ _) fun u _ => ?_
    simp only [cut_kernel_tree_m _ _ _ _ C.decI, cut_kernel_couple_m _ _ _ _ C.decR,
      cut_kernel_couple_m _ _ _ _ C.decG]
    rfl
  · -- the root at `t`, the terminal node at `s`
    intro T s' s t htT hsT
    have hid := kernelProt_rootTerm_cfg D P.L P.γ P.δ H hHs _ _ _ _ _ hMf CM hMc' hmi' hmr' hmg' T s' s t htT hsT k
    refine hid.trans ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun e => ?_
    rw [show c e = c₀ * ((fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB (starA m P.L k e) *
      fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB (starB m P.L k e) * ((indB ind (starB m P.L k e) : ℝ) : ℂ)) *
        (cutEps m e : ℂ)) from rfl, mul_assoc c₀]
    congr 1
    congr 1
    simp only [cut_kernel_tree_m _ _ _ _ C.decI, cut_kernel_couple_m _ _ _ _ C.decR,
      cut_kernel_couple_m _ _ _ _ C.decG]
    rfl

end WaveTurbulence.Flower.ProtPin
