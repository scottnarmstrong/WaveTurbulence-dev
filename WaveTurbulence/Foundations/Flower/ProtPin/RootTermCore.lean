/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.PairStar
public import WaveTurbulence.Foundations.Flower.ProtPin.Pointwise
public import WaveTurbulence.Foundations.Flower.ProtPin.TermStar
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckNil

/-! # D3 PROT-PIN: (P2) above the pinned root — the kernel is a constant, bounded pointwise

For a one-pair protected tree `X = pair m Qr Qg inner nil` with its root pinned at `t` and its terminal node at `s`
(`ProtCfg.rootTerm`), and an upper clock `T ≥ t`, D2c's `kernelProt_rootTerm_cfg` gives
`c² (iζ_a)(iζ_b) Σ'_e Mc ε_e e^{πiA_e(t−s)} K_int(t, s) Q_r(t, s) Q_g(t, s)`, independent of `T` and of the port clock.
`rootTerm_value_le` bounds it at one output: the pieces at the point `(t, s)` by their restricted norms
(`enorm_le_rn`, continuity), hence by the gates (`tree_piece_star`, `couple_piece_star`; coherent pieces flat by
`cut_flat` with an empty prefix), the exceptional sum as in `term`. This is the `T ≥ t` part of (P2) in either option
of finding F-D3-4. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The prefix of a one-pair chain is its lone leaf: it has no input leaves. -/
theorem leafSize_nil_prefix {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
    {Qr Qg : RegCpl} {inner : RegChain} (C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg)
    (B : (Fin 1 × TTree.Path) → NNReal) : leafSizeProduct LGp B = 1 := by
  unfold leafSizeProduct
  refine Finset.prod_eq_one fun ℓ hℓ => ?_
  exfalso
  have hm := (Finset.mem_filter.mp hℓ).2.2
  have hX := C.decP
  have h2 : ℓ.1.2 ∈ (LGp.garden.tree 0).leaves := by
    have h := ℓ.2
    rwa [Fin.fin_one_eq_zero ℓ.1.1] at h
  rw [hX.1] at h2
  have hpath : ℓ.1.2 = [] := by
    simpa [RegChain.plug, TTree.leaves] using h2
  rw [hX.2.1 ℓ] at hm
  simp [hpath, RegChain.lonePath] at hm

/-- Three pieces: `C₁³ (C₁δ)^{n₁+n₂+n₃} L^{-(γ₁-√η) g}`. -/
theorem rb_three {P : WTParams} (hL : 0 < P.L) {n₁ n₂ n₃ g₁ g₂ g₃ : ℕ} :
    rb P n₁ g₁ * rb P n₂ g₂ * rb P n₃ g₃ = P.C₁ ^ 2 * rb P (n₁ + n₂ + n₃) (g₁ + g₂ + g₃) := by
  unfold rb
  push_cast
  rw [show -(P.gamma1 - Real.sqrt P.η) * ((g₁ : ℝ) + g₂ + g₃) =
    -(P.gamma1 - Real.sqrt P.η) * g₁ + -(P.gamma1 - Real.sqrt P.η) * g₂ + -(P.gamma1 - Real.sqrt P.η) * g₃ by ring,
    Real.rpow_add hL, Real.rpow_add hL]
  ring

/-- **(P2) above the pinned root, one output.** -/
theorem rootTerm_value_le {θ : ℝ} (hθ0 : 0 ≤ θ) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
    (K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ} (hθc : PieceLoss P θ c') {p : ℕ} (hp : p < P.D) {n : ℕ}
    (hn : n ≤ P.N (p + 1) ^ 4) {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
    {Qr Qg : RegCpl} {inner : RegChain} (C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg)
    (hsh : ProtShape p (cpair m Qr Qg inner) LG) (hsz : (cpair m Qr Qg inner).size = 2 * n)
    (hamb : TreeAmb p (cpair m Qr Qg inner) LG) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
    (T s' : ℝ) (htT : t ≤ T) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator (cpair m Qr Qg inner) ind)
    (k : Mom P.d) :
    ‖kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => T) s' (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t T) k (fun _ => 0) 0‖ₑ ≤
      ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (3 * c') *
        (P.C₁ ^ 2 * rb P (n - 1) (protIncoh (cpair m Qr Qg inner) LG)) * leafSizeProduct LG B *
          starCost S cω) := by
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
  -- the multiplier
  have hMf := star_pair_mult D S ω F M Fu Mu ind hind
  have hMc := star_pair_Mc_le D S ω cω hpres F M Fu Mu ind hind.1
  have hGi := pull_pres (J := 30 * P.d) D.hp.ιi hpres
  have hGr := pull_pres (J := 30 * P.d) D.hp.ιr hpres
  have hGg := pull_pres (J := 30 * P.d) D.hp.ιg hpres
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
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  rw [kernelProt_rootTerm_cfg D P.L P.γ P.δ H hHs _ _ _ _ _ hMf CM
    (fun A B => (hMc A B).trans (le_max_left _ _))
    (fun κ => (hmiB κ).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (fun κ => (hmrB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    (fun κ => (hmgB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    T s' s t htT (hst.le.trans htT) k]
  -- the pieces at the point `(t, s)`
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
  set br : ℝ := P.L ^ c' * rb P nr gr * leafSizeProduct LGr (cutBr .nil m inner (LG.garden.sig 0) B) *
    starCost (pullS D.hp.ιr S) (fun z => cω (D.hp.ιr z)) with hbr
  set bg : ℝ := P.L ^ c' * rb P ng gg * leafSizeProduct LGg (cutBg .nil m inner (LG.garden.sig 0) B) *
    starCost (pullS D.hp.ιg S) (fun z => cω (D.hp.ιg z)) with hbg
  have hts : (![t, s] : Fin 2 → ℝ) ∈ timeBoxGt (p : ℝ) p := by
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith
  have htsb : ∀ c : Fin 2 → ℝ, (c 0 = t ∧ c 1 = s) ∨ (c 0 = s ∧ c 1 = t) → c ∈ timeBox (p : ℝ) p := by
    intro c hc
    rcases hc with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [timeBox, Set.mem_ofPred_eq, h0, h1, Set.mem_Icc, Set.mem_Icc] <;>
      constructor <;> constructor <;> linarith
  have hBcl : ∀ x ∈ timeBox (p : ℝ) p, x ∈ closure (interior (timeBox (p : ℝ) p)) :=
    fun x hx => VineEstS3.timeBox_subset_closure_interior p p hx
  have hKi : ∀ k', ‖kernelProt P.L P.γ P.δ LGi (cutHi .nil m H) (pullMult D.hp.ιi D.hp.βi S ω F M Fu Mu)
      (fun _ => t) s (fun _ => none) k' (fun _ => 0) 0‖ₑ ≤ ENNReal.ofReal bi := fun k' => by
    rw [cut_kernel_tree_m _ _ _ _ C.decI]
    have hc := FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGi (cutHi .nil m H) C.decI
      (pullMult D.hp.ιi D.hp.βi S ω F M Fu Mu) Bi hmiB k' (summable_coset_piece hHi hL1 k')
    refine (enorm_le_rn hθ0 (timeBoxGt_cl p) hc hts).trans ?_
    rw [hbi, ← piece_conv hL0 hrb _ _ c' ni gi _]
    exact tree_piece_star K hp (hle_n ni (by omega)) hθc inner LGi hwfi hni C.decI hli hlonei fI _ _ _ hGi
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) (cutHi .nil m H) (cutBi .nil m B) hHi k'
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKr : ∀ k', ‖kernelProt P.L P.γ P.δ LGr (cutHr .nil m inner (LG.garden.sig 0) H)
      (pullMult D.hp.ιr D.hp.βr S ω F M Fu Mu)
      (fun y => cupR m inner (LG.garden.sig 0) t s y.1.1) 0 (fun _ => none) k' (fun _ => 0) 0‖ₑ ≤
      ENNReal.ofReal br * ENNReal.ofReal (jbr k' ^ (30 * P.d))⁻¹ := fun k' => by
    rw [cut_kernel_couple_m _ _ _ _ C.decR]
    have hc := FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGr (cutHr .nil m inner (LG.garden.sig 0) H)
      C.decR.1.1 (pullMult D.hp.ιr D.hp.βr S ω F M Fu Mu) Br hmrB k' (summable_coset_piece hHr hL1 _)
    have hmem : (![cupR m inner (LG.garden.sig 0) t s 0, cupR m inner (LG.garden.sig 0) t s 1] : Fin 2 → ℝ) ∈
        timeBox (p : ℝ) p := by
      refine htsb _ ?_
      rcases cupR_cases m inner (LG.garden.sig 0) with h | h
      · exact Or.inl ⟨by simp [(h t s).1], by simp [(h t s).2]⟩
      · exact Or.inr ⟨by simp [(h t s).1], by simp [(h t s).2]⟩
    have h1 := enorm_le_rn hθ0 hBcl hc hmem
    refine le_mul_inv_of_weighted (hjpos _) ?_
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [hbr, ← piece_conv hL0 hrb _ _ c' nr gr _]
    exact couple_piece_star K hp (hle_n nr (by omega)) hθc Qr LGr hwfr hnr C.decR hlr fR _ _ _ hGr
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHr _
  have hKg : ∀ k', ‖kernelProt P.L P.γ P.δ LGg (cutHg .nil m inner (LG.garden.sig 0) H)
      (pullMult D.hp.ιg D.hp.βg S ω F M Fu Mu)
      (fun y => cupG m inner (LG.garden.sig 0) t s y.1.1) 0 (fun _ => none) k' (fun _ => 0) 0‖ₑ ≤
      ENNReal.ofReal bg * ENNReal.ofReal (jbr k' ^ (30 * P.d))⁻¹ := fun k' => by
    rw [cut_kernel_couple_m _ _ _ _ C.decG]
    have hc := FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg (cutHg .nil m inner (LG.garden.sig 0) H)
      C.decG.1.1 (pullMult D.hp.ιg D.hp.βg S ω F M Fu Mu) Bg hmgB k' (summable_coset_piece hHg hL1 _)
    have hmem : (![cupG m inner (LG.garden.sig 0) t s 0, cupG m inner (LG.garden.sig 0) t s 1] : Fin 2 → ℝ) ∈
        timeBox (p : ℝ) p := by
      refine htsb _ ?_
      rcases cupG_cases m inner (LG.garden.sig 0) with h | h
      · exact Or.inl ⟨by simp [(h t s).1], by simp [(h t s).2]⟩
      · exact Or.inr ⟨by simp [(h t s).1], by simp [(h t s).2]⟩
    have h1 := enorm_le_rn hθ0 hBcl hc hmem
    refine le_mul_inv_of_weighted (hjpos _) ?_
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [hbg, ← piece_conv hL0 hrb _ _ c' ng gg _]
    exact couple_piece_star K hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng C.decG hlg fG _ _ _ hGg
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHg _
  -- the exceptional sum
  have hc0n : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
      (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ)))‖ₑ =
      ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2) := by
    rw [← ofReal_norm, norm_cutPrefactor hL0 K.hδ]
  set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
  rw [enorm_mul, hc0n]
  refine (mul_le_mul' le_rfl enorm_tsum_le_tsum_enorm).trans ?_
  have hterm : ∀ e : PairE m P.d, ‖fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB (starA m P.L k e) *
        fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB (starB m P.L k e) * ((indB ind (starB m P.L k e) : ℝ) : ℂ) *
        (cutEps m e : ℂ) * (cutPh m (LG.garden.sig 0) P.L P.γ P.δ k s e t *
          (kernelProt P.L P.γ P.δ LGi (cutHi .nil m H) (pullMult D.hp.ιi D.hp.βi S ω F M Fu Mu) (fun _ => t) s
              (fun _ => none) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
            (kernelProt P.L P.γ P.δ LGr (cutHr .nil m inner (LG.garden.sig 0) H)
                (pullMult D.hp.ιr D.hp.βr S ω F M Fu Mu)
                (fun y => cupR m inner (LG.garden.sig 0) t s y.1.1) 0 (fun _ => none)
                (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
              kernelProt P.L P.γ P.δ LGg (cutHg .nil m inner (LG.garden.sig 0) H)
                (pullMult D.hp.ιg D.hp.βg S ω F M Fu Mu)
                (fun y => cupG m inner (LG.garden.sig 0) t s y.1.1) 0 (fun _ => none)
                (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0)))‖ₑ ≤
      ENNReal.ofReal Ca * (ENNReal.ofReal bi * (ENNReal.ofReal br * ENNReal.ofReal bg)) * (f e.1.2.1 * f e.1.2.2) :=
    fun e => by
      have hMe : ‖fD3' S ω F (fun _ => false) M Fu Mu D.hp.rootB (starA m P.L k e) *
          fD3' S ω F (fun _ => false) M Fu Mu D.hp.bB (starB m P.L k e) * ((indB ind (starB m P.L k e) : ℝ) : ℂ) *
            (cutEps m e : ℂ)‖ₑ ≤ ENNReal.ofReal Ca := by
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ((norm_mul_le _ _).trans ?_)
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) hCa0).trans (by rw [mul_one])
      have hph : ‖cutPh m (LG.garden.sig 0) P.L P.γ P.δ k s e t‖ₑ = 1 := by
        rw [← ofReal_norm, norm_cutPh, ENNReal.ofReal_one]
      calc _ ≤ ENNReal.ofReal Ca * (1 * (ENNReal.ofReal bi * ((ENNReal.ofReal br * f e.1.2.1) *
            (ENNReal.ofReal bg * f e.1.2.2)))) := by
            refine ((enorm_mul _ _).le).trans (mul_le_mul' hMe (((enorm_mul _ _).le).trans ?_))
            rw [hph]
            exact mul_le_mul' le_rfl (((enorm_mul _ _).le).trans (mul_le_mul' (hKi _) (((enorm_mul _ _).le).trans
              (mul_le_mul' (hKr _) (hKg _)))))
        _ = _ := by ring
  refine (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hterm)).trans ?_
  rw [ENNReal.tsum_mul_left]
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl ((tsum_pairE_le m f).trans
    (mul_le_mul' (tsum_decay_le hd1 hL1 k) (tsum_decay_le hd1 hL1 k))))).trans ?_
  -- the algebra
  have hlat0 : 0 ≤ latC P.d * P.L ^ P.d := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
  have hn1 : ni + nr + ng = n - 1 := by have : RegChain.nil.size = 0 := rfl; omega
  have hg : gi + gr + gg = protIncoh (cpair m Qr Qg inner) LG := (PairOnly.incoherency_of_chainIn C hch).symm
  have hleaf : leafSizeProduct LG B = leafSizeProduct LGi (cutBi .nil m B) *
      leafSizeProduct LGr (cutBr .nil m inner (LG.garden.sig 0) B) *
        leafSizeProduct LGg (cutBg .nil m inner (LG.garden.sig 0) B) := by
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
  rw [← ENNReal.ofReal_mul hr0, ← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul hCa0, ← ENNReal.ofReal_mul hlat0,
    ← ENNReal.ofReal_mul (mul_nonneg hCa0 (mul_nonneg hi0 (mul_nonneg hr0 hg0))),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [hcost]
  linear_combination (coupling P.d P.L P.γ P.δ ^ 2 * Ca * (latC P.d * P.L ^ P.d) ^ 2) * hprod

end WaveTurbulence.Flower.ProtPin
