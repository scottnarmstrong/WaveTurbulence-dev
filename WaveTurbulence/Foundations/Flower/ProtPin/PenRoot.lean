/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootPair

/-! # D3 PROT-PIN: (P4) with the root pinned — `penTerm` on a one-pair chain with an empty interior

For `X = pair m Qr Qg nil nil` the penultimate chain node is the root `𝔫_a` and the terminal node is `𝔫_b`; `penTerm`
pins both at `s`, which is `rootTerm` with `t := s` (`pen_fix_eq`). On the R176 box (`t ≤ ts 0`, so `s ≤ ts 0`) the kernel
is the constant `Σ'_e c_e W_e(s, s)` of `pair_pack`, bounded pointwise at the diagonal point `(s, s)` (in the closure of
the open triangle: `pen_enorm_le_rn_closure`); `pen_final_root` closes it with `final_pair` (one cut). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **Pointwise bound on the closure** of a set whose points are limits of interior points. -/
theorem pen_enorm_le_rn_closure {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)}
    (hB : ∀ t ∈ B, t ∈ closure (interior B)) {f : (Fin r → ℝ) → ℂ} (hf : Continuous f) {x : Fin r → ℝ}
    (hx : x ∈ closure B) : ‖f x‖ₑ ≤ rn θ B f := by
  by_cases htop : rn θ B f = ⊤
  · rw [htop]; exact le_top
  have hfin : rn θ B f < ⊤ := lt_top_iff_ne_top.mpr htop
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨g, hgc, hgag, -, hgle⟩ := exists_cont_ext hθ hB hf hfin (ε := (ε : ℝ≥0∞))
    (by exact_mod_cast hε) ENNReal.coe_ne_top
  have hEq : Set.EqOn g f (closure B) := Set.EqOn.closure (fun t ht => hgag t ht) hgc hf
  rw [← hEq hx]
  exact (Regref.enorm_le_timeFourierNorm_at hθ g x hgc.continuousAt).trans hgle

/-- The diagonal point `(s, s)` lies in the closure of the open triangle. -/
theorem pen_diag_mem_closure {p s : ℝ} (hps : p ≤ s) (hsp : s < p + 1) :
    (![s, s] : Fin 2 → ℝ) ∈ closure (timeBoxGt p p) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min (ε / 2) ((p + 1 - s) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ (p + 1 - s) / 2 := min_le_right _ _
  refine ⟨![s + δ, s], ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · refine lt_of_le_of_lt ((dist_pi_le_iff hδ0.le).2 fun i => ?_) (by linarith)
    fin_cases i <;> simp [Real.dist_eq, abs_of_pos hδ0, hδ0.le]

/-- `penTerm` on `pair m Qr Qg nil nil` is `rootTerm` with the root at `s`. -/
theorem pen_fix_eq (m : MiniTreeCode) (Qr Qg : RegCpl) (s t up : ℝ) {T : Fin 1 → TTree} :
    (ProtCfg.penTerm.fix (appendChain .nil (cpair m Qr Qg .nil)) s t up : GBranch T → Option ℝ) =
      ProtCfg.rootTerm.fix (cpair m Qr Qg .nil) s s up := by
  have hl : (appendChain .nil (cpair m Qr Qg .nil)).lonePath = [m.c, m.lone] := by
    show (cpair m Qr Qg .nil).lonePath = _
    rw [cpair_lonePath]
    simp [lonePos, bPath, RegChain.lonePath]
  have hl' : (cpair m Qr Qg .nil).lonePath = [m.c, m.lone] := hl
  funext b
  unfold ProtCfg.fix ProtCfg.pins
  rw [hl, hl']
  simp

theorem pen_pinsRoot (m : MiniTreeCode) (Qr Qg : RegCpl) :
    ProtCfg.penTerm.pinsRoot (appendChain .nil (cpair m Qr Qg .nil)) = true := by
  have hl : (appendChain .nil (cpair m Qr Qg .nil)).lonePath = [m.c, m.lone] := by
    show (cpair m Qr Qg .nil).lonePath = _
    rw [cpair_lonePath]
    simp [lonePos, bPath, RegChain.lonePath]
  unfold ProtCfg.pinsRoot
  rw [hl]
  rfl

/-- **(P4) with the root pinned, one output.** -/
theorem pen_perk_root {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      (_C : CutTermData LG .nil m Qr Qg .nil LGp LGi LGr LGg)
      (_hsh : ProtShape p (cpair m Qr Qg .nil) LG) (_hsz : (cpair m Qr Qg .nil).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg .nil) LG) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t)
      (_htp : t < p + 1) (q' : ℕ)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator (cpair m Qr Qg .nil) ind)
      (k : Mom P.d),
      rn θ (ProtCfg.penTerm.box (appendChain .nil (cpair m Qr Qg .nil)) t p q') (fun ts =>
          kernelProt P.L P.γ P.δ LG H
            (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
              filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
            (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain .nil (cpair m Qr Qg .nil)) s t (ts 0)) k
            (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (pairRb P c' n (protIncoh (cpair m Qr Qg .nil) LG) (leafSizeProduct LG B)
          (starCost S cω)) := by
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨T4 * cutNormR θ 2, ENNReal.mul_lt_top hT4f (cutNormR_lt_top θ 2), ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGp LGi LGr LGg m Qr Qg C hsh hsz hamb s t hps hst htp q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  obtain ⟨c, A, W, hWc, -, hsum, -, hrt⟩ := pair_pack hθ0 K hθc hp hn C hsh hsz hamb H B hH S ω cω hpres
    F M hM Fu Mu hMu ind hind k
  set V : ℂ := ∑' e, c e * (rootPh (A e) s s * W e ![s, s]) with hV
  have hconst : ∀ ts ∈ ProtCfg.penTerm.box (appendChain .nil (cpair m Qr Qg .nil)) t p q',
      kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain .nil (cpair m Qr Qg .nil)) s t (ts 0)) k
          (fun _ => 0) 0 = V := by
    intro ts hts
    rw [box_of_pinsRoot (pen_pinsRoot m Qr Qg)] at hts
    rw [pen_fix_eq]
    exact hrt (ts 0) (ts 1) s s (by linarith [hts.2]) (by linarith [hts.2])
  rw [rn_congr θ hconst, box_of_pinsRoot (pen_pinsRoot m Qr Qg)]
  refine (rn_const_le θ ![(p : ℝ), (q' : ℝ)] (rootBox_sub_cell (p : ℝ) q' t) V).trans ?_
  have hVb : ‖V‖ₑ ≤ ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e) := by
    refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun e => ?_)
    rw [enorm_mul, enorm_mul, ← ofReal_norm (rootPh _ _ _), norm_rootPh, ENNReal.ofReal_one, one_mul]
    exact mul_le_mul' le_rfl (pen_enorm_le_rn_closure hθ0 (timeBoxGt_cl p) (hWc e)
      (pen_diag_mem_closure hps.le (hst.trans htp)))
  calc ‖V‖ₑ * cutNormR θ 2 ≤ (T4 * ENNReal.ofReal (pairRb P c' n (protIncoh (cpair m Qr Qg .nil) LG)
        (leafSizeProduct LG B) (starCost S cω))) * cutNormR θ 2 := mul_le_mul' (hVb.trans hsum) le_rfl
    _ = _ := by ring

/-- **(P4) with the root pinned, for one-pair protected trees, in `X^{θ,30d,0}`** (R176 box; stars, filters,
dagger; the weight `θ = η`). -/
theorem pen_final_root {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c CL : ℝ}
      (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c) (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      (_D : CutTermData LG .nil m Qr Qg .nil LGp LGi LGr LGg)
      (_hsh : ProtShape p (appendChain .nil (cpair m Qr Qg .nil)) LG)
      (_hsz : protSize (appendChain .nil (cpair m Qr Qg .nil)) LG = 2 * n)
      (_hamb : ProtAmbient p (appendChain .nil (cpair m Qr Qg .nil)) LG)
      {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t) (_htp : t < p + 1) (q' : ℕ)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain .nil (cpair m Qr Qg .nil)) ind)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.penTerm.box (appendChain .nil (cpair m Qr Qg .nil)) t p q')
        (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain .nil (cpair m Qr Qg .nil)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (protIncoh (appendChain .nil (cpair m Qr Qg .nil)) LG) *
            ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C, hC, hperk⟩ := pen_perk_root hθ0
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c CL hθc hc hCL hC11 hLOE hbig p hp n hn LG LGp LGi LGr LGg m Qr Qg D hsh hsz hamb
    s t hps hst htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hsz' : (cpair m Qr Qg .nil).size = 2 * n := hsz
  have hn1 : 1 ≤ n := by
    obtain ⟨_, _, _, _, -, -, -, -, h⟩ := cut_sizes (Xp := .nil) hsz'
    omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hc' : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ c := by linarith
  rw [prod_ofReal_starCost]
  refine final_pair (c' := 0) K.hL K.hδ hC11 ENNReal.toReal_nonneg hCL le_rfl hc' hLOE hbig _ b₀ c₀ _ hn1 hleaf
    (starCost_nonneg' S cω) fun k => ?_
  rw [← mul_ofReal_toReal hC (pairRb_nonneg (by linarith) K.hδ hL0 _ _ hleaf (starCost_nonneg' S cω))]
  exact hperk K hθc hp hn D hsh hsz' (treeAmb_of_protAmbient hamb) hps hst htp q' H B hH S ω cω hpres
    F M hM Fu Mu hMu ind hind k

end WaveTurbulence.Flower.ProtPin
