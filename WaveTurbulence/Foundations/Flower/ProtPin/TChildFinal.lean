/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildPerkG
public import WaveTurbulence.Foundations.Flower.ProtPin.FinalTwo

/-! # D3 PROT-PIN (P7): `termChild` for protected paired trees in `X^{θ,30d,0}`, given the root-trace bound

`tc_termChild_final_of`: the configuration `termChild i` of `ProtBoundAt` for trees at the weight `θ = η`
(`PieceLoss P θ 0`, `c ≥ 31d + 6`), from the uniform root-trace bound `TcTraceU θ Ct` of side couples.
`ProtCfg.Valid (termChild i)` puts a branch of layer `p` at the child `i ≠ lone` of the terminal node, i.e. at the
bottom tree of the red (`i = m.red.2`) or the green (`i = m.green.2`) side couple; the per-output bounds
`tc_perk_red`/`tc_perk_green` and `final_two` (two cuts, `a = 1`) conclude. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem tc_rBase_bot (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    ∃ j, rBase m inner ζ j = bPath m inner ++ [m.red.2] := by
  by_cases hs : slotSign ζ m.red.1 = 1
  · exact ⟨1, by simp [rBase, hs]⟩
  · exact ⟨0, by simp [rBase, hs]⟩

theorem tc_gBase_bot (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    ∃ j, gBase m inner ζ j = bPath m inner ++ [m.green.2] := by
  by_cases hs : slotSign ζ m.green.1 = 1
  · exact ⟨1, by simp [gBase, hs]⟩
  · exact ⟨0, by simp [gBase, hs]⟩

theorem tc_gBase_ne (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) :
    gBase m inner ζ j ≠ bPath m inner ++ [m.red.2] := by
  rcases gBase_cases m inner ζ j with h | h <;> rw [h] <;> intro h'
  · have := congrArg List.length h'
    simp [bPath] at this
  · have h2 := List.append_cancel_left h'
    simp only [List.cons.injEq, and_true] at h2
    exact red2_ne_green2 m h2.symm

theorem tc_rBase_ne (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) :
    rBase m inner ζ j ≠ bPath m inner ++ [m.green.2] := by
  rcases rBase_cases m inner ζ j with h | h <;> rw [h] <;> intro h'
  · have := congrArg List.length h'
    simp [bPath] at this
  · have h2 := List.append_cancel_left h'
    simp only [List.cons.injEq, and_true] at h2
    exact red2_ne_green2 m h2

/-- **(P7) for protected paired trees in `X^{θ,30d,0}`**, given the root-trace bound of side couples. -/
theorem tc_termChild_final_of {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {Ct : ℝ} (_hCt : 0 ≤ Ct) (_hT : TcTraceU θ Ct) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
      (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c CL : ℝ} (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c)
      (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig2 : twoK CL (Cr * Ct * 2) P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 1) (X : RegChain)
      (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n) (_hamb : TreeAmb p X LG) (i : Fin 3)
      (_hval : (ProtCfg.termChild i).Valid X LG p) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t)
      (_htp : t < p + 1) (q' : ℕ)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator X ind)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 ((ProtCfg.termChild i).box X t p q') (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) ((ProtCfg.termChild i).fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
          ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨Cw, hCw, hred⟩ := tc_perk_red hθ0 hθ1
  obtain ⟨Cg, hCg, hgreen⟩ := tc_perk_green hθ0 hθ1
  set Cm : ℝ≥0∞ := max Cw Cg with hCm
  have hCmf : Cm < ⊤ := max_lt hCw hCg
  refine ⟨Cm.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ct hCt hT P C₁a C₂a C₁b C₂b K c CL hθc hc hCL hC11 hLOE hbig2 p hp n hn LG X hsh hsz hamb i hval s t hps hst
    htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := by linarith
  obtain ⟨hne, hlast, b, hb0, hbp, hbl⟩ := hval
  obtain ⟨Xp, m, Qr, Qg, inner, rfl, LGp, LGi, LGr, LGg, D⟩ := cutTerm_pieces hsh hne
  have hsz' : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n := hsz
  have hlp : (appendChain Xp (cpair m Qr Qg inner)).lonePath = Xp.lonePath ++ (bPath m inner ++ [m.lone]) := by
    rw [appendChain_lonePath, cpair_lonePath]; rfl
  have hi : i ≠ m.lone := by
    intro h
    apply hlast
    rw [hlp, h]
    simp
  have hdrop : (appendChain Xp (cpair m Qr Qg inner)).lonePath.dropLast = Xp.lonePath ++ bPath m inner := by
    rw [hlp, ← List.append_assoc, List.dropLast_concat]
  have hbpath : b.1.2 = Xp.lonePath ++ (bPath m inner ++ [i]) := by rw [hbp, hdrop, List.append_assoc]
  have hbb : Xp.lonePath ++ (bPath m inner ++ [i]) ∈ (LG.garden.tree 0).branching := by
    have h2 := b.2
    rw [show b.1.1 = 0 from Subsingleton.elim _ _, hbpath] at h2
    exact h2
  have hbL : layerAt LG ((0 : Fin 1), Xp.lonePath ++ (bPath m inner ++ [i])) = p := by
    have h1 := layerAt_node LG b.toNode
    rw [hbl] at h1
    rw [← h1]
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) hbpath.symm
  have hSM : StarMult P.L LG (appendChain Xp (cpair m Qr Qg inner))
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) (starCost S cω) :=
    starMult_tree S ω cω hpres F M hM Fu Mu hMu ind hind
  have hn2 : 2 ≤ n := by
    obtain ⟨np, ni, nr, ng, -, -, hnr, hng, hnsum⟩ := cut_sizes hsz'
    rcases tc_child_cases m i hi with hr | hg
    · obtain ⟨j, hj⟩ := tc_rBase_bot m inner (LG.garden.sig 0)
      rw [← hr] at hj
      have := tc_size_pos (cut_wf D hsh.1).2.2.1 D.decR (tc_red_root_branch D hj hbb) hnr
      omega
    · obtain ⟨j, hj⟩ := tc_gBase_bot m inner (LG.garden.sig 0)
      rw [← hg] at hj
      have := tc_size_pos (cut_wf D hsh.1).2.2.2 D.decG (tc_green_root_branch D hj hbb) hng
      omega
  -- the per-output bound in the form of `final_two`
  set Cr' : ℝ := Cm.toReal * Ct * 2 with hCr'
  have hCr'0 : 0 ≤ Cr' := mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hCt) (by norm_num)
  have hleaf0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS0 := starCost_nonneg' S cω
  have hperk : ∀ k, rn θ ((ProtCfg.termChild i).box (appendChain Xp (cpair m Qr Qg inner)) t p q')
      (fun ts => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k
        (fun _ => 0) 0) ≤
      ENNReal.ofReal (Cr' * twoRb P 1 n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
        (leafSizeProduct LG B) (starCost S cω)) := by
    intro k
    have hsp : s < p + 1 := hst.trans htp
    have hbase : ∀ C : ℝ≥0∞, C ≤ Cm →
        C * ENNReal.ofReal (Ct * (P.L * (2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
          (P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
            leafSizeProduct LG B * starCost S cω))) ≤
        ENNReal.ofReal (Cr' * twoRb P 1 n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
          (leafSizeProduct LG B) (starCost S cω)) := by
      intro C hC
      have hrb := rb_nonneg hC1 K.hδ hL0 (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
      have hX0 : 0 ≤ Ct * (P.L * (2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
          (P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
            leafSizeProduct LG B * starCost S cω)) := by
        positivity
      refine (mul_le_mul' hC le_rfl).trans ?_
      rw [mul_ofReal_toReal hCmf hX0]
      refine ENNReal.ofReal_le_ofReal ?_
      unfold twoRb
      rw [hCr', Real.rpow_one]
      have hC56 : P.C₁ ^ 5 ≤ P.C₁ ^ 6 := pow_le_pow_right₀ hC11 (by norm_num)
      have hY : 0 ≤ Cm.toReal * Ct * 2 * P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
          rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) * leafSizeProduct LG B *
            starCost S cω := by
        have := (ENNReal.toReal_nonneg : 0 ≤ Cm.toReal)
        positivity
      calc Cm.toReal * (Ct * (P.L * (2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
            (P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
              leafSizeProduct LG B * starCost S cω)))
          = (Cm.toReal * Ct * 2 * P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
              rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) * leafSizeProduct LG B *
                starCost S cω) * P.C₁ ^ 5 := by ring
        _ ≤ (Cm.toReal * Ct * 2 * P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
              rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) * leafSizeProduct LG B *
                starCost S cω) * P.C₁ ^ 6 := mul_le_mul_of_nonneg_left hC56 hY
        _ = _ := by ring
    rw [box_termChild]
    rcases tc_child_cases m i hi with hr | hg
    · obtain ⟨j, hj⟩ := tc_rBase_bot m inner (LG.garden.sig 0)
      rw [← hr] at hj
      have hgn : ∀ j', gBase m inner (LG.garden.sig 0) j' ≠ bPath m inner ++ [i] := fun j' => by
        rw [hr]; exact tc_gBase_ne m inner _ j'
      exact (hred hCt hT K hθc hp hn D hsh hsz' hamb i j hj hgn hbb hbL hps hsp t q' H B hH
        _ _ hSM k).trans (hbase Cw (le_max_left _ _))
    · obtain ⟨j, hj⟩ := tc_gBase_bot m inner (LG.garden.sig 0)
      rw [← hg] at hj
      have hrn : ∀ j', rBase m inner (LG.garden.sig 0) j' ≠ bPath m inner ++ [i] := fun j' => by
        rw [hg]; exact tc_rBase_ne m inner _ j'
      exact (hgreen hCt hT K hθc hp hn D hsh hsz' hamb i j hj hrn hbb hbL hps hsp t q' H B
        hH _ _ hSM k).trans (hbase Cg (le_max_right _ _))
  rw [prod_ofReal_starCost]
  exact final_two K.hL K.hδ hC1 hCr'0 hCL le_rfl hc hLOE hbig2 _ b₀ c₀ _ hn2 hleaf0 hCS0 hperk

end WaveTurbulence.Flower.ProtPin
