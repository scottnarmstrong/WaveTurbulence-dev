/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.TreeFinal

/-! # RT-GATE (i): clause (i) of `RootTraceBoundAt` on one lattice ball (`rt_tree_ball`)

From the per-output bound `rt_tree_perk` (`Cr · termRb(g')`), D3's `final_term` (the local output extension at
`L^{31d}`, the one-cut size condition `hbig`) gives `L^{47d+4} · regBound(n, g')`; the closing link, if lost
(`g' = g − 1`), costs `L` (`rb_pred_le`): `L^{47d+5} · regBound(n, g)`, the exponent of `RootTraceBoundAt`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin

/-- A link lost from the incoherency costs at most `L`. -/
theorem rt_regBound_le {P : WTParams} (hL : 1 ≤ P.L) (hC1 : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hη : 0 ≤ P.η) (n : ℕ)
    {g g' : ℕ} (h1 : g' ≤ g) (h2 : g ≤ g' + 1) : regBound P n g' ≤ ENNReal.ofReal P.L * regBound P n g := by
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  rw [regBound_eq_rb, regBound_eq_rb, ← ENNReal.ofReal_mul hL0]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · rw [h]; exact le_mul_of_one_le_left (rb_nonneg hC1 hδ hL0 n g) hL
  · have hg : g' = g - 1 := by omega
    rw [hg]
    have := rb_pred_le hL hC1 hδ hη n (show 1 ≤ g by omega)
    rwa [Real.rpow_one] at this

/-- **Clause (i) on one lattice ball** (given the prefix facts). -/
theorem rt_tree_ball {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P)
      (_hθc : PieceLoss P θ 0) (_hC11 : 1 ≤ P.C₁) {CL : ℝ} (_hCL : 0 ≤ CL)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (X : RegChain) (LG : LayeredGarden 1) (_hwf : X.wf = true) (_hsz : X.size = 2 * n)
      (_hdec : X.DecodesTree LG.garden) (_hne : X.lonePath ≠ []) (_hle : ∀ a, LG.layer a ≤ p)
      (_hroot : LG.layer (GNode.root LG.garden.tree 0) = p) {q' : ℕ}
      (_hlone : ∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') (_hamb : ProtAmbient p X LG)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (timeBoxGt p q' ∩ {ts | ts 1 < s ∧ s ≤ ts 0}) (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
          (fun _ => ts 0) (ts 1) (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 5)) *
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) * ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨Cr, hCr, hperk⟩ := rt_tree_perk hθ0 hθ1
  refine ⟨Cr, hCr, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hθc hC11 CL hCL hLOE hbig p hp n hn s hps hsp X LG hwf hsz hdec hne hle hroot q'
    hlone hamb S ω cω hpres H B hH b₀ c₀
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  obtain ⟨hn1, g', hg1, hg2, hk⟩ := hperk K hFC hθc hC11 hp hn hps hsp X LG hwf hsz hdec hne hle hroot hlone hamb
    S ω cω hpres H B hH
  have hd0 : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
  have hfin := final_term (c := 47 * (P.d : ℝ) + 4) (c' := 0) hL1 K.hδ hC1 hCr hCL (by linarith) hLOE hbig
    (rtBox p q' s) b₀ c₀ _ hn1 hleaf hCS hk
  refine hfin.trans ?_
  rw [prod_ofReal_starCost]
  have hrb := rt_regBound_le hL1 hC1 K.hδ K.hη0 n hg1 hg2
  have hpow : ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 4)) * ENNReal.ofReal P.L =
      ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 5)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hL0 _)]
    congr 1
    rw [show (47 * (P.d : ℝ) + 5) = (47 * P.d + 4) + 1 by ring,
      Real.rpow_add (by linarith : (0 : ℝ) < P.L) (47 * (P.d : ℝ) + 4) 1, Real.rpow_one]
  calc ENNReal.ofReal (starCost S cω) * ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 4)) * regBound P n g' *
        ENNReal.ofReal (leafSizeProduct LG B)
      ≤ ENNReal.ofReal (starCost S cω) * ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 4)) *
          (ENNReal.ofReal P.L * regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0)))) *
            ENNReal.ofReal (leafSizeProduct LG B) := mul_le_mul' (mul_le_mul' le_rfl hrb) le_rfl
    _ = _ := by rw [← hpow]; ring

end WaveTurbulence.Flower.ProtRT
