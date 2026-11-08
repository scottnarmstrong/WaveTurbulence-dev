/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TreeFinals
public import WaveTurbulence.Foundations.Flower.ProtPin.Pen5
public import WaveTurbulence.Foundations.Flower.ProtPin.PenRoot
public import WaveTurbulence.Foundations.Flower.ProtPin.NTGate

/-! # D3 PROT-PIN: slices of `ProtBoundAt` at the weight `θ = η`

`CfgU θ Cr sel` is `ProtBoundAt` at `(θ, c) = (η, 31d+6)` for the objects and configurations selected by `sel`, given
the prefix facts (`AlphaConsts`, `1 ≤ C₁`, `LocalOutputExtension`, the one- and two-cut size conditions with the
constant `Cr`). Every configuration other than `none`/`term` is needed only at this weight. The tree slices proved
here: `root` (P1), `rootTerm` (P2/P3), `trace` (P8, nonempty chain), `penTerm` with an empty prefix or a nonempty
interior (P4 root-pinned, P5). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- A slice of `ProtBoundAt` at `θ = η`. -/
def CfgU (θ Cr : ℝ) (sel : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hη : P.η = θ) {CL : ℝ}
    (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
    (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    (_hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ)),
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (cfg : ProtCfg), cfg.Valid X LG p → ProtAmbient p X LG → sel w LG X cfg →
  ∀ (s t : ℝ), (p : ℝ) < s → s < t → t < p + 1 → ∀ q' : ℕ, q' ≤ p →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    ((cfg = .none ∨ cfg = .root ∨ cfg = .trace) → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr θ (30 * P.d) 0 (cfg.box X t p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
        regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B)

theorem termK_mono {CL Cr Cr' : ℝ} (hCL : 0 ≤ CL) (h : Cr ≤ Cr') (d : ℕ) : termK CL Cr d ≤ termK CL Cr' d := by
  unfold termK
  have := latC_nonneg d
  gcongr

theorem twoK_mono {CL Cr Cr' : ℝ} (hCL : 0 ≤ CL) (h : Cr ≤ Cr') (d : ℕ) : twoK CL Cr d ≤ twoK CL Cr' d := by
  unfold twoK
  have := latC_nonneg d
  gcongr

/-- The size conditions pass to a smaller constant. -/
theorem big_mono {P : WTParams} {CL Cr Cr' : ℝ} (hCL : 0 ≤ CL) (h : Cr ≤ Cr') (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L)
    (hbig : termK CL Cr' P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ)) :
    termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ) := by
  refine le_trans ?_ hbig
  have h1 := termK_mono hCL h P.d
  have h2 : 0 ≤ P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) := by
    have := Real.rpow_nonneg hL (2 * P.γ)
    positivity
  calc termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) = termK CL Cr P.d * (P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ)) := by
        ring
    _ ≤ termK CL Cr' P.d * (P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ)) := mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

theorem big2_mono {P : WTParams} {CL Cr Cr' : ℝ} (hCL : 0 ≤ CL) (h : Cr ≤ Cr') (hL : 0 ≤ P.L)
    (hbig2 : twoK CL Cr' P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ)) :
    twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ) := by
  refine le_trans ?_ hbig2
  have h1 := twoK_mono hCL h P.d
  have h2 : 0 ≤ P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) := by
    have := Real.rpow_nonneg hL (4 * P.γ)
    positivity
  calc twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) = twoK CL Cr P.d * (P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ)) := by
        ring
    _ ≤ twoK CL Cr' P.d * (P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ)) := mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

theorem CfgU.mono {θ Cr Cr' : ℝ} {sel : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop}
    (h : CfgU θ Cr sel) (hle : Cr ≤ Cr') : CfgU θ Cr' sel := by
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  exact h K hη hCL hC11 hLOE (big_mono hCL hle K.hδ hL0 hbig) (big2_mono hCL hle hL0 hbig2)

theorem CfgU.or {θ Cr : ℝ} {sel₁ sel₂ : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop}
    (h₁ : CfgU θ Cr sel₁) (h₂ : CfgU θ Cr sel₂) : CfgU θ Cr (fun w LG X cfg => sel₁ w LG X cfg ∨ sel₂ w LG X cfg) := by
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel
  rcases hsel with h | h
  · exact h₁ K hη hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb h
  · exact h₂ K hη hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb h

theorem pieceLoss_eta {P : WTParams} {θ : ℝ} (hη : P.η = θ) : PieceLoss P θ 0 := Or.inl ⟨hη.symm, rfl⟩

/-! ### Tree slices -/

/-- **(P1), trees.** -/
theorem cfgU_root_tree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ _ cfg => w = 1 ∧ cfg = .root) := by
  obtain ⟨Cr1, h1, hf1⟩ := root_final_pair hθ0 hθ1
  obtain ⟨Cr2, h2, hf2⟩ := root_final_rest hθ0 hθ1
  refine ⟨Cr1 + Cr2, by linarith, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel s t hps hst
    htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl⟩ := hsel
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hθc := pieceLoss_eta hη
  have hc : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ 31 * P.d + 6 := by linarith
  have hi1 := hind1 (Or.inr (Or.inl rfl))
  have hne : X.lonePath ≠ [] := hval
  cases X with
  | nil => exact absurd rfl hne
  | pair m Qr Qg inner rest =>
    by_cases hrest : rest = .nil
    · subst hrest
      obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG .nil m Qr Qg inner hsh.2.1 hsh.1
      exact hf1 K hθc le_rfl hc hCL hC11 hLOE (big_mono hCL (by linarith) K.hδ hL0 hbig) hp hn C hsh hsz
        (treeAmb_of_protAmbient hamb) (hps.trans hst) htp s q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
    · obtain ⟨LGZ, LGi, LGs, LGr, LGg, D⟩ := RootData.exists_of_wf LG m Qr Qg inner rest hsh.2.1 hsh.1 hrest
      exact hf2 K hθc hc hCL hLOE (big_mono hCL (by linarith) K.hδ hL0 hbig) hp hn D hsh hsz
        (treeAmb_of_protAmbient hamb) (hps.trans hst) htp s q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hi1 b₀ c₀

/-- **(P8), trees with a nonempty chain.** -/
theorem cfgU_trace_tree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ X cfg => w = 1 ∧ cfg = .trace ∧ X ≠ .nil) := by
  obtain ⟨Cr1, h1, hf1⟩ := trace_final_pair hθ0 hθ1
  obtain ⟨Cr2, h2, hf2⟩ := trace_final_rest hθ0 hθ1
  refine ⟨Cr1 + Cr2, by linarith, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel s t hps hst
    htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl, hX⟩ := hsel
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hθc := pieceLoss_eta hη
  have hc : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ 31 * P.d + 6 := by linarith
  have hi1 := hind1 (Or.inr (Or.inr rfl))
  cases X with
  | nil => exact absurd rfl hX
  | pair m Qr Qg inner rest =>
    by_cases hrest : rest = .nil
    · subst hrest
      obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG .nil m Qr Qg inner hsh.2.1 hsh.1
      exact hf1 K hθc le_rfl hc hCL hC11 hLOE (big_mono hCL (by linarith) K.hδ hL0 hbig) hp hn C hsh hsz
        (treeAmb_of_protAmbient hamb) s t q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
    · obtain ⟨LGZ, LGi, LGs, LGr, LGg, D⟩ := RootData.exists_of_wf LG m Qr Qg inner rest hsh.2.1 hsh.1 hrest
      exact hf2 K hθc hc hCL hLOE (big_mono hCL (by linarith) K.hδ hL0 hbig) hp hn D hsh hsz
        (treeAmb_of_protAmbient hamb) s t q' hq' H B hH S ω cω hpres F M hM Fu Mu hMu ind hi1 b₀ c₀

/-- **(P2)/(P3), trees.** -/
theorem cfgU_rootTerm_tree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ _ cfg => w = 1 ∧ cfg = .rootTerm) := by
  obtain ⟨Cr2, h2, hf2⟩ := p3_final hθ0 hθ1
  set Cr1 : ℝ := (cutNormR θ 2).toReal with hCr1
  have h1 : 0 ≤ Cr1 := ENNReal.toReal_nonneg
  refine ⟨Cr1 + Cr2, by linarith, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel s t hps hst
    htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl⟩ := hsel
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hθc := pieceLoss_eta hη
  have hc : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ 31 * P.d + 6 := by linarith
  have hθ0' : 0 ≤ θ := hθ0
  have hlen : 2 ≤ X.lonePath.length := hval
  cases X with
  | nil => simp [RegChain.lonePath] at hlen
  | pair m Qr Qg inner rest =>
    by_cases hrest : rest = .nil
    · subst hrest
      obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG .nil m Qr Qg inner hsh.2.1 hsh.1
      exact rootTerm_final hθ0' K hθc le_rfl hc hCL hC11 hLOE (big_mono hCL (by linarith) K.hδ hL0 hbig) hp hn C
        hsh hsz (treeAmb_of_protAmbient hamb) hps hst htp q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
    · obtain ⟨LGZ, LGi, LGs, LGr, LGg, D⟩ := RootData.exists_of_wf LG m Qr Qg inner rest hsh.2.1 hsh.1 hrest
      exact hf2 K hθc (by linarith) hCL hLOE (big2_mono hCL (by linarith) hL0 hbig2) hp hn D hsh hsz
        (treeAmb_of_protAmbient hamb) hps hst htp q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀

end WaveTurbulence.Flower.ProtPin
