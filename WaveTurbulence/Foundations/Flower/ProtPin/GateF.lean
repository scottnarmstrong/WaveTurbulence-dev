/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.GateAll
public import WaveTurbulence.Foundations.Flower.FiltCoh.GateD5

/-! # D3 PROT-PIN: slices with FILT-COH's multi-layer coherent gate

`CfgUF θ Cr sel` is `CfgU θ Cr sel` with one more prefix fact: FILT-COH's `FiltCoherentBoundAt` (coherent couples and
trees whose two parents may lie in different layers, `q' ≤ q`), with a constant `C₁c ≤ C₁`; the prefix supplies it from
the unconditional `FiltCoh.filtCoherentBoundGate`. Needed by (P7) (sub-couples of the root-traced side couple whose
parents lie in two layers). Every `CfgU` slice is a `CfgUF` slice (`CfgU.toF`); `protBoundGate_ofF` is the gate
assembly with this prefix. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- A slice of `ProtBoundAt` at `θ = η`, given also FILT-COH's multi-layer coherent gate. -/
def CfgUF (θ Cr : ℝ) (sel : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b C₁c C₂c : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b)
    (_hFC : FiltCoherentBoundAt { P with C₁ := C₁c, C₂ := C₂c }) (_hc0 : 0 ≤ C₁c) (_hcle : C₁c ≤ P.C₁)
    (_hη : P.η = θ) {CL : ℝ}
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


theorem CfgU.toF {θ Cr : ℝ} {sel : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop} (h : CfgU θ Cr sel) :
    CfgUF θ Cr sel := by
  intro P C₁a C₂a C₁b C₂b C₁c C₂c K _ _ _ hη CL hCL hC11 hLOE hbig hbig2
  exact h K hη hCL hC11 hLOE hbig hbig2

theorem CfgUF.mono {θ Cr Cr' : ℝ} {sel : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop}
    (h : CfgUF θ Cr sel) (hle : Cr ≤ Cr') : CfgUF θ Cr' sel := by
  intro P C₁a C₂a C₁b C₂b C₁c C₂c K hFC hc0 hcle hη CL hCL hC11 hLOE hbig hbig2
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  exact h K hFC hc0 hcle hη hCL hC11 hLOE (big_mono hCL hle K.hδ hL0 hbig) (big2_mono hCL hle hL0 hbig2)

theorem CfgUF.or {θ Cr : ℝ} {sel₁ sel₂ : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop}
    (h₁ : CfgUF θ Cr sel₁) (h₂ : CfgUF θ Cr sel₂) :
    CfgUF θ Cr (fun w LG X cfg => sel₁ w LG X cfg ∨ sel₂ w LG X cfg) := by
  intro P C₁a C₂a C₁b C₂b C₁c C₂c K hFC hc0 hcle hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval
    hamb hsel
  rcases hsel with h | h
  · exact h₁ K hFC hc0 hcle hη hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb h
  · exact h₂ K hFC hc0 hcle hη hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb h

theorem CfgUF.weaken {θ Cr : ℝ} {sel sel' : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop}
    (h : CfgUF θ Cr sel)
    (himp : ∀ (p : ℕ) (w : ℕ) (LG : LayeredGarden w) (X : RegChain) (cfg : ProtCfg), ProtShape p X LG →
      cfg.Valid X LG p → sel' w LG X cfg → sel w LG X cfg) : CfgUF θ Cr sel' := by
  intro P C₁a C₂a C₁b C₂b C₁c C₂c K hFC hc0 hcle hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval
    hamb hsel
  exact h K hFC hc0 hcle hη hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb
    (himp p w LG X cfg hsh hval hsel)

/-- **`ProtBoundAt` from `none`/`term` and the rest**, with the multi-layer coherent gate. -/
theorem protBoundAt_ofF {P : WTParams} {C₁a C₂a C₁b C₂b C₁c C₂c : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    (hFC : FiltCoherentBoundAt { P with C₁ := C₁c, C₂ := C₂c }) (hc0 : 0 ≤ C₁c) (hcle : C₁c ≤ P.C₁)
    (hNT : ProtBoundNTAt P) {Cr CL : ℝ} (hCL : 0 ≤ CL) (hC11 : 1 ≤ P.C₁)
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr P.η B {k} F ≤ X) →
      XNormRestr P.η (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    (hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
    (hU : CfgUF P.η Cr selRest) : ProtBoundAt P := by
  intro p hp n hn w LG X hsh hsz cfg hval hamb θ c hθc s t hps hst htp q' hq' S ω cω hpres F M hM Fu Mu hMu
    ind hind hind1 H B hH b₀ c₀
  by_cases hnt : cfg = .none ∨ cfg = .term
  · exact hNT p hp n hn w LG X hsh hsz cfg hval hamb hnt θ c hθc s t hps hst htp q' hq' S ω cω hpres F M hM Fu Mu
      hMu ind hind hind1 H B hH b₀ c₀
  have hθ : θ = P.η ∧ c = 31 * P.d + 6 := by
    rcases hθc with h | ⟨-, -, h⟩
    · exact h
    · exact absurd h hnt
  obtain ⟨rfl, rfl⟩ := hθ
  by_cases htr : cfg = .trace ∧ X = .nil
  · obtain ⟨rfl, rfl⟩ := htr
    have h1 := hind1 (Or.inr (Or.inr rfl))
    have hfix : ∀ ts : Fin 2 → ℝ, (ProtCfg.trace.fix .nil s t (ts 0) : GBranch LG.garden.tree → Option ℝ) =
        ProtCfg.none.fix .nil s t (ts 0) := fun ts => trace_fix_nil hsh s t (ts 0)
    simp only [hfix]
    exact hNT p hp n hn w LG .nil hsh hsz .none trivial hamb (Or.inl rfl) P.η (31 * P.d + 6) (Or.inl ⟨rfl, rfl⟩)
      s t hps hst htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind (fun _ => h1) H B hH b₀ c₀
  · push_neg at hnt
    exact hU K hFC hc0 hcle rfl hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb
      ⟨hnt.1, hnt.2, htr⟩ s t hps hst htp q' hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀

end WaveTurbulence.Flower.ProtPin
