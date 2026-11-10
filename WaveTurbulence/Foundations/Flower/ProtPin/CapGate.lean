/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.CapMore
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildTrace
public import WaveTurbulence.Foundations.Flower.ProtPin.GateMain
public import WaveTurbulence.Foundations.Flower.ProtPin.GateF

/-! # D3 PROT-PIN: the cap couples (`w = 2`) as slices of `CfgU`/`CfgUF`

Per configuration: `capc_cfgU_root`, `capc_cfgU_trace` (nonempty chain), `capc_cfgU_rootTerm`, `capc_cfgU_pen`
(all three penTerm shapes), unconditional; `capc_cfgU_rest` collects them over `selCap` minus `termChild`.
`termChild` (P7) is conditional on the root-trace bound of TChild: `capc_cfgU_tchild_of_traceU` (from
`TcTraceU θ Ct`) and `capc_cfgU_tchild_of_cases` (from its two open cases `tcT1F`, `tcT2`).
Assembled: `capc_cfgU_cap_of` (selCap, from any `CfgUF` termChild cap slice), `capc_cfgU_cap_of_cases`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **(P1), caps.** -/
theorem capc_cfgU_root {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ _ cfg => w = 2 ∧ cfg = .root) := by
  obtain ⟨Cr, h0, hf⟩ := capc_root_final hθ0 hθ1
  refine ⟨Cr, h0, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig _hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel s t hps hst
    htp q' _hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl⟩ := hsel
  have hc : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ 31 * P.d + 6 := by linarith
  have hne : X.lonePath ≠ [] := hval
  exact hf K (pieceLoss_eta hη) le_rfl hc hCL hC11 hLOE hbig hp hn LG X hsh hsz hamb hne (hps.trans hst) htp s q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind (hind1 (Or.inr (Or.inl rfl))) b₀ c₀

/-- **(P8), caps with a nonempty chain.** -/
theorem capc_cfgU_trace {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ X cfg => w = 2 ∧ cfg = .trace ∧ X ≠ .nil) := by
  obtain ⟨Cr, h0, hf⟩ := capc_trace_final hθ0 hθ1
  refine ⟨Cr, h0, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig _hbig2 p hp n hn w LG X hsh hsz cfg _hval hamb hsel s t _hps
    _hst _htp q' _hq' S ω cω hpres F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl, hX⟩ := hsel
  have hc : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ 31 * P.d + 6 := by linarith
  have hne : X.lonePath ≠ [] := by
    cases X with
    | nil => exact absurd rfl hX
    | pair m Qr Qg inner rest => simp [RegChain.lonePath]
  exact hf K (pieceLoss_eta hη) le_rfl hc hCL hC11 hLOE hbig hp hn LG X hsh hsz hamb hne s t q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind (hind1 (Or.inr (Or.inr rfl))) b₀ c₀

/-- **(P2)/(P3), caps.** -/
theorem capc_cfgU_rootTerm {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ _ cfg => w = 2 ∧ cfg = .rootTerm) := by
  obtain ⟨Cr, h0, hf⟩ := capc_rootTerm_final hθ0 hθ1
  refine ⟨Cr, h0, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel s t hps hst
    htp q' _hq' S ω cω hpres F M hM Fu Mu hMu ind hind _hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl⟩ := hsel
  exact hf K (pieceLoss_eta hη) le_rfl hCL hC11 hLOE hbig hbig2 hp hn LG X hsh hsz hamb hval hps hst htp q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀

/-- **(P4)/(P5), caps**: empty prefix and interior (P4), nonempty interior (P5), nonempty prefix and empty
interior. -/
theorem capc_cfgU_pen {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr (fun w _ _ cfg => w = 2 ∧ cfg = .penTerm) := by
  obtain ⟨Cr1, h1, hf1⟩ := capc_pen_root_final hθ0
  obtain ⟨Cr2, h2, hf2⟩ := capc_pen5_final hθ0 hθ1
  obtain ⟨Cr3, h3, hf3⟩ := capc_pen_pre_final hθ0 hθ1
  refine ⟨Cr1 + Cr2 + Cr3, by linarith, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hη CL hCL hC11 hLOE hbig hbig2 p hp n hn w LG X hsh hsz cfg hval hamb hsel s t hps hst
    htp q' _hq' S ω cω hpres F M hM Fu Mu hMu ind hind _hind1 H B hH b₀ c₀
  obtain ⟨rfl, rfl⟩ := hsel
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hθc := pieceLoss_eta hη
  have hlen : 2 ≤ X.lonePath.length := hval
  have hXne : X ≠ .nil := by rintro rfl; simp [RegChain.lonePath] at hlen
  obtain ⟨Xp, m, Qr, Qg, inner, rfl⟩ := exists_last_pair X hXne
  by_cases hin : inner.lonePath ≠ []
  · exact hf2 K hθc le_rfl hCL hLOE (big2_mono hCL (by linarith) hL0 hbig2) hp hn LG hin hsh hsz hamb hps
      (hst.trans htp) t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
  · have hinn : inner = .nil := eq_nil_of_lonePath (not_not.mp hin)
    subst hinn
    by_cases hXp : Xp = .nil
    · subst hXp
      have hc : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ 31 * P.d + 6 := by linarith
      exact hf1 K hθc le_rfl hc hCL hC11 hLOE (big_mono hCL (by linarith) K.hδ hL0 hbig) hp hn LG hsh hsz hamb
        hps hst htp q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
    · exact hf3 K hθc le_rfl hCL hC11 hLOE (big2_mono hCL (by linarith) hL0 hbig2) hp hn LG hXp hsh hsz hamb
        hps (hst.trans htp) t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀

/-- The cap selector without `termChild`. -/
def capc_selRest : ∀ (w : ℕ), LayeredGarden w → RegChain → ProtCfg → Prop :=
  fun w LG X cfg => selCap w LG X cfg ∧ ∀ i, cfg ≠ .termChild i

theorem capc_selRest_cover (w : ℕ) (LG : LayeredGarden w) (X : RegChain) (cfg : ProtCfg)
    (hs : capc_selRest w LG X cfg) :
    (((w = 2 ∧ cfg = .root) ∨ (w = 2 ∧ cfg = .trace ∧ X ≠ .nil)) ∨ (w = 2 ∧ cfg = .rootTerm)) ∨
      (w = 2 ∧ cfg = .penTerm) := by
  obtain ⟨⟨hw, hn, ht, htr⟩, htc⟩ := hs
  cases cfg with
  | none => exact absurd rfl hn
  | term => exact absurd rfl ht
  | root => exact Or.inl (Or.inl (Or.inl ⟨hw, rfl⟩))
  | trace => exact Or.inl (Or.inl (Or.inr ⟨hw, rfl, fun h => htr ⟨rfl, h⟩⟩))
  | rootTerm => exact Or.inl (Or.inr ⟨hw, rfl⟩)
  | penTerm => exact Or.inr ⟨hw, rfl⟩
  | termChild i => exact absurd rfl (htc i)

theorem capc_selCap_cover (w : ℕ) (LG : LayeredGarden w) (X : RegChain) (cfg : ProtCfg) (hs : selCap w LG X cfg) :
    capc_selRest w LG X cfg ∨ (w = 2 ∧ ∃ i, cfg = .termChild i) := by
  by_cases htc : ∃ i, cfg = .termChild i
  · exact Or.inr ⟨hs.1, htc⟩
  · push_neg at htc
    exact Or.inl ⟨hs, htc⟩

/-- **Every cap configuration other than `termChild`** (and `none`/`term`/`trace` on an empty chain). -/
theorem capc_cfgU_rest {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgU θ Cr capc_selRest := by
  obtain ⟨Cr1, h1, hf1⟩ := capc_cfgU_root hθ0 hθ1
  obtain ⟨Cr2, h2, hf2⟩ := capc_cfgU_trace hθ0 hθ1
  obtain ⟨Cr3, h3, hf3⟩ := capc_cfgU_rootTerm hθ0 hθ1
  obtain ⟨Cr4, h4, hf4⟩ := capc_cfgU_pen hθ0 hθ1
  set Cr := Cr1 + Cr2 + Cr3 + Cr4 with hCr
  have hA : CfgU θ Cr (fun w _ _ cfg => w = 2 ∧ cfg = .root) := CfgU.mono hf1 (by linarith)
  have hB : CfgU θ Cr (fun w _ X cfg => w = 2 ∧ cfg = .trace ∧ X ≠ .nil) := CfgU.mono hf2 (by linarith)
  have hC : CfgU θ Cr (fun w _ _ cfg => w = 2 ∧ cfg = .rootTerm) := CfgU.mono hf3 (by linarith)
  have hD : CfgU θ Cr (fun w _ _ cfg => w = 2 ∧ cfg = .penTerm) := CfgU.mono hf4 (by linarith)
  have hU : CfgU θ Cr capc_selRest := CfgU.weaken (CfgU.or (CfgU.or (CfgU.or hA hB) hC) hD)
    fun _ w LG X cfg _ _ hs => capc_selRest_cover w LG X cfg hs
  exact ⟨Cr, by positivity, hU⟩

/-- **The cap slice `selCap` of the gate**, from any `CfgUF` cap slice for `termChild`. -/
theorem capc_cfgU_cap_of {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4)
    (hTC : ∃ Ct : ℝ, 0 ≤ Ct ∧ CfgUF θ Ct (fun w _ _ cfg => w = 2 ∧ ∃ i, cfg = .termChild i)) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr selCap := by
  obtain ⟨Cr1, h1, hf1⟩ := capc_cfgU_rest hθ0 hθ1
  obtain ⟨Cr2, h2, hf2⟩ := hTC
  have hA : CfgUF θ (Cr1 + Cr2) capc_selRest := CfgU.toF (CfgU.mono hf1 (by linarith))
  have hB : CfgUF θ (Cr1 + Cr2) (fun w _ _ cfg => w = 2 ∧ ∃ i, cfg = .termChild i) := CfgUF.mono hf2 (by linarith)
  have hU : CfgUF θ (Cr1 + Cr2) selCap := CfgUF.weaken (CfgUF.or hA hB)
    fun _ w LG X cfg _ _ hs => capc_selCap_cover w LG X cfg hs
  exact ⟨Cr1 + Cr2, by linarith, hU⟩

end WaveTurbulence.Flower.ProtPin
